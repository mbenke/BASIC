{-# LANGUAGE FlexibleContexts #-}
module Language.BASIC.Translate(translateBASIC) where
import Control.Monad
import Data.List
import qualified Data.Map as M
import Data.Map((!), fromList)
import Data.Word
import Foreign.Ptr
import Type.Data.Num.Decimal.Literal(D3,D6)
import LLVM.Core
import LLVM.Util.File
import LLVM.ExecutionEngine(simpleFunction)
--import Debug.Trace

import Language.BASIC.Types

renumber :: [Expr a] -> [Expr a]
renumber cs =
    let m = M.fromList $ zip (map cmdLabel cs) [10, 20 ..]
        ren (Cmd l c es) = Cmd (m M.! l) c (map ren es)
	ren (Label l) = Label (m M.! l)
	ren e = e
    in  map ren cs

-- This assumes some sanity in loop nesting.
removeFor :: [Expr a] -> [Expr a]
removeFor [] = []
removeFor (Cmd l For [v, lo, hi, inc] : cs) =
    let cs' = removeFor cs
        (n, cs'') = removeNext cs'
	removeNext [] = error $ "No NEXT for line " ++ show (l, v)
	removeNext (Cmd ln Next [v'] : bs) | v == v' = (ln+2,
	    [Cmd ln Let [v, Binop v "+" inc],
             Cmd (ln+1) Goto [Label (l+1)],
             Cmd (ln+2) Rem []] ++ bs)
	removeNext (c:bs) = (ln, c:bs') where (ln, bs') = removeNext bs
	loopStart = [Cmd l Let [v, lo],
                     Cmd (l+1) If [Binop v ">" hi, Label n]]
    in  loopStart ++ cs''
removeFor (c:cs) = c : removeFor cs

translateBASIC :: [Expr ()] -> IO (IO ())
translateBASIC cmds = do
    let cmds' = removeFor $ renumber cmds
--    putStrLn $ unlines $ map show cmds'

    let mfunc = trans cmds'
    writeCodeGenModule "run.bc" mfunc

    -- Slow external optimizer.
    -- func <- optimizeFunctionCG mfunc

    -- Use this for unoptimized code
    func <- simpleFunction mfunc

    return func

-- Translate a (END terminated) list of lines to a function.
trans :: [Expr ()] -> CodeGenModule (Function (IO ()))
trans cmds = do
    atan     <- newNamedFunction ExternalLinkage "atan"     :: TFunction (Double -> IO Double)
    atof     <- newNamedFunction ExternalLinkage "atof"     :: TFunction (Ptr Word8 -> IO Double)
    cos      <- newNamedFunction ExternalLinkage "cos"      :: TFunction (Double -> IO Double)
    exp      <- newNamedFunction ExternalLinkage "exp"      :: TFunction (Double -> IO Double)
    fabs     <- newNamedFunction ExternalLinkage "fabs"     :: TFunction (Double -> IO Double)
    gets     <- newNamedFunction ExternalLinkage "gets"     :: TFunction (Ptr Word8 -> IO (Ptr Word8))
    log      <- newNamedFunction ExternalLinkage "log"      :: TFunction (Double -> IO Double)
    pow      <- newNamedFunction ExternalLinkage "pow"      :: TFunction (Double -> Double -> IO Double)
    printfv  <- newNamedFunction ExternalLinkage "printf"   :: TFunction (Ptr Word8 -> VarArgs Word32)
    rand     <- newNamedFunction ExternalLinkage "rand"     :: TFunction (IO Word32)
    sin      <- newNamedFunction ExternalLinkage "sin"      :: TFunction (Double -> IO Double)
    sqrt     <- newNamedFunction ExternalLinkage "sqrt"     :: TFunction (Double -> IO Double)
    -- sranddev <- newNamedFunction ExternalLinkage "sranddev" :: TFunction (IO ())
    tan      <- newNamedFunction ExternalLinkage "tan"      :: TFunction (Double -> IO Double)
    trunc    <- newNamedFunction ExternalLinkage "trunc"    :: TFunction (Double -> IO Double)
    let printfd :: Function (Ptr Word8 -> Double -> IO Word32)
        printfd = castVarArgs printfv
        printfs :: Function (Ptr Word8 -> Ptr Word8 -> IO Word32)
        printfs = castVarArgs printfv
        printfn :: Function (Ptr Word8 -> IO Word32)
        printfn = castVarArgs printfv

    fmtg <- createStringNul "%.15g"
    fmts <- createStringNul "%s"
    fmtn <- createStringNul "\n"

    let nextmap = fromList $ zip (map cmdLabel cmds) (map cmdLabel (tail cmds))
        strings = nub $ concatMap getCmdStrings cmds
	getCmdStrings (Cmd _ _ es) = concatMap getExprStrings es
	getCmdStrings _ = error "getCmdStrings"
	getExprStrings (Str s) = [s]
	getExprStrings (Binop e1 _ e2) = getExprStrings e1 ++ getExprStrings e2
	getExprStrings _ = []
    strmap <- liftM (fromList . zip strings) $ mapM createStringNul strings

    let mkGlobal x = do
            v <- createNamedGlobal False InternalLinkage (show x) zero
	    return (x, v)
    globmap <- liftM fromList $ mapM mkGlobal [A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z]

    gosubStack <- createNamedGlobal False InternalLinkage "gosubStack" zero
    let _ = gosubStack :: Global (Ptr Word32)

    -- Find GOSUB return points
    let returnmap = M.fromList $ zip [ nextmap ! l | Cmd l Gosub _ <- cmds ] (map constOf [0..])

    createFunction ExternalLinkage $ do
        let mkBlk c = do b <- newBasicBlock; return (cmdLabel c, b)
        blkmap <- liftM fromList $ mapM mkBlk cmds
	retlabel <- newBasicBlock
	let block = (blkmap !)
	    next = block . (nextmap !)
	    gen (Cmd l kw es) = do
                defineBasicBlock (block l)
		case (kw, es) of
		    (End, _) -> ret ()
		    (Goto, [Label d]) -> br (block d)
		    (Print, as) -> do mapM_ pr as; newline; br (next l)
		    (Let, [v, e]) -> do
                        d <- genExpr e
                        store d (globmap ! v)
		        br (next l)
		    (If, [b, Label d]) -> do
                        v <- genBool b
                        condBr v (block d) (next l)
                    (Input, [v]) -> do
                        buff <- arrayMalloc (100 :: Word32)
			call gets buff
			d <- call atof buff
			store d (globmap ! v)
			free buff
			br (next l)
		    (Rem, _) -> br (next l)
		    (Gosub, [Label d]) -> do
                        sp <- load gosubStack
			sp' <- getElementPtr sp (1::Word32, ())
			store sp' gosubStack
			store (value (returnmap ! (nextmap ! l))) sp
			br (block d)
		    (Return, _) -> br retlabel
		    x -> error $ "Unimplemented construct " ++ show x
            gen _ = error "gen"

            -- newline = withStringNul "\n" $ \fmtn -> do
            newline = do
                tmp <- getElementPtr (fmtn::Value (Ptr (Array D3 Word8))) (0::Word32, (0::Word32, ()))
                call printfn tmp

            -- pr (Str s) = withStringNul "%s" $ \fmts -> do
            pr (Str s) = do
	        tmp <- getElementPtr (fmts::Value (Ptr (Array D3 Word8))) (0::Word32, (0::Word32, ()))
	        tmpa <- getElementPtr ((strmap ! s)::Value(Ptr (Array D6 Word8))) (0::Word32, (0::Word32, ()))
                call printfs tmp tmpa
            -- pr e = withStringNul "%.15g" $ \fmtg -> do
            pr e = do
                d <- genExpr e
                -- tmp <- getElementPtr fmtg (0::Word32, (0::Word32, ()))
                tmp <- getElementPtr (fmtg::Value(Ptr (Array D6 Word8))) (0::Word32, (0::Word32, ()))
                call printfd tmp d

--	    genExpr e | trace (show e) False = undefined
            genExpr (Dbl d) = return $ value $ constOf d
	    genExpr (Binop e1 "+" e2) = binop add e1 e2
	    genExpr (Binop e1 "-" e2) = binop sub e1 e2
	    genExpr (Binop e1 "*" e2) = binop mul e1 e2
	    genExpr (Binop e1 "/" e2) = binop fdiv e1 e2
	    genExpr (Binop e1 "^" e2) = binop (call pow) e1 e2
	    genExpr (SIN e) = unop (call sin) e
	    genExpr (COS e) = unop (call cos) e
	    genExpr (TAN e) = unop (call tan) e
	    genExpr (ATN e) = unop (call atan) e
	    genExpr (EXP e) = unop (call exp) e
	    genExpr (LOG e) = unop (call log) e
	    genExpr (SQR e) = unop (call sqrt) e
	    genExpr (ABS e) = unop (call fabs) e
	    genExpr (INT e) = unop (call trunc) e
            genExpr (RND _) = do
                r <- call rand
                d <- uitofp r
		fdiv (d :: Value Double) (constOf (0x7fffffff :: Double))
            genExpr (SGN e) = do
                d <- genExpr e
                n <- fcmp FPOLT d zero -- (0 :: Value Double)
                p <- fcmp FPOGT d zero -- (0 :: Value Double)
		nd <- uitofp n
		pd <- uitofp p
		sub (pd :: Value Double) (nd :: Value Double)
	    genExpr e | e > Var && e < None= load (globmap ! e)
	    genExpr e = error $ "genExpr: " ++ show e

            genBool (Binop e1 "<>" e2) = binop (fcmp FPONE) e1 e2
	    genBool (Binop e1 "==" e2) = binop (fcmp FPOEQ) e1 e2
	    genBool (Binop e1 "<"  e2) = binop (fcmp FPOLT) e1 e2
	    genBool (Binop e1 "<=" e2) = binop (fcmp FPOLE) e1 e2
	    genBool (Binop e1 ">"  e2) = binop (fcmp FPOGT) e1 e2
	    genBool (Binop e1 ">=" e2) = binop (fcmp FPOGE) e1 e2
	    genBool e = error $ "Unknown bool op " ++ show e

	    binop :: (Value Double -> Value Double -> CodeGenFunction r (Value c)) ->
	             Expr () -> Expr () -> CodeGenFunction r (Value c)
            binop op e1 e2 = do
                d1 <- genExpr e1
                d2 <- genExpr e2
                op d1 d2

            unop op e = do
                d <- genExpr e
                op d

        -- call sranddev -- Make sure we get new random numbers
	p <- arrayMalloc (1000 :: Word32)
	store p gosubStack
	br (block $ cmdLabel $ head cmds)  -- jump to first line

        mapM_ gen cmds -- generate all lines

	unreach <- createBasicBlock
	unreachable

	-- The code for RETURN
	defineBasicBlock retlabel
        sp' <- load gosubStack
	sp <- getElementPtr sp' ((-1)::Word32, ())
	store sp gosubStack
	r <- load sp
	switch r unreach [ (c, block l) | (l, c) <- M.toList returnmap ]
