module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.ThetaSpor.HeThreeData
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.ThetaSpor.PrimCertDef
public import CFSG.Sporadic.HeldB.InnerCheckInputs
public import CFSG.Sporadic.HeldB.HeBlocks
public import Certificates.Data.CFSGNative.HeldB.Tests
public meta import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.ThetaSpor.HeThreeData
public meta import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.ThetaSpor.PrimCertDef
public meta import CFSG.Sporadic.HeldB.InnerCheckInputs
public meta import CFSG.Sporadic.HeldB.HeBlocks
public meta import Certificates.Data.CFSGNative.HeldB.Tests
public meta import Certificates.Data.CFSGNative.PairSchreier.Core

public section

namespace CFSG.AGLEmbeddingD2.Wilson.ThetaSpor.He

open CFSG.Certificates CFSG.Sporadic.Schreier CFSG.Monster.B.Co2.Native CFSG.Certificates.Native
open CFSG.Sporadic.Schreier.Native CFSG.Sporadic.Th.Native CFSG.Sporadic.HeldB

@[expose] def heThreeArr (w : List Int) : Array Nat :=
  wordA 8330 heABArrs (heABArrs.map (invCand 8330)) w

@[expose] def heThreeBA : Array Nat := heThreeArr (heThreeWordsA.getD 0 [])

@[expose] def heThreeBB : Array Nat := heThreeArr (heThreeWordsB.getD 0 [])

@[expose] def heThreeCA (j : Nat) : Array Nat := heThreeArr (heThreeWordsA.getD j [])

@[expose] def heThreeCB (j : Nat) : Array Nat := heThreeArr (heThreeWordsB.getD j [])

@[expose] def heThreeXA : RawSchreierDatum 35 :=
  certificate (by decide) (heThreeSigmaA.map (permOrId 35)) heThreeChainWordsA #v[0, 1, 2, 3]
    (by decide)

@[expose] def heThreeXB : RawSchreierDatum 8 :=
  certificate (by decide) (heThreeSigmaB.map (permOrId 8)) heThreeChainWordsB #v[1, 0, 2]
    (by decide)

@[expose] def heThreeLettersA : Array (Array Nat) :=
  (heThreeSigmaA ++ heThreeSigmaA.map (invCand 35)).toArray

@[expose] def heThreeLettersB : Array (Array Nat) :=
  (heThreeSigmaB ++ heThreeSigmaB.map (invCand 8)).toArray

end CFSG.AGLEmbeddingD2.Wilson.ThetaSpor.He

end
