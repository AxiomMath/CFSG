module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoL3FourHypIITests
public import CFSG.Certificates.Kernel.Census.ToMain
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeData

public section

namespace CFSG.ComponentClassification.RankTwoL3Four.HypII

open CFSG.ComponentClassification.RankTwoSporadic.Cert CFSG.RankThree.Native
open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates.Native CFSG.KC.Census

@[expose] def l34DW : List (List ℤ) :=
  [[2], [-1, 2, 1], [-1, 3, 1], [-1, -5, 2, 5, 1], [-3, -7, 5, 3, 2], [-7, -8, 7, 6, 5]]

@[expose] def l34SW : Array (Array ℕ) := CFSG.EvenSmallLie.OmegaEight.pushWords 42 l34GensS l34DW

@[expose] def l34BaseWL : List (Fin 42) := [0, 1, 5, 2]

@[expose] def l34BaseW : Array ℕ := (l34BaseWL.map Fin.val).toArray

@[expose] def l34InSW (t : Array ℕ) : Bool := siftA 42 (rawLevels 42 l34SW l34BaseW) l34BaseW 0 t

@[expose] noncomputable def l34CheckWII (prog : List (ℕ × ℕ)) (sG roots : Array ℕ)
    (nodes : Array NodeP) (cS : ArrCertP) (wcs : Array (Array ArrCertP)) : Bool :=
  rawChainOK 42 (l34SW.extract 0 3) l34SW l34BaseW
      (CFSG.EvenSmallLie.OmegaEight.wordsOf 3 l34DW) 4 && slpOK 42 l34GensR prog &&
    censusOKW 42 l34PS l34InSW l34InSW false true false (sG.map (unpackP 42 6)) roots
      (nodes.map (NodeP.toMain 42 6)) (cS.toMain 42 6)
      (wcs.map fun cs => cs.map (ArrCertP.toMain 42 6)) &&
    (allLt (sG.map (unpackP 42 6)).size fun k =>
      inRegsL 42 (slpRegs 42 l34GensR prog) (sG.map (unpackP 42 6))[k]!) &&
    (cS.toMain 42 6).pts.size == 256

end CFSG.ComponentClassification.RankTwoL3Four.HypII
