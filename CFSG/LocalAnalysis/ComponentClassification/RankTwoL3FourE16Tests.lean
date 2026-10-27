module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoL3FourHypIIW

public section

namespace CFSG.ComponentClassification.RankTwoL3Four.HypII

open CFSG.ComponentClassification.RankTwoSporadic.Cert CFSG.RankThree.Native
open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Monster.B.Fischer CFSG.KC.Census
open CFSG.Certificates.Native

@[expose] def isInvA (a : Array ℕ) : Bool :=
  eqA 42 (compA 42 a a) (idA 42) && !(eqA 42 a (idA 42))

@[expose] def inSpan3 (u v w t : Array ℕ) : Bool :=
  [idA 42, u, v, w, compA 42 u v, compA 42 u w, compA 42 v w, compA 42 u (compA 42 v w)].any
    (eqA 42 t)

@[expose] def e16OKW (inS : Array ℕ → Bool) (I : List (Array ℕ)) : Bool :=
  I.all fun u => inS u || I.all fun v => !(commA 42 u v) || eqA 42 v u ||
    I.all fun w => !(commA 42 u w) || !(commA 42 v w) || eqA 42 w u || eqA 42 w v ||
      eqA 42 w (compA 42 u v) ||
      I.all fun t => !(commA 42 t u) || !(commA 42 t v) || !(commA 42 t w) || inSpan3 u v w t

end CFSG.ComponentClassification.RankTwoL3Four.HypII

namespace CFSG.ComponentClassification

structure L34E16Cert where
  prog : List (ℕ × ℕ)
  sG : Array ℕ
  cS : CFSG.KC.Census.ArrCertP

end CFSG.ComponentClassification

namespace CFSG.ComponentClassification.RankTwoL3Four.HypII

open CFSG.ComponentClassification.RankTwoSporadic.Cert CFSG.RankThree.Native
open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Monster.B.Fischer CFSG.KC.Census
open CFSG.Certificates.Native

@[expose] noncomputable def l34CheckWE16 (d : L34E16Cert) : Bool :=
  rawChainOK 42 (l34SW.extract 0 3) l34SW l34BaseW
      (CFSG.EvenSmallLie.OmegaEight.wordsOf 3 l34DW) 4 && slpOK 42 l34GensR d.prog &&
    enumOKK 42 (d.sG.map (unpackP 42 6)) l34PS (d.cS.toMain 42 6) &&
    (allLt (d.sG.map (unpackP 42 6)).size fun k =>
      inRegsL 42 (slpRegs 42 l34GensR d.prog) (d.sG.map (unpackP 42 6))[k]!) &&
    (d.cS.toMain 42 6).pts.size == 256 &&
    e16OKW l34InSW ((d.cS.toMain 42 6).pts.toList.filter isInvA)

end CFSG.ComponentClassification.RankTwoL3Four.HypII
