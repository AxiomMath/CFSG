module

public import Certificates.Certificate15115
public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec5RuPi7Equiv

public section

namespace CFSG.ComponentClassification.GMS78.RuNE

theorem card_pi7bRels :
    Finite (CFSG.CosetTable.PG 7 pi7bRels) ∧
      Nat.card (CFSG.CosetTable.PG 7 pi7bRels) ≤ 145926144000 :=
  Certificates.certificate15115.1

theorem pi7b_rels :
    ∀ r ∈ pi7bRels, CFSG.Sporadic.Bridge.wordProd RuPi7.pi7Img (r.map fun l => (l.1.val, l.2)) =
      1 :=
  Certificates.certificate15115.2.1

theorem card_relsM1 :
    Finite (CFSG.CosetTable.PG sub1.length relsM1) ∧
      Nat.card (CFSG.CosetTable.PG sub1.length relsM1) ≤ 245760 :=
  Certificates.certificate15115.2.2.1

theorem ne_basisEqs : ∀ p ∈ neBasisEqs,
    CFSG.Sporadic.Bridge.wordProd RuPi7.pi7Img (RuAsm.ruAsmNatWord p.1) =
      CFSG.Sporadic.Bridge.wordProd RuPi7.pi7Img (RuAsm.ruAsmNatWord p.2) :=
  Certificates.certificate15115.2.2.2.1

theorem ne_tNe : ∀ i < 64, i ≠ 0 →
    CFSG.Sporadic.Bridge.wordProd RuPi7.pi7Img (RuAsm.ruAsmNatWord (neTWord i)) ≠ 1 :=
  Certificates.certificate15115.2.2.2.2.1

theorem ne_orbitComm : ∀ t ∈ neOrbitWit, ∃ j : ℕ,
    CFSG.Sporadic.Bridge.wordProd RuPi7.pi7Img
        (RuAsm.ruAsmNatWord (neOrbitX t ++ RuAsm.ruE0Words.getD j [])) ≠
      CFSG.Sporadic.Bridge.wordProd RuPi7.pi7Img
        (RuAsm.ruAsmNatWord (RuAsm.ruE0Words.getD j [] ++ neOrbitX t)) :=
  Certificates.certificate15115.2.2.2.2.2.1

theorem ne_conjLin :
    ∀ k < 6, ∀ i < 64, (neConjTab.getD k []).getD i 0 = neConjLin k i :=
  Certificates.certificate15115.2.2.2.2.2.2.1

theorem ne_actCheck : neActCheck = true :=
  Certificates.certificate15115.2.2.2.2.2.2.2.1

theorem ne_w0Check : neW0Check = true :=
  Certificates.certificate15115.2.2.2.2.2.2.2.2

end CFSG.ComponentClassification.GMS78.RuNE
