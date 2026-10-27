module

public import Certificates.Certificate101703
public import CFSG.Fischer.Classification.Recognition.PSU6

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H1017.PureA

open CFSG.Open CFSG.Sporadic.Fi23 CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BThreeFi23

theorem exists_sylow_centralizer_conjPt_pure :
    ∃ S : Subgroup J, S ≤ Subgroup.centralizer ({conjPt 770} : Set J) ∧ Nat.card S = 3 ^ 9 ∧
      ∀ D ≤ S, IsElemAbelian 3 D → Nat.card D = 3 ^ 4 →
        ∃ x ∈ D, x ≠ 1 ∧ (IsConj x (t3 0) ∨ IsConj x (t3 2)) :=
  Certificates.certificate101703

end CFSG.LocalAnalysis.GLTheoremA.H1017.PureA
