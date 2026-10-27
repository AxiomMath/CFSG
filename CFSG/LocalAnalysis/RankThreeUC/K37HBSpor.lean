module

public import CFSG.LocalAnalysis.RankThreeUC.K37HBQuot
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.SporRec

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15.K37H

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC.S15.K37 CFSG.LocalAnalysis.GLTheoremB
  CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.HardMathSupport.Dickson.I271

theorem k37b_rest_of_sporStrong {name : TauCeti.SporadicName} (hS : SporStrong name 3)
    {X : Type} [Group X] [Finite X] {K E S : Subgroup X} (h : K37Setting X K E S)
    (h3 : 3 ∣ Nat.card K)
    (hK : Nonempty (↥K ⧸ Subgroup.center ↥K ≃* (TauCeti.CFSGIndex.sporadic name).Group)) :
    S ≤ Subgroup.centralizer (K : Set X) := by
  obtain ⟨Y, _, _, K', B', ⟨φ⟩, -, hcore, hcomp, hB, hBN, h9, hback⟩ := k37b_quot h h3
  obtain ⟨e⟩ := hK
  have eZ : (↥K ⧸ Subgroup.center ↥K) ≃* (↥K' ⧸ Subgroup.center ↥K') :=
    QuotientGroup.congr _ _ φ (Subgroup.map_center_eq φ)
  exact hback (hS Y K' B' ⟨Nat.prime_three, by norm_num, hcore, hcomp, hB, hBN⟩
    ⟨hBN, by simpa using h9⟩ ⟨eZ.symm.trans e⟩)

end CFSG.LocalAnalysis.RankThreeUC.S15.K37H

end
