module

public import CFSG.LocalAnalysis.RankThreeUC.K37HBGlue
public import CFSG.HardMathSupport.Dickson.Bal207.Holds
public import CFSG.LocalAnalysis.RankThreeUC.K37HDefs

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15.K37H

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC.S15.K37 CFSG.LocalAnalysis.GLTheoremB
  CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Solomon.Coordinator.ChevQ
  CFSG.HardMathSupport.Dickson.Bal207

private theorem k37b_rest_of_bal207 (hB207 : Bal207Corr) {X : Type} [Group X] [Finite X]
    {K E S : Subgroup X} (h : K37Setting X K E S) {P : TauCeti.LieTypeIndex → Prop}
    (hP : ∀ d, P d → Bal207Index 3 d ∧ ¬ IsG2EightIndex d) (hL : IsLieQuot ↥K P) :
    S ≤ Subgroup.centralizer (K : Set X) := by
  obtain ⟨B, hB, -, hBS⟩ := k37b_exists_scp h
  exact k37b_centralizes h hBS
    (Bal207Corr.of_index hB207 (k37b_isKGroup h) Nat.prime_three (by norm_num)
      (k37b_isComponentOf_top h) hB (k37b_le_normalizer h B) hP hL)

section Holds

set_option linter.unusedSectionVars false


theorem k37Rest₃_holds : K37Rest₃ := by
  intro X _ _ K E S h hO
  obtain ⟨d, ⟨q, hqp, hqe, hd⟩, hiso⟩ := hO
  refine k37b_rest_of_bal207 bal207Corr_holds h
    (P := fun i => ∃ q : TauCeti.PrimePower, IsTwoPow q 1 ∧ i = .twistedA 3 q) ?_
    ⟨d, ⟨q, ⟨hqp, hqe⟩, hd⟩, hiso⟩
  rintro _ ⟨q, hq, rfl⟩
  exact ⟨⟨rfl, Or.inl ⟨Or.inl hq, by norm_num⟩⟩, fun hg => hg⟩

theorem k37Rest₄_holds : K37Rest₄ := by
  intro X _ _ K E S h hO
  obtain ⟨d, ⟨q, hqp, hqe, hd⟩, hiso⟩ := hO
  refine k37b_rest_of_bal207 bal207Corr_holds h
    (P := fun i => ∃ q : TauCeti.PrimePower, IsTwoPow q 1 ∧ i = .B 4 q) ?_
    ⟨d, ⟨q, ⟨hqp, hqe⟩, hd⟩, hiso⟩
  rintro _ ⟨q, hq, rfl⟩
  exact ⟨⟨rfl, Or.inl ⟨hq, by norm_num⟩⟩, fun hg => hg⟩

end Holds

end CFSG.LocalAnalysis.RankThreeUC.S15.K37H

end
