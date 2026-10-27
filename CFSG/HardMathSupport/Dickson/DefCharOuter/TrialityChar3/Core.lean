module

public import CFSG.HardMathSupport.Dickson.DefCharOuter.TrialityChar3.CoreStatement
public import CFSG.HardMathSupport.Dickson.DefCharOuter.TrialityChar3.SylowConj
public import CFSG.HardMathSupport.Dickson.DefCharOuter.TrialityChar3.G2Stage
public import CFSG.HardMathSupport.Dickson.DefCharOuter.TrialityChar3.CoreG2

public section

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.HardMathSupport.Lang.Triality CFSG.HardMathSupport.Lang.E27Lie
open CFSG.HardMathSupport.Solomon.Coordinator
open scoped commutatorElement

namespace CFSG.HardMathSupport.Dickson.DefCharOuter.TrialityChar3


theorem trialityThreeCore_holds : TrialityThreeCore := by
  intro f hf K _ _ _ hK σ hσ β hβ3 hout
  obtain ⟨u, hu, hu3, hgood⟩ := exists_conj_unipotent_goodPlus hf hK σ hσ β hβ3 hout
  refine hgood ?_
  obtain ⟨w, s, r, r', hs, hr, hr', hw⟩ := exists_twistedConj_longForm hf hK σ hσ hu hu3
  refine defCharGoodPlus_conj (MulAut.conj w⁻¹) _ ?_
  rw [conj_mul_twisted hf hK σ hσ (fieldActor (t := TwistTag.D4) σ σ) u w, hw]
  by_cases hne : s = 0 ∧ r = 0 ∧ r' = 0
  · obtain ⟨rfl, rfl, rfl⟩ := hne
    rw [longElt_zero hf hK σ hσ, longElt_zero hf hK σ hσ, longElt_zero hf hK σ hσ]
    simp only [mul_one, map_one, one_mul]
    exact Or.inl ⟨isSimpleGroup_fixSubgroup_fieldActor_D4 3 f Nat.prime_three (by norm_num) K hK σ hσ,
      nonabelian_fixSubgroup_fieldActor_D4 3 f Nat.prime_three (by norm_num) K hK σ hσ⟩
  · obtain ⟨ε, c, hc, hc0, hε⟩ := exists_conj_to_top_of_longForm hf hK σ hσ hs hr hr' hne
    refine defCharGoodPlus_conj ε _ ?_
    rw [hε]
    exact Or.inr (glaPPrimeCoreOf_fixSubgroup_conj_mul_fieldActor hf hK σ hσ hc hc0)

end CFSG.HardMathSupport.Dickson.DefCharOuter.TrialityChar3
