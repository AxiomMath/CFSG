module

public import CFSG.HardMathSupport.Dickson.Sec6.I923Fam.TriD4Aux.G2Class
public import CFSG.HardMathSupport.Dickson.Sec6.Up34OddAux.Layer

public section

namespace CFSG.HardMathSupport.Dickson.Sec6.OutTri

open CFSG.Open CFSG.HardMathSupport.Solomon.Coordinator CFSG.Assembly.LowTwoRank
  CFSG.ComponentClassification.CatLeaf CFSG.HardMathSupport.Solomon.UniquenessMaximal
  CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Dickson.DefCharOuter.TrialityChar3
open CFSG.HardMathSupport.Dickson.Sec6 CFSG.HardMathSupport.Dickson.Sec6.I923

set_option linter.unusedSectionVars false

theorem lt_lieOrderNumerator_g2 {q : ℕ} (hq : 3 ≤ q) : 20160 < lieOrderNumerator .G2 0 q := by
  have h6 : 729 ≤ q ^ 6 :=
    calc 729 = 3 ^ 6 := by norm_num
      _ ≤ q ^ 6 := Nat.pow_le_pow_left hq 6
  have h2 : 9 ≤ q ^ 2 :=
    calc 9 = 3 ^ 2 := by norm_num
      _ ≤ q ^ 2 := Nat.pow_le_pow_left hq 2
  have h := Nat.mul_le_mul (Nat.mul_le_mul h6 (show 728 ≤ q ^ 6 - 1 by omega))
    (show 8 ≤ q ^ 2 - 1 by omega)
  simp only [lieOrderNumerator]
  omega

section G2


theorem noL34Layer_fieldActor_odd {ℓ f : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (hf : 1 ≤ f)
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = (ℓ ^ f) ^ 3) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) : NoL34Layer (fieldActor (t := TwistTag.D4) σ σ) := by
  haveI := TriD4Aux.finite_graphFixedRootGroup_D4 σ
  have hs := isSimpleGroup_fixSubgroup_fieldActor_D4 ℓ f hℓ hℓ2 K hK σ hσ
  have hnab := nonabelian_fixSubgroup_fieldActor_D4 ℓ f hℓ hℓ2 K hK σ hσ
  refine noL34Layer_of_fixed_equiv _ (MulEquiv.refl _) hs hnab fun hT => ?_
  have h1 := card_eq_of_isLThreeFour hT
  rw [TriD4Aux.card_fixSubgroup_fieldActor hℓ hf hK σ hσ] at h1
  have h2 := lt_lieOrderNumerator_g2 (TriD4Aux.three_le_pow_of_odd hℓ hℓ2 hf)
  omega

end G2

end CFSG.HardMathSupport.Dickson.Sec6.OutTri
