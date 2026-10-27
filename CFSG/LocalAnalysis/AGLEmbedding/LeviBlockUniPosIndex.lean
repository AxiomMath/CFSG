module

public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherOrthogonality

public section

namespace CFSG.AGLEmbedding.LeviBlock

open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open scoped Pointwise

variable {p f : ℕ} {K : Type} [Field K] {r ε : ℕ}

theorem hypFlag_one_mem_hypIsotropicLines (h : UnitaryFieldData p f K) (hε : ε ≤ 1)
    (hr : 1 ≤ r) : hypFlag h r ε 1 ∈ hypIsotropicLines h r ε := by
  rw [mem_hypIsotropicLines, hypFlag_eq_posFlag h hε (by omega), finrank_posFlag hr]
  exact ⟨rfl, fun a ha => posFlag_isotropic h hr a ha a ha⟩

theorem exists_smul_hypFlag_one_eq (h : UnitaryFieldData p f K) (hε : ε ≤ 1)
    {W : Submodule K (HypIndex r ε → K)} (hW : W ∈ hypIsotropicLines h r ε) :
    ∃ g : hypSU h r ε, g • hypFlag h r ε 1 = W := by
  have hW0 : W ≠ ⊥ := fun h0 => by
    have := hW.1
    rw [h0, finrank_bot] at this
    exact zero_ne_one this
  obtain ⟨-, -, g, hg⟩ := exists_smul_hypFlag_eq h hε hW0
    (isTotIso_of_mem_isoLines (B := hypForm h r ε) hW)
  rw [hW.1] at hg
  exact ⟨g, hg⟩

theorem index_eq_card_hypIsotropicLines (h : UnitaryFieldData p f K) (hε : ε ≤ 1) (hr : 1 ≤ r)
    {J : Subgroup (hypSU h r ε)} (g : hypSU h r ε)
    (hJ : ∀ y, y ∈ J ↔ y • (g • hypFlag h r ε 1) = g • hypFlag h r ε 1) :
    J.index = Nat.card (hypIsotropicLines h r ε) := by
  set W : hypIsotropicLines h r ε :=
    ⟨g • hypFlag h r ε 1, (hypIsotropicLines h r ε).smul_mem g
      (hypFlag_one_mem_hypIsotropicLines h hε hr)⟩ with hWd
  have hJW : J = MulAction.stabilizer (hypSU h r ε) W := by
    ext y
    rw [hJ, MulAction.mem_stabilizer_iff, Subtype.ext_iff, SubMulAction.val_smul]
  have horb : MulAction.orbit (hypSU h r ε) W = Set.univ := by
    refine Set.eq_univ_of_forall fun M => ?_
    obtain ⟨g', hg'⟩ := exists_smul_hypFlag_one_eq h hε M.2
    refine ⟨g' * g⁻¹, Subtype.ext ?_⟩
    change (g' * g⁻¹) • (g • hypFlag h r ε 1) = (M : Submodule K (HypIndex r ε → K))
    rw [mul_smul, inv_smul_smul, hg']
  rw [hJW, MulAction.index_stabilizer, horb, Set.ncard_univ]

theorem card_hypIsotropicLines_three_zero (h : UnitaryFieldData 2 1 K) :
    Nat.card (hypIsotropicLines h 3 0) = 693 := by
  have := card_hypLines h (r := 3) (ε := 0) (by norm_num)
  norm_num at this
  omega

end CFSG.AGLEmbedding.LeviBlock
