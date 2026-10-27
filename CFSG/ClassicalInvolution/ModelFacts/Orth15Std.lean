module

public import CFSG.ClassicalInvolution.ModelFacts.Orth15Spin

public section

namespace CFSG.ClassicalInvolution.ModelFacts.Orth15

open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Models.OrthogonalPairs
  CFSG.LieType.Universal.Spin CFSG.ClassicalGroups.Orthogonal
open scoped MatrixGroups

variable {K : Type} [Field K] [Finite K]

theorem alphaOf_spinOdd_frame_eq_bot (hodd : Odd (Nat.card K)) (h5 : 5 ≤ Nat.card K) {n : ℕ}
    (hn : 3 ≤ n) (fr : Frame (quadOdd n K)) {A A' : SL(2, K)}
    (hA : (A : Matrix (Fin 2) (Fin 2) K) * A = -1)
    (hA' : (A' : Matrix (Fin 2) (Fin 2) K) * A' = -1)
    {s₁ s₂ : spinGroup (quadOdd n K)} (hs₁ : spinAction (quadOdd n K) s₁ = twinInv fr A A')
    (hs₂ : spinAction (quadOdd n K) s₂ = fr.La (-1)) {H : Type} [Group H] [Finite H]
    (ψ : spinGroup (quadOdd n K) →* H) (hψ : ψ.ker ≤ Subgroup.center (spinGroup (quadOdd n K))) :
    alphaOf (Subgroup.closure ({toInducedAutOn ψ.range ⟨ψ s₁, mem_normalizer_range ψ s₁⟩,
      toInducedAutOn ψ.range ⟨ψ s₂, mem_normalizer_range ψ s₂⟩} :
        Set ↥(inducedAutOn ψ.range))) = ⊥ := by
  have h2 := two_ne_zero_of_odd_card hodd
  have : Group.IsPerfect (spinGroup (quadOdd n K)) := isPerfect_spinGroup_quadOdd h2 hn
  refine alphaOf_spin_frame_eq_bot hodd h5 (nondegenerate_polarBilin_quadOdd n K h2)
    (range_spinAction_quadOdd h2 hn) fr hA hA' ?_ hs₁ hs₂ ψ hψ
  rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_sum, Fintype.card_fin,
    Fintype.card_unit]
  omega

theorem alphaOf_spinPlus_frame_eq_bot (hodd : Odd (Nat.card K)) (h5 : 5 ≤ Nat.card K) {n : ℕ}
    (hn : 4 ≤ n) (fr : Frame (quadPlus n K)) {A A' : SL(2, K)}
    (hA : (A : Matrix (Fin 2) (Fin 2) K) * A = -1)
    (hA' : (A' : Matrix (Fin 2) (Fin 2) K) * A' = -1)
    {s₁ s₂ : spinGroup (quadPlus n K)} (hs₁ : spinAction (quadPlus n K) s₁ = twinInv fr A A')
    (hs₂ : spinAction (quadPlus n K) s₂ = fr.La (-1)) {H : Type} [Group H] [Finite H]
    (ψ : spinGroup (quadPlus n K) →* H) (hψ : ψ.ker ≤ Subgroup.center (spinGroup (quadPlus n K))) :
    alphaOf (Subgroup.closure ({toInducedAutOn ψ.range ⟨ψ s₁, mem_normalizer_range ψ s₁⟩,
      toInducedAutOn ψ.range ⟨ψ s₂, mem_normalizer_range ψ s₂⟩} :
        Set ↥(inducedAutOn ψ.range))) = ⊥ := by
  have : Group.IsPerfect (spinGroup (quadPlus n K)) := isPerfect_spinGroup_quadPlus (by omega)
  refine alphaOf_spin_frame_eq_bot hodd h5 (nondegenerate_polarBilin_quadPlus n K)
    (range_spinAction_quadPlus (by omega)) fr hA hA' ?_ hs₁ hs₂ ψ hψ
  rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin]
  omega

theorem alphaOf_spinMinus_frame_eq_bot (hodd : Odd (Nat.card K)) (h5 : 5 ≤ Nat.card K) {n : ℕ}
    {b c : K} (hn : 4 ≤ n) (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (fr : Frame (quadMinus n K b c)) {A A' : SL(2, K)}
    (hA : (A : Matrix (Fin 2) (Fin 2) K) * A = -1)
    (hA' : (A' : Matrix (Fin 2) (Fin 2) K) * A' = -1)
    {s₁ s₂ : spinGroup (quadMinus n K b c)}
    (hs₁ : spinAction (quadMinus n K b c) s₁ = twinInv fr A A')
    (hs₂ : spinAction (quadMinus n K b c) s₂ = fr.La (-1)) {H : Type} [Group H] [Finite H]
    (ψ : spinGroup (quadMinus n K b c) →* H)
    (hψ : ψ.ker ≤ Subgroup.center (spinGroup (quadMinus n K b c))) :
    alphaOf (Subgroup.closure ({toInducedAutOn ψ.range ⟨ψ s₁, mem_normalizer_range ψ s₁⟩,
      toInducedAutOn ψ.range ⟨ψ s₂, mem_normalizer_range ψ s₂⟩} :
        Set ↥(inducedAutOn ψ.range))) = ⊥ := by
  have : Group.IsPerfect (spinGroup (quadMinus n K b c)) :=
    isPerfect_spinGroup_quadMinus hn hirr
  refine alphaOf_spin_frame_eq_bot hodd h5 (nondegenerate_polarBilin_quadMinus_of_finite n K hirr)
    (range_spinAction_quadMinus hn hirr) fr hA hA' ?_ hs₁ hs₂ ψ hψ
  rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_sum, Fintype.card_fin,
    Fintype.card_fin]
  omega

end CFSG.ClassicalInvolution.ModelFacts.Orth15
