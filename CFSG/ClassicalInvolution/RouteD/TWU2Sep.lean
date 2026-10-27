module

public import CFSG.ClassicalInvolution.RouteD.TWU2Model
public import CFSG.ClassicalInvolution.RouteD.TWT9Spin

public section

namespace CFSG.ClassicalInvolution.RouteD.TWU

open CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.ClassicalGroups.Orthogonal QuadraticMap
  CFSG.ClassicalInvolution.RouteD.Gaps CFSG.LieType.Universal.Spin CFSG.ClassicalInvolution.WeakCT

open CFSG.ClassicalInvolution.Generic (Commutes)

set_option linter.unusedSectionVars false

section Generic

variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Q : QuadraticForm K V} {m : ℕ}

theorem not_mem_center_of_orth (hodd : Odd (Nat.card K)) (hdim : 8 < Module.finrank K V)
    (F₀ : HypFrame Q m) (x : spinGroup Q) {i₀ i₁ i₂ i₃ : Fin m} (h01 : i₀ ≠ i₁) (h23 : i₂ ≠ i₃)
    (h02 : i₀ ≠ i₂) (h03 : i₀ ≠ i₃) (h12 : i₁ ≠ i₂) (h13 : i₁ ≠ i₃)
    {𝓕 : Set (Subgroup (spinGroup Q))}
    (cq : CentralQuot (spinAction Q) 𝓕 (fundSet Q) (scalars K V)) (t : Bool)
    {R₀ RJ : Subgroup (spinGroup Q)} (h₀ : R₀ ∈ 𝓕)
    (hR₀ : R₀ = (F₀.longSL2 h01 true false).range.map (MulAut.conj x).toMonoidHom)
    (hRJ : RJ = (F₀.longSL2 h23 true t).range.map (MulAut.conj x).toMonoidHom) :
    ∀ r ∈ R₀, orderOf r = 2 → ∀ r' ∈ RJ, r⁻¹ * r' ∉ Subgroup.center (spinGroup Q) := by
  classical
  intro r hr hord r' hr' hcen
  have h2 : (2 : K) ≠ 0 := IsFundamental.two_ne_zero_of_odd hodd
  have hg := mem_orthogonalGroup_spinAction x
  have o01 : (imgPair F₀ i₀ hg).Orth (swapPair (imgPair F₀ i₁ hg)) :=
    orth_swapPair (imgPair_orth_of_ne F₀ hg h01)
  have o23 : (imgPair F₀ i₂ hg).Orth (swapPair (imgPair F₀ i₃ hg)) :=
    orth_swapPair (imgPair_orth_of_ne F₀ hg h23)
  have hperp := polar_span_mkFrame_eq_zero o01 o23 (imgPair_orth_of_ne F₀ hg h02)
    (imgPair_orth_of_ne F₀ hg h03) (imgPair_orth_of_ne F₀ hg h12) (imgPair_orth_of_ne F₀ hg h13)
  rw [← toFrame_map_true_false F₀ h01 hg o01, ← toFrame_map_true_false F₀ h23 hg o23] at hperp
  have hmem₀ : spinAction Q r ∈ ((F₀.toFrame h01 true false).map hg).La.range := by
    rw [← map_conj_longSL2_range F₀ h01 true false x, ← hR₀]
    exact ⟨r, hr, rfl⟩
  have hmem₂ : spinAction Q r' ∈ ((F₀.toFrame h23 true t).map hg).La.range := by
    rw [← map_conj_longSL2_range F₀ h23 true t x, ← hRJ]
    exact ⟨r', hr', rfl⟩
  have hi₀ : spinAction Q r = ((F₀.toFrame h01 true false).map hg).La (-1) :=
    IsFundamental.eq_of_orderOf_eq_two hodd (IsFundamental.of_frame _) hmem₀
      (cq.invOf h₀ ⟨hr, hord⟩).2
  have hsc : (((F₀.toFrame h01 true false).map hg).La (-1))⁻¹ * spinAction Q r' ∈
      scalars K V := by
    rw [← hi₀, ← map_inv, ← map_mul]
    exact cq.center_le _ hcen
  cases t
  · exact TWT9.no_scalar_between_frames h2 hdim _ _ hperp hmem₂ hsc
  · rw [toFrame_map_true_true] at hmem₂
    refine TWT9.no_scalar_between_frames h2 hdim _ ((F₀.toFrame h23 true false).map hg).swap ?_
      hmem₂ hsc
    rw [Frame.span_eq_swap_span]
    exact hperp

end Generic

section Statement

abbrev ChainTwin {M : Type} [Group M] (𝓕 : Set (Subgroup M)) (F : Type) [Field F]
    (R₀ R₁ RT : Subgroup M) : Prop :=
  ∃ RJ RJ' : Subgroup M, RJ ∈ 𝓕 ∧ RJ' ∈ 𝓕 ∧ Commutes RJ R₀ ∧ Commutes RJ RT ∧
    Commutes RJ' R₀ ∧ Commutes RJ' RT ∧ Commutes RJ RJ' ∧ RJ' ≠ RJ ∧
    (∃ W, LinearBlockStandardPair F W R₁ RJ) ∧
    (∀ r ∈ R₀, orderOf r = 2 → ∀ r' ∈ RJ, r⁻¹ * r' ∉ Subgroup.center M) ∧
    (∀ r ∈ R₀, orderOf r = 2 → ∀ r' ∈ RJ', r⁻¹ * r' ∉ Subgroup.center M) ∧
    ∃ a a' b b' r₁ ν : M, a ∈ R₀ ∧ a' ∈ RT ∧ b ∈ RJ ∧ b' ∈ RJ' ∧ r₁ ∈ R₁ ∧
      (∀ r ∈ R₀, orderOf r = 2 → r = a * a) ∧ (∀ r ∈ RT, orderOf r = 2 → r = a' * a') ∧
      (∀ r ∈ RJ, orderOf r = 2 → r = b * b) ∧ (∀ r ∈ RJ', orderOf r = 2 → r = b' * b') ∧
      (∀ r ∈ R₁, orderOf r = 2 → r = r₁) ∧ ν ∈ Subgroup.center M ∧
      a * a * (a' * a') = ν ∧ b * b * (b' * b') = ν ∧
      (a * a' * (b * b') = r₁ ∨ a * a' * (b * b') = ν * r₁)

end Statement

end CFSG.ClassicalInvolution.RouteD.TWU
