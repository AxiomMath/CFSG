module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4HDChain
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4HDData

public section

namespace CFSG.ComponentClassification.GrSLit.HeDiag

open CFSG Subgroup CFSG.Sporadic.HeldB CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr
open scoped Pointwise

variable {X : Type} [Group X] [Finite X]

theorem card_le_two_mul_card_inf_of_mul {F H : Subgroup X} {x : X} (hxF : x ∈ F)
    (hH : ∀ f ∈ F, f ∉ H → x⁻¹ * f ∈ H) : Nat.card F ≤ 2 * Nat.card ↥(F ⊓ H) := by
  classical
  let g : F → ↥(F ⊓ H) ⊕ ↥(F ⊓ H) := fun f =>
    if hf : (f : X) ∈ H then Sum.inl ⟨f, mem_inf.mpr ⟨f.2, hf⟩⟩
    else Sum.inr ⟨x⁻¹ * f, mem_inf.mpr ⟨mul_mem (inv_mem hxF) f.2, hH f f.2 hf⟩⟩
  have hg : Function.Injective g := by
    intro f₁ f₂ h12
    by_cases h1 : (f₁ : X) ∈ H <;> by_cases h2 : (f₂ : X) ∈ H <;>
      simp only [g, h1, h2, dite_true, dite_false, Sum.inl.injEq, Sum.inr.injEq,
        reduceCtorEq] at h12
    · exact Subtype.ext (congrArg (fun w : ↥(F ⊓ H) => (w : X)) h12)
    · exact Subtype.ext (mul_left_cancel (congrArg (fun w : ↥(F ⊓ H) => (w : X)) h12))
  have := Nat.card_le_card_of_injective g hg
  rw [Nat.card_sum] at this
  omega

namespace SwapData

variable {M K T : Subgroup X} {a : X} (h : SwapData M K T a)
include h

omit [Finite X] in
theorem card_left' : Nat.card ↥(T ⊓ normalizer (K : Set X) ⊓ K) = 1024 := by
  rw [inf_normalizer_inf]
  exact h.card_left

omit [Finite X] in
theorem card_right' :
    Nat.card ↥(T ⊓ normalizer (conjugate K a : Set X) ⊓ conjugate K a) = 1024 := by
  rw [inf_normalizer_inf]
  exact h.card_right

theorem sup_le_sup_coreActionKernel :
    T ⊓ K ⊔ T ⊓ conjugate K a ≤ K ⊔ coreActionKernel K ∧
      T ⊓ K ⊔ T ⊓ conjugate K a ≤ conjugate K a ⊔ coreActionKernel (conjugate K a) :=
  ⟨sup_le (inf_le_right.trans le_sup_left)
      (inf_le_right.trans (h.le_coreActionKernel.2.trans le_sup_right)),
    sup_le (inf_le_right.trans (h.le_coreActionKernel.1.trans le_sup_right))
      (inf_le_right.trans le_sup_left)⟩

variable (e₁ : K ⧸ pPrimeCore 2 ↥K ≃* Blueprint.NativeSporadic.He)
  (e₂ : (conjugate K a) ⧸ pPrimeCore 2 ↥(conjugate K a) ≃* Blueprint.NativeSporadic.He)

include e₁ e₂ in
theorem mem_sup_of_mem {x : X} (hxT : x ∈ T) (hxN : x ∈ normalizer (K : Set X))
    (hx1 : x ∈ K ⊔ coreActionKernel K)
    (hx2 : x ∈ conjugate K a ⊔ coreActionKernel (conjugate K a)) :
    x ∈ T ⊓ K ⊔ T ⊓ conjugate K a := by
  have hcoreK : ∀ J : Subgroup X, (T ⊓ normalizer (J : Set X) ⊓ coreActionKernel J) ≤
      normalizer ((T ⊓ normalizer (J : Set X) ⊓ J : Subgroup X) : Set X) :=
    fun J p hp => mem_normalizer_inf (le_normalizer (mem_inf.mp hp).1)
      (mem_coreActionKernel.mp (mem_inf.mp hp).2).1
  have hxset : x ∈ ((T ⊓ normalizer (K : Set X) ⊓ K : Subgroup X) : Set X) *
      ((T ⊓ normalizer (K : Set X) ⊓ coreActionKernel K : Subgroup X) : Set X) := by
    rw [← coe_mul_of_right_le_normalizer_left _ _ (hcoreK _)]
    exact inf_sup_coreActionKernel_le' e₁ inf_le_right (h.isPGroup.to_le inf_le_left) h.card_left'
      (mem_inf.mpr ⟨mem_inf.mpr ⟨hxT, hxN⟩, hx1⟩)
  obtain ⟨t, ht, p, hp, hxeq₀⟩ := hxset
  have hxeq : t * p = x := hxeq₀
  have hpT : p ∈ T := (mem_inf.mp (mem_inf.mp hp).1).1
  have hpN' : p ∈ normalizer (conjugate K a : Set X) :=
    h.mem_normalizer_right hpT (mem_inf.mp (mem_inf.mp hp).1).2
  have hp2 : p ∈ conjugate K a ⊔ coreActionKernel (conjugate K a) := by
    have hp' : p = t⁻¹ * x := by rw [← hxeq]; group
    rw [hp']
    exact mul_mem (mem_sup_right (inv_mem (h.le_coreActionKernel.1 (mem_inf.mp ht).2))) hx2
  have hpset : p ∈ ((T ⊓ normalizer (conjugate K a : Set X) ⊓ conjugate K a : Subgroup X) :
      Set X) * ((T ⊓ normalizer (conjugate K a : Set X) ⊓ coreActionKernel (conjugate K a) :
        Subgroup X) : Set X) := by
    rw [← coe_mul_of_right_le_normalizer_left _ _ (hcoreK _)]
    exact inf_sup_coreActionKernel_le' e₂ inf_le_right (h.isPGroup.to_le inf_le_left)
      h.card_right' (mem_inf.mpr ⟨mem_inf.mpr ⟨hpT, hpN'⟩, hp2⟩)
  obtain ⟨t', ht', p', hp', hpeq₀⟩ := hpset
  have hpeq : t' * p' = p := hpeq₀
  have hp'1 : p' = 1 := by
    have hmem : p' ∈ T ⊓ coreActionKernel K ⊓ coreActionKernel (conjugate K a) := by
      refine mem_inf.mpr ⟨mem_inf.mpr ⟨(mem_inf.mp (mem_inf.mp hp').1).1, ?_⟩,
        (mem_inf.mp hp').2⟩
      have hp'' : p' = t'⁻¹ * p := by rw [← hpeq]; group
      rw [hp'']
      exact mul_mem (inv_mem (h.le_coreActionKernel.2 (mem_inf.mp ht').2)) (mem_inf.mp hp).2
    rw [h.kernel_eq_bot, mem_bot] at hmem
    exact hmem
  rw [← hxeq, ← hpeq, hp'1, mul_one]
  exact mul_mem (mem_sup_left (mem_inf.mpr ⟨(mem_inf.mp (mem_inf.mp ht).1).1,
    (mem_inf.mp ht).2⟩)) (mem_sup_right (mem_inf.mpr ⟨(mem_inf.mp (mem_inf.mp ht').1).1,
    (mem_inf.mp ht').2⟩))

include e₁ e₂ in
theorem exists_connected_of_le (hOut : HeldOuterInvolutionRank) {ζ : X}
    (hζR : ζ ∈ T ⊓ K ⊔ T ⊓ conjugate K a) (hζ2 : orderOf ζ = 2) (hζc : ∀ s ∈ T, s * ζ = ζ * s)
    {F : Subgroup X} (hFU : F ≤ T ⊓ normalizer (K : Set X)) (hF : IsElemTwo F)
    (hF8 : Nat.card F = 8) :
    ∃ A' : Subgroup X, A' ≤ T ⊓ K ⊔ T ⊓ conjugate K a ∧ IsAbelianTwoOfRank 3 A' ∧
      AbelianConnectedIn T 3 F A' := by
  have hFT : F ≤ T := hFU.trans inf_le_left
  have hFr : IsAbelianTwoOfRank 3 F := hF.isAbelianTwoOfRank (by omega)
  have hRT : T ⊓ K ⊔ T ⊓ conjugate K a ≤ T := sup_le inf_le_left inf_le_left
  by_cases hFR : F ≤ T ⊓ K ⊔ T ⊓ conjugate K a
  · exact ⟨F, hFR, hFr, hFT, hFr, Relation.ReflTransGen.refl⟩
  obtain ⟨x, hxF, hxR⟩ := IsConcreteLE.not_le_iff_exists.mp hFR
  have hxT : x ∈ T := hFT hxF
  have hxN : x ∈ normalizer (K : Set X) := (hFU hxF).2
  have hζT : ζ ∈ T := hRT hζR
  by_cases hx1 : x ∈ K ⊔ coreActionKernel K
  · by_cases hx2 : x ∈ conjugate K a ⊔ coreActionKernel (conjugate K a)
    · exact absurd (h.mem_sup_of_mem e₁ e₂ hxT hxN hx1 hx2) hxR
    · have hFS' : F ≤ T ⊓ normalizer (conjugate K a : Set X) := fun f hf =>
        mem_inf.mpr ⟨hFT hf, h.mem_normalizer_right (hFT hf) (hFU hf).2⟩
      obtain ⟨A', hA'R, hA', hc⟩ := exists_chain_outer e₂ hOut h.isPGroup h.card_right' hζT hζ2
        hζc (h.sup_le_sup_coreActionKernel.2 hζR) hFS' hF hF8 hxF hx2
      exact ⟨A', hA'R.trans le_sup_right, hA', hc⟩
  · obtain ⟨A', hA'R, hA', hc⟩ := exists_chain_outer e₁ hOut h.isPGroup h.card_left' hζT hζ2 hζc
      (h.sup_le_sup_coreActionKernel.1 hζR) hFU hF hF8 hxF hx1
    exact ⟨A', hA'R.trans le_sup_left, hA', hc⟩

end SwapData

end CFSG.ComponentClassification.GrSLit.HeDiag
