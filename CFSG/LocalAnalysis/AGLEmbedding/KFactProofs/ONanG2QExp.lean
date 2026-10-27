module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanG2QTor

public section

namespace CFSG.AGLEmbedding.KFactProofs.G2Q

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

set_option linter.unusedSectionVars false

variable {L : Type} [Field L]

theorem yq_not_mem_torusGroup {g : Lˣ} (hg : g ≠ 1) : (yq : ModGL .G2 L) ∉ torusGroup .G2 L := by
  intro hy
  obtain ⟨s0, t0, h0⟩ := exists_tz_of_mem_torusGroup hy
  have h1 : (yq : ModGL .G2 L) * tz g 1 * yq⁻¹ = tz g 1 := by
    rw [h0, tz_inv, tz_mul, tz_mul]
    congr 1
    · rw [mul_comm s0 g, mul_assoc, mul_inv_cancel, mul_one]
    · simp
  rw [yq_tz] at h1
  have := (tz_injective h1).2
  apply hg
  simpa using this

@[expose] def tz3 : Subgroup (ModGL .G2 L) where
  carrier := {g | ∃ s t : Lˣ, s ^ 3 = 1 ∧ t ^ 3 = 1 ∧ g = tz s t}
  mul_mem' := by
    rintro _ _ ⟨s, t, hs, ht, rfl⟩ ⟨s', t', hs', ht', rfl⟩
    exact ⟨s * s', t * t', by rw [mul_pow, hs, hs', one_mul], by rw [mul_pow, ht, ht', one_mul],
      tz_mul s t s' t'⟩
  one_mem' := ⟨1, 1, one_pow _, one_pow _, tz_one_one.symm⟩
  inv_mem' := by
    rintro _ ⟨s, t, hs, ht, rfl⟩
    exact ⟨s⁻¹, t⁻¹, by rw [inv_pow, hs, inv_one], by rw [inv_pow, ht, inv_one], tz_inv s t⟩

theorem ext3_tz3 {g : Lˣ} (hg : g ≠ 1) : Ext3 (tz3 : Subgroup (ModGL .G2 L)) yq where
  pow_three := yq_pow_three
  normal := by
    rintro _ ⟨s, t, hs, ht, rfl⟩
    refine ⟨s * (t ^ 3)⁻¹, s * (t ^ 2)⁻¹, ?_, ?_, yq_tz s t⟩
    · rw [mul_pow, inv_pow, ← pow_mul, mul_comm 3 3, pow_mul, ht, hs]; simp
    · have : (s * (t ^ 2)⁻¹) ^ 3 = s ^ 3 * (t ^ 3) ^ (-2 : ℤ) := by
        apply Additive.ofMul.injective
        simp only [ofMul_mul, ofMul_inv, ofMul_pow, ofMul_zpow]
        module
      rw [this, hs, ht]; simp
  not_mem := by
    intro h
    obtain ⟨s, t, -, -, hst⟩ := h
    exact yq_not_mem_torusGroup hg (hst ▸ tz_mem_torusGroup s t)


theorem pow_three_tz_mul_yq (s t : Lˣ) : (tz s t * yq : ModGL .G2 L) ^ 3 = 1 := by
  have e1 : (tz s t * yq : ModGL .G2 L) ^ 3 = tz s t * (yq * tz s t * yq⁻¹) *
      (yq * (yq * tz s t * yq⁻¹) * yq⁻¹) * yq ^ 3 := by
    simp only [pow_succ, pow_zero, one_mul]
    group
  rw [e1, yq_pow_three, yq_tz, yq_tz, tz_mul, tz_mul, mul_one, ← tz_one_one]
  congr 1
  · apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv, ofMul_pow, ofMul_one]
    module
  · apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv, ofMul_pow, ofMul_one]
    module

theorem pow_three_of_mem_extSub {g : Lˣ} (hg : g ≠ 1) {x : ModGL .G2 L}
    (hx : x ∈ extSub (ext3_tz3 hg)) : x ^ 3 = 1 := by
  obtain ⟨t, ⟨s, u, hs, hu, rfl⟩, k, hk, rfl⟩ := (mem_extSub_iff_lt (ext3_tz3 hg)).1 hx
  interval_cases k
  · rw [pow_zero, mul_one, tz_pow, hs, hu, tz_one_one]
  · rw [pow_one]
    exact pow_three_tz_mul_yq s u
  ·
    have hy2 : (yq ^ 2 : ModGL .G2 L)⁻¹ = yq := by
      refine inv_eq_of_mul_eq_one_right ?_
      rw [← pow_succ]
      exact yq_pow_three
    have hinv : (tz s u * yq ^ 2 : ModGL .G2 L)⁻¹ =
        tz (s⁻¹ * ((u⁻¹) ^ 3)⁻¹) (s⁻¹ * ((u⁻¹) ^ 2)⁻¹) * yq := by
      calc (tz s u * yq ^ 2 : ModGL .G2 L)⁻¹ = (yq ^ 2)⁻¹ * (tz s u)⁻¹ := mul_inv_rev _ _
        _ = yq * tz s⁻¹ u⁻¹ := by rw [hy2, tz_inv]
        _ = (yq * tz s⁻¹ u⁻¹ * yq⁻¹) * yq := by group
        _ = _ := by rw [yq_tz]
    have h1 := pow_three_tz_mul_yq (s⁻¹ * ((u⁻¹) ^ 3)⁻¹) (s⁻¹ * ((u⁻¹) ^ 2)⁻¹)
    rw [← hinv, inv_pow, inv_eq_one] at h1
    exact h1

end CFSG.AGLEmbedding.KFactProofs.G2Q
