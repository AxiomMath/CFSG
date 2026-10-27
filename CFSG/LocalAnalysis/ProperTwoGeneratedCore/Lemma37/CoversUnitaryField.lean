module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.UnitaryRootAutomorphismCoord

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37

open CFSG.BenderSuzuki.MatrixGroups CFSG.BenderSuzuki.External
open CFSG.ShultStronglyClosedTI.UnitaryRootAutomorphism

namespace CoverUnitary

variable {K : Type} [Field K] [Finite K] [CharP K 2] (J : HermitianForm 3 K) {f : ℕ}

omit [CharP K 2] in
theorem exists_conj_eq_ne (hf : 2 ≤ f) (hfixed : Nat.card {x : K // J.conj x = x} = 2 ^ f) :
    ∃ ν : K, J.conj ν = ν ∧ ν ≠ 0 ∧ ν ≠ 1 := by
  classical
  let _ : Fintype {x : K // J.conj x = x} := Fintype.ofFinite _
  let s : Finset {x : K // J.conj x = x} := {⟨0, map_zero _⟩, ⟨1, map_one _⟩}
  have hlt : s.card < (Finset.univ : Finset {x : K // J.conj x = x}).card := by
    rw [Finset.card_univ, ← Nat.card_eq_fintype_card, hfixed]
    calc s.card ≤ 2 := Finset.card_le_two
      _ < 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  obtain ⟨⟨ν, hν⟩, -, hνs⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
  simp only [s, Finset.mem_insert, Finset.mem_singleton, Subtype.mk.injEq, not_or] at hνs
  exact ⟨ν, hν, hνs.1, hνs.2⟩

theorem exists_conj_cube_ne (hf : 2 ≤ f) (hcard : Nat.card K = (2 ^ f) ^ 2)
    (hfixed : Nat.card {x : K // J.conj x = x} = 2 ^ f) : ∃ k : K, J.conj (k ^ 3) ≠ k ^ 3 := by
  obtain ⟨ξ, hξ⟩ := exists_conj_ne J (2 ^ f) hcard hfixed
  obtain ⟨ν, hνc, hν0, hν1⟩ := exists_conj_eq_ne J hf hfixed
  by_contra! h
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hδ : J.conj ξ - ξ ≠ 0 := sub_ne_zero.mpr hξ
  have E0 := h ξ
  have E1 := h (ξ + 1)
  have E2 := h (ξ + ν)
  simp only [map_pow, map_add, map_one, hνc] at E0 E1 E2
  have k1 : (J.conj ξ - ξ) * (J.conj ξ + ξ + 1) = 0 := by
    linear_combination E1 - E0 - (J.conj ξ ^ 2 + J.conj ξ - ξ ^ 2 - ξ) * h2
  have k2 : ν * ((J.conj ξ - ξ) * (J.conj ξ + ξ + ν)) = 0 := by
    linear_combination E2 - E0 - ν * (J.conj ξ ^ 2 - ξ ^ 2 + ν * J.conj ξ - ν * ξ) * h2
  have k1' := (mul_eq_zero.mp k1).resolve_left hδ
  have k2' := (mul_eq_zero.mp ((mul_eq_zero.mp k2).resolve_left hν0)).resolve_left hδ
  exact hν1 (by linear_combination k2' - k1')

theorem unitary_pairing_eq_zero (hf : 2 ≤ f) (hcard : Nat.card K = (2 ^ f) ^ 2)
    (hfixed : Nat.card {x : K // J.conj x = x} = 2 ^ f) (F : K → K → ZMod 2)
    (hl : ∀ a a' c, J.conj c = c → F (a + a') c = F a c + F a' c)
    (hr : ∀ a c c', J.conj c = c → J.conj c' = c' → F a (c + c') = F a c + F a c')
    (hinv : ∀ k : Kˣ, ∀ a c, J.conj c = c →
      F (a * (k : K) * (J.conj (k : K))⁻¹ ^ 2) (c * (J.conj (k : K))⁻¹ * (k : K)⁻¹) = F a c)
    (a c : K) (hc : J.conj c = c) : F a c = 0 := by
  have h2 : ∀ u : ZMod 2, u + u = 0 := by decide
  have hconjN : ∀ k : K, J.conj (k * J.conj k) = k * J.conj k := fun k => by
    rw [map_mul, J.conj_involutive, mul_comm]
  have hmove : ∀ k : K, k ≠ 0 → ∀ a c, J.conj c = c →
      F (a * (k * (J.conj k)⁻¹ ^ 2)) c = F a (c * (k * J.conj k)) := by
    intro k hk a c hc
    have hk' : J.conj k ≠ 0 := (map_ne_zero J.conj).mpr hk
    have h := hinv (Units.mk0 k hk) a (c * (k * J.conj k))
      (by rw [map_mul, hc, hconjN])
    rw [Units.val_mk0, show c * (k * J.conj k) * (J.conj k)⁻¹ * k⁻¹ = c by field_simp,
      mul_assoc] at h
    exact h
  obtain ⟨ν, hνc, hν0, hν1⟩ := exists_conj_eq_ne J hf hfixed
  obtain ⟨k₁, hk₁, hN₁⟩ := huppert_II_10_4_norm_surjective J (2 ^ f) hcard hfixed ν hνc hν0
  have hν1c : J.conj (ν + 1) = ν + 1 := by rw [map_add, hνc, map_one]
  have hν1' : ν + 1 ≠ 0 := fun h => hν1 (CharTwo.add_eq_zero.mp h)
  have hkill : ∀ k : K, k ≠ 0 → k * J.conj k = ν + 1 → ∀ a c, J.conj c = c →
      F (a * (k * (J.conj k)⁻¹ ^ 2 + k₁ * (J.conj k₁)⁻¹ ^ 2 + 1)) c = 0 := by
    intro k hk hNk a c hc
    have hcν : J.conj (c * ν) = c * ν := by rw [map_mul, hc, hνc]
    have e1 := hmove k hk a c hc
    have e2 := hmove k₁ hk₁ a c hc
    rw [hNk, mul_add, mul_one, hr _ _ _ hcν hc] at e1
    rw [hN₁] at e2
    rw [mul_add, mul_add, mul_one, hl _ _ _ hc, hl _ _ _ hc, e1, e2]
    calc F a (c * ν) + F a c + F a (c * ν) + F a c =
        (F a (c * ν) + F a (c * ν)) + (F a c + F a c) := by ring
      _ = 0 := by rw [h2, h2, add_zero]
  obtain ⟨k₂, hk₂, hN₂⟩ :=
    huppert_II_10_4_norm_surjective J (2 ^ f) hcard hfixed (ν + 1) hν1c hν1'
  obtain ⟨k₀, hk₀⟩ := exists_conj_cube_ne J hf hcard hfixed
  have hk₀0 : k₀ ≠ 0 := by
    rintro rfl
    exact hk₀ (by simp)
  have hk₀' : J.conj k₀ ≠ 0 := (map_ne_zero J.conj).mpr hk₀0
  have hk₂' : J.conj k₂ ≠ 0 := (map_ne_zero J.conj).mpr hk₂
  set k₃ := k₂ * k₀ * (J.conj k₀)⁻¹
  have hk₃ : k₃ ≠ 0 := mul_ne_zero (mul_ne_zero hk₂ hk₀0) (inv_ne_zero hk₀')
  have hconj₃ : J.conj k₃ = J.conj k₂ * J.conj k₀ * k₀⁻¹ := by
    simp only [k₃, map_mul, map_inv₀]
    rw [J.conj_involutive k₀]
  have hN₃ : k₃ * J.conj k₃ = ν + 1 := by
    rw [hconj₃, ← hN₂]
    simp only [k₃]
    field_simp
  have hne : k₂ * (J.conj k₂)⁻¹ ^ 2 + k₁ * (J.conj k₁)⁻¹ ^ 2 + 1 ≠ 0 ∨
      k₃ * (J.conj k₃)⁻¹ ^ 2 + k₁ * (J.conj k₁)⁻¹ ^ 2 + 1 ≠ 0 := by
    by_contra! h
    obtain ⟨ht₂, ht₃⟩ := h
    apply hk₀
    have hs3 : k₃ * (J.conj k₃)⁻¹ ^ 2 = k₂ * (J.conj k₂)⁻¹ ^ 2 := by
      linear_combination ht₃ - ht₂
    have h' : k₃ * (J.conj k₃)⁻¹ ^ 2 * J.conj k₀ ^ 3 = k₂ * (J.conj k₂)⁻¹ ^ 2 * k₀ ^ 3 := by
      rw [hconj₃]
      simp only [k₃]
      field_simp
    rw [hs3] at h'
    have hs : k₂ * (J.conj k₂)⁻¹ ^ 2 * (k₀ ^ 3 - J.conj k₀ ^ 3) = 0 := by
      linear_combination -h'
    have hs0 : k₂ * (J.conj k₂)⁻¹ ^ 2 ≠ 0 := mul_ne_zero hk₂ (pow_ne_zero _ (inv_ne_zero hk₂'))
    rw [map_pow]
    exact (sub_eq_zero.mp ((mul_eq_zero.mp hs).resolve_left hs0)).symm
  rcases hne with ht | ht
  · have h := hkill k₂ hk₂ hN₂ (a * (k₂ * (J.conj k₂)⁻¹ ^ 2 + k₁ * (J.conj k₁)⁻¹ ^ 2 + 1)⁻¹) c hc
    rwa [inv_mul_cancel_right₀ ht] at h
  · have h := hkill k₃ hk₃ hN₃ (a * (k₃ * (J.conj k₃)⁻¹ ^ 2 + k₁ * (J.conj k₁)⁻¹ ^ 2 + 1)⁻¹) c hc
    rwa [inv_mul_cancel_right₀ ht] at h

end CoverUnitary

end CFSG.ProperTwoGeneratedCore.Lemma37
