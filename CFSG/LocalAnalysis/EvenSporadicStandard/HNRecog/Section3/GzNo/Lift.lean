module

public import Mathlib.GroupTheory.OrderOfElement
import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.GzNo.Count

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

theorem gzNo_exists_lift {K : Type*} [Group K] [Finite K] (Q : Subgroup K) [Q.Normal]
    (hQ : Nat.card Q = 2 ^ 9) {ρ : K} (hρ : orderOf ρ = 5) (g : K)
    (hg : (g : K ⧸ Q) * (ρ : K ⧸ Q) = (ρ : K ⧸ Q) * (g : K ⧸ Q)) :
    ∃ s : K, (s : K ⧸ Q) = (g : K ⧸ Q) ∧ s * ρ = ρ * s := by
  let S : Set K := {k | (k : K ⧸ Q) = (g : K ⧸ Q)}
  have hS : ∀ k ∈ S, ρ * k * ρ⁻¹ ∈ S := by
    intro k hk
    change (k : K ⧸ Q) = (g : K ⧸ Q) at hk
    change ((ρ * k * ρ⁻¹ : K) : K ⧸ Q) = (g : K ⧸ Q)
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv, hk, ← hg,
      mul_inv_cancel_right]
  have hcardS : Nat.card S = 2 ^ 9 := by
    rw [← hQ]
    refine Nat.card_congr
      { toFun := fun k => ⟨g⁻¹ * k, QuotientGroup.eq.mp k.2.symm⟩
        invFun := fun q => ⟨g * q, by
          change ((g * q : K) : K ⧸ Q) = (g : K ⧸ Q)
          rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff (q : K)).mpr q.2, mul_one]⟩
        left_inv := fun k => Subtype.ext (mul_inv_cancel_left g k)
        right_inv := fun q => Subtype.ext (inv_mul_cancel_left g q) }
  have hmod := gzNo_card_modEq_five hρ S hS
  have hN : Nat.card {s : K // s ∈ S ∧ s * ρ = ρ * s} ≠ 0 := by
    intro h0
    rw [hcardS, h0] at hmod
    unfold Nat.ModEq at hmod
    exact absurd hmod (by decide)
  obtain ⟨⟨s, hs, hsρ⟩⟩ := (Nat.card_ne_zero.mp hN).1
  exact ⟨s, hs, hsρ⟩

theorem gzNo_commute_of_cycle {K : Type*} [Group K] (Q : Subgroup K) [Q.Normal] {ρ x s ζ : K}
    (hζ : ∀ q ∈ Q, q * ρ = ρ * q → q = 1 ∨ q = ζ) (hζc : ∀ g : K, g * ζ = ζ * g)
    (hζ2 : ζ ^ 2 = 1) (hx2 : x ^ 2 = 1) (hxρ : x * ρ = ρ * x) (hsρ : s * ρ = ρ * s)
    (hrel : ((s * (s * x * s⁻¹) * s⁻¹ : K) : K ⧸ Q) = ((x * (s * x * s⁻¹) : K) : K ⧸ Q)) :
    x * (s * x * s⁻¹) = (s * x * s⁻¹) * x := by
  have hinv : ∀ w : K, w ^ 2 = 1 → w⁻¹ = w := fun w hw =>
    inv_eq_of_mul_eq_one_right (by rw [← sq]; exact hw)
  have hc1 : Commute (s * x * s⁻¹) ρ :=
    (Commute.mul_left hsρ hxρ).mul_left (Commute.inv_left hsρ)
  have hc2 : Commute (s * (s * x * s⁻¹) * s⁻¹) ρ :=
    (Commute.mul_left hsρ hc1).mul_left (Commute.inv_left hsρ)
  have h1 : (s * x * s⁻¹) ^ 2 = 1 := by rw [conj_pow, hx2, mul_one, mul_inv_cancel]
  have h2 : (s * (s * x * s⁻¹) * s⁻¹) ^ 2 = 1 := by
    rw [conj_pow, h1, mul_one, mul_inv_cancel]
  have hk := QuotientGroup.eq.mp hrel
  set k := (s * (s * x * s⁻¹) * s⁻¹)⁻¹ * (x * (s * x * s⁻¹)) with hkdef
  have hkρ : k * ρ = ρ * k := (Commute.inv_left hc2).mul_left (Commute.mul_left hxρ hc1)
  have hkc : (∀ g : K, g * k = k * g) ∧ k ^ 2 = 1 := by
    rcases hζ k hk hkρ with h | h
    · rw [h]
      exact ⟨fun g => by rw [mul_one, one_mul], one_pow 2⟩
    · rw [h]
      exact ⟨hζc, hζ2⟩
  have h3 : x * (s * x * s⁻¹) = (s * (s * x * s⁻¹) * s⁻¹) * k := by
    rw [hkdef, mul_inv_cancel_left]
  have h4 : (x * (s * x * s⁻¹)) ^ 2 = 1 := by
    rw [h3, Commute.mul_pow (hkc.1 _), h2, hkc.2, one_mul]
  have h5 := hinv _ h4
  rw [mul_inv_rev, hinv x hx2, hinv _ h1] at h5
  exact h5.symm

end CFSG.EvenSporadicStandard.HNRecog.Section3
