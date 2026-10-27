module

public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.G2SylQP
public import Mathlib.RingTheory.Coprime.Lemmas

public section

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec6.G2Syl

open Subgroup CFSG.GH74.GLS.Stage1.Thm3.Sec8.G2Syl

section Asm

variable {X : Type*} [Group X]

theorem mem_zpowers_pow_odd {c : X} {n k : ℕ} (hc : c ^ (2 ^ n) = 1) (hk : Odd k) :
    c ∈ zpowers (c ^ k) := by
  have hcop : IsCoprime (k : ℤ) ((2 ^ n : ℕ) : ℤ) :=
    Nat.isCoprime_iff_coprime.2 (Nat.Coprime.pow_right _ (Nat.coprime_two_right.2 hk))
  obtain ⟨u, v, huv⟩ := hcop
  refine ⟨u, ?_⟩
  have h1 : c = c ^ ((k : ℤ) * u + ((2 ^ n : ℕ) : ℤ) * v) := by
    rw [show (k : ℤ) * u + ((2 ^ n : ℕ) : ℤ) * v = 1 by rw [← huv]; ring, zpow_one]
  rw [zpow_add, zpow_mul, zpow_mul, zpow_natCast, zpow_natCast, hc, one_zpow, mul_one] at h1
  exact h1.symm

theorem conj_of_comm {a b : X} (h : a * b = b * a) : a * b * a⁻¹ = b := by
  rw [h, mul_inv_cancel_right]

theorem conj_inv_of_conj_inv {y c : X} (h : y * c * y⁻¹ = c⁻¹) : y * c⁻¹ * y⁻¹ = c := by
  calc y * c⁻¹ * y⁻¹ = (y * c * y⁻¹)⁻¹ := by group
    _ = c := by rw [h, inv_inv]

theorem ia_assemble {P Q : Subgroup X} {y z c₁ w₁ c₂ w₂ : X} {n k₁ k₂ : ℕ}
    (hn : 2 ≤ n) (hyy : y * y = 1) (hyR : y ∉ P ⊔ Q) (hz1 : z ≠ 1)
    (hP : P = closure {c₁, w₁}) (hQ : Q = closure {c₂, w₂})
    (hc₁ : c₁ ^ (2 ^ n) = 1) (hc₁z : c₁ ^ (2 ^ (n - 1)) = z) (hw₁ : w₁ * w₁ = z)
    (hwc₁ : w₁ * c₁ * w₁⁻¹ = c₁⁻¹) (hyc₁ : y * c₁ * y⁻¹ = c₁⁻¹)
    (hyw₁ : y * w₁ * y⁻¹ = c₁ ^ k₁ * w₁) (hk₁ : Odd k₁)
    (hc₂ : c₂ ^ (2 ^ n) = 1) (hc₂z : c₂ ^ (2 ^ (n - 1)) = z) (hw₂ : w₂ * w₂ = z)
    (hwc₂ : w₂ * c₂ * w₂⁻¹ = c₂⁻¹) (hyc₂ : y * c₂ * y⁻¹ = c₂⁻¹)
    (hyw₂ : y * w₂ * y⁻¹ = c₂ ^ k₂ * w₂) (hk₂ : Odd k₂)
    (hcomm : ∀ p ∈ P, ∀ q ∈ Q, p * q = q * p) (hint : P ⊓ Q ≤ zpowers z) :
    ∃ (A : Subgroup X) (a t y' : X), ShapeConds (P ⊔ Q ⊔ zpowers y) A a t y' n := by
  have hc₁P : c₁ ∈ P := hP ▸ subset_closure (by simp)
  have hw₁P : w₁ ∈ P := hP ▸ subset_closure (by simp)
  have hc₂Q : c₂ ∈ Q := hQ ▸ subset_closure (by simp)
  have hw₂Q : w₂ ∈ Q := hQ ▸ subset_closure (by simp)
  have hzz : z * z = 1 := by
    rw [← hc₁z, ← pow_add, show 2 ^ (n - 1) + 2 ^ (n - 1) = 2 ^ n by
      have : n = (n - 1) + 1 := by omega
      rw [this, Nat.add_sub_cancel, pow_succ]; ring]
    exact hc₁
  have hyinv : y⁻¹ = y := inv_eq_of_mul_eq_one_right hyy
  have hc₁w₂ : c₁ * w₂ = w₂ * c₁ := hcomm _ hc₁P _ hw₂Q
  have hw₁c₂ : w₁ * c₂ = c₂ * w₁ := hcomm _ hw₁P _ hc₂Q
  have hw₁w₂ : w₁ * w₂ = w₂ * w₁ := hcomm _ hw₁P _ hw₂Q
  have hc₁c₂ : c₁ * c₂ = c₂ * c₁ := hcomm _ hc₁P _ hc₂Q
  have hWc₁ : w₁ * w₂ * c₁ * (w₁ * w₂)⁻¹ = c₁⁻¹ := by
    calc w₁ * w₂ * c₁ * (w₁ * w₂)⁻¹ = w₁ * (w₂ * c₁ * w₂⁻¹) * w₁⁻¹ := by group
      _ = w₁ * c₁ * w₁⁻¹ := by rw [← hc₁w₂, mul_assoc c₁, mul_inv_cancel, mul_one]
      _ = c₁⁻¹ := hwc₁
  have hWc₂ : w₁ * w₂ * c₂ * (w₁ * w₂)⁻¹ = c₂⁻¹ := by
    have h1 : w₁ * c₂⁻¹ * w₁⁻¹ = c₂⁻¹ :=
      conj_of_comm (Commute.inv_right (show Commute w₁ c₂ from hw₁c₂))
    calc w₁ * w₂ * c₂ * (w₁ * w₂)⁻¹ = w₁ * (w₂ * c₂ * w₂⁻¹) * w₁⁻¹ := by group
      _ = w₁ * c₂⁻¹ * w₁⁻¹ := by rw [hwc₂]
      _ = c₂⁻¹ := h1
  have hWw₁ : w₁ * w₂ * w₁ * (w₁ * w₂)⁻¹ = w₁ := by
    have h1 : w₂ * w₁ * w₂⁻¹ = w₁ := conj_of_comm hw₁w₂.symm
    calc w₁ * w₂ * w₁ * (w₁ * w₂)⁻¹ = w₁ * (w₂ * w₁ * w₂⁻¹) * w₁⁻¹ := by group
      _ = w₁ := by rw [h1]; group
  have hWw₂ : w₁ * w₂ * w₂ * (w₁ * w₂)⁻¹ = w₂ := by
    have h1 : w₁ * w₂ * w₁⁻¹ = w₂ := conj_of_comm hw₁w₂
    calc w₁ * w₂ * w₂ * (w₁ * w₂)⁻¹ = w₁ * w₂ * w₁⁻¹ := by group
      _ = w₂ := h1
  have hyinv' : ∀ a : X, y * a * y⁻¹ = y * a * y := by intro a; rw [hyinv]
  have hQP : QPData n k₁ k₂ c₁ c₂ w₁ w₂ (y * (w₁ * w₂)) := by
    refine ⟨hn, hc₁, hc₂, ?_, ?_, ?_, ?_, hwc₁, hwc₂, hc₁c₂, hc₁w₂, hw₁c₂, hw₁w₂, ?_, ?_, hk₁, hk₂,
      ?_, ?_, ?_, ?_, ?_⟩
    · rw [hc₁z]; exact hz1
    · rw [hc₂z, hc₁z]
    · rw [hw₁, hc₁z]
    · rw [hw₂, hc₁z]
    · apply mul_inv_eq_iff_eq_mul.1
      calc y * (w₁ * w₂) * c₁ * (y * (w₁ * w₂))⁻¹ = y * (w₁ * w₂ * c₁ * (w₁ * w₂)⁻¹) * y⁻¹ := by
            group
        _ = c₁ := by rw [hWc₁]; exact conj_inv_of_conj_inv hyc₁
    · apply mul_inv_eq_iff_eq_mul.1
      calc y * (w₁ * w₂) * c₂ * (y * (w₁ * w₂))⁻¹ = y * (w₁ * w₂ * c₂ * (w₁ * w₂)⁻¹) * y⁻¹ := by
            group
        _ = c₂ := by rw [hWc₂]; exact conj_inv_of_conj_inv hyc₂
    · calc y * (w₁ * w₂) * w₁ * (y * (w₁ * w₂))⁻¹ = y * (w₁ * w₂ * w₁ * (w₁ * w₂)⁻¹) * y⁻¹ := by
            group
        _ = c₁ ^ k₁ * w₁ := by rw [hWw₁, hyw₁]
    · calc y * (w₁ * w₂) * w₂ * (y * (w₁ * w₂))⁻¹ = y * (w₁ * w₂ * w₂ * (w₁ * w₂)⁻¹) * y⁻¹ := by
            group
        _ = c₂ ^ k₂ * w₂ := by rw [hWw₂, hyw₂]
    · have hWW : (w₁ * w₂) * (w₁ * w₂) = 1 := by
        calc (w₁ * w₂) * (w₁ * w₂) = w₁ * (w₂ * w₁) * w₂ := by group
          _ = (w₁ * w₁) * (w₂ * w₂) := by rw [← hw₁w₂]; group
          _ = 1 := by rw [hw₁, hw₂, hzz]
      have h1 : y * (w₁ * w₂) * y⁻¹ = c₁ ^ k₁ * c₂ ^ k₂ * (w₁ * w₂) := by
        calc y * (w₁ * w₂) * y⁻¹ = (y * w₁ * y⁻¹) * (y * w₂ * y⁻¹) := by group
          _ = (c₁ ^ k₁ * w₁) * (c₂ ^ k₂ * w₂) := by rw [hyw₁, hyw₂]
          _ = c₁ ^ k₁ * (w₁ * c₂ ^ k₂) * w₂ := by group
          _ = c₁ ^ k₁ * (c₂ ^ k₂ * w₁) * w₂ := by
              rw [(Commute.pow_right (show Commute w₁ c₂ from hw₁c₂) k₂).eq]
          _ = c₁ ^ k₁ * c₂ ^ k₂ * (w₁ * w₂) := by group
      calc y * (w₁ * w₂) * (y * (w₁ * w₂))
          = (y * (w₁ * w₂) * y⁻¹) * (y * y) * (w₁ * w₂) := by group
        _ = (c₁ ^ k₁ * c₂ ^ k₂ * (w₁ * w₂)) * 1 * (w₁ * w₂) := by rw [h1, hyy]
        _ = c₁ ^ k₁ * c₂ ^ k₂ * ((w₁ * w₂) * (w₁ * w₂)) := by group
        _ = c₁ ^ k₁ * c₂ ^ k₂ := by rw [hWW, mul_one]
    · rintro x ⟨hx1, hx2⟩
      have hx : x ∈ P ⊓ Q := ⟨(zpowers_le.2 hc₁P) hx1, (zpowers_le.2 hc₂Q) hx2⟩
      rw [hc₁z]
      exact hint hx
    · intro hmem
      have hle : closure ({c₁, c₂} : Set X) ≤ P ⊔ Q := by
        rw [closure_le]
        rintro x (rfl | rfl)
        · exact mem_sup_left hc₁P
        · exact mem_sup_right hc₂Q
      have hW : w₁ * w₂ ∈ P ⊔ Q := mul_mem (mem_sup_left hw₁P) (mem_sup_right hw₂Q)
      apply hyR
      have := mul_mem (hle hmem) (inv_mem hW)
      rwa [mul_inv_cancel_right] at this
  refine ⟨qpA n w₁ (y * (w₁ * w₂)), y * (w₁ * w₂), qpT n w₁ (y * (w₁ * w₂)), qpY w₁ w₂, ?_⟩
  have hSC := shapeConds_of_qpData hQP
  set h : X := y * (w₁ * w₂) with hh
  have hyS : y ∈ P ⊔ Q ⊔ zpowers y := mem_sup_right (mem_zpowers y)
  have hW' : w₁ * w₂ ∈ P ⊔ Q ⊔ zpowers y :=
    mem_sup_left (mul_mem (mem_sup_left hw₁P) (mem_sup_right hw₂Q))
  have hhS : h ∈ P ⊔ Q ⊔ zpowers y := mul_mem hyS hW'
  have htS : qpT n w₁ h ∈ P ⊔ Q ⊔ zpowers y :=
    mul_mem (mem_sup_left (mem_sup_left hw₁P)) (pow_mem hhS _)
  have hS : qpS n w₁ w₂ h = P ⊔ Q ⊔ zpowers y := by
    apply le_antisymm
    · refine sup_le (sup_le (sup_le (zpowers_le.2 hhS) (zpowers_le.2 ?_)) (zpowers_le.2 htS))
        (zpowers_le.2 hW')
      exact mul_mem (mul_mem (inv_mem htS) hhS) htS
    · have hhA : h ∈ qpS n w₁ w₂ h :=
        mem_sup_left (mem_sup_left (mem_sup_left (mem_zpowers h)))
      have hatA : (qpT n w₁ h)⁻¹ * h * qpT n w₁ h ∈ qpS n w₁ w₂ h :=
        mem_sup_left (mem_sup_left (mem_sup_right (mem_zpowers _)))
      have htT : qpT n w₁ h ∈ qpS n w₁ w₂ h := mem_sup_left (mem_sup_right (mem_zpowers _))
      have hyT : qpY w₁ w₂ ∈ qpS n w₁ w₂ h := mem_sup_right (mem_zpowers _)
      have hck : c₁ ^ k₁ ∈ qpS n w₁ w₂ h := by
        have h1 : (c₁ ^ k₁)⁻¹ = ((qpT n w₁ h)⁻¹ * h * qpT n w₁ h) * h⁻¹ := by
          rw [hQP.at_eq]; group
        rw [← inv_mem_iff, h1]
        exact mul_mem hatA (inv_mem hhA)
      have hc₁T : c₁ ∈ qpS n w₁ w₂ h := (zpowers_le.2 hck) (mem_zpowers_pow_odd hc₁ hk₁)
      have hc₂T : c₂ ∈ qpS n w₁ w₂ h := by
        have h1 : c₂ ^ k₂ = (c₁ ^ k₁)⁻¹ * (h * h) := by rw [hQP.h_sq]; group
        have : c₂ ^ k₂ ∈ qpS n w₁ w₂ h := by
          rw [h1]; exact mul_mem (inv_mem hck) (mul_mem hhA hhA)
        exact (zpowers_le.2 this) (mem_zpowers_pow_odd hc₂ hk₂)
      have hw₁T : w₁ ∈ qpS n w₁ w₂ h := by
        have key : qpT n w₁ h * (h ^ (2 ^ (n - 1)))⁻¹ ∈ qpS n w₁ w₂ h :=
          mul_mem htT (inv_mem (pow_mem hhA _))
        have e : qpT n w₁ h * (h ^ (2 ^ (n - 1)))⁻¹ = w₁ := by unfold qpT; group
        rwa [e] at key
      have hw₂T : w₂ ∈ qpS n w₁ w₂ h := by
        have key : w₁⁻¹ * qpY w₁ w₂ ∈ qpS n w₁ w₂ h := mul_mem (inv_mem hw₁T) hyT
        have e : w₁⁻¹ * qpY w₁ w₂ = w₂ := by unfold qpY; group
        rwa [e] at key
      have hyT' : y ∈ qpS n w₁ w₂ h := by
        have key : h * (qpY w₁ w₂)⁻¹ ∈ qpS n w₁ w₂ h := mul_mem hhA (inv_mem hyT)
        have e : h * (qpY w₁ w₂)⁻¹ = y := by unfold qpY; rw [hh]; group
        rwa [e] at key
      refine sup_le (sup_le ?_ ?_) (zpowers_le.2 hyT')
      · rw [hP]; exact (closure_le _).2 (by rintro x (rfl | rfl) <;> assumption)
      · rw [hQ]; exact (closure_le _).2 (by rintro x (rfl | rfl) <;> assumption)
  rwa [hS] at hSC

end Asm

end CFSG.GH74.GLS.Stage1.Thm3.Sec6.G2Syl
