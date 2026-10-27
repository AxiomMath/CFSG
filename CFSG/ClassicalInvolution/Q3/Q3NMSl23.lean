module

public import CFSG.ClassicalInvolution.Q3.Q3NMLie

public section

namespace CFSG.ClassicalInvolution.Q3.Q3NM

open CFSG.Open CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Q3
open scoped commutatorElement MatrixGroups

section Klein

variable {P : Type} [Group P] [Finite P]

omit [Finite P] in
theorem eq_one_of_odd_orderOf_of_sq {x : P} (hodd : Odd (orderOf x)) (hx : x * x = 1) :
    x = 1 := by
  have h2 : orderOf x ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [sq]; exact hx)
  have h1 : orderOf x = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp h2 with h | h
    · exact h
    · rw [h] at hodd
      exact absurd hodd (by decide)
  exact orderOf_eq_one_iff.mp h1

theorem fixedOddFree_of_klein (a b : P) (ha : a * a = 1) (hb : b * b = 1) (ha1 : a ≠ 1)
    (hb1 : b ≠ 1) (hab : a ≠ b)
    (hE : ∀ x : P, x * x = 1 → x = 1 ∨ x = a ∨ x = b ∨ x = a * b)
    (hEmul : ∀ x y : P, x * x = 1 → y * y = 1 → (x * y) * (x * y) = 1)
    (hC : ∀ w y : P, w * w = 1 → w ≠ 1 → y * w = w * y → y * y = 1) : FixedOddFree P := by
  intro σ hσ
  have hσσ : ∀ x : P, σ (σ x) = x := fun x => apply_apply_of_mul_eq_one hσ x
  have hσsq : ∀ x : P, x * x = 1 → σ x * σ x = 1 := fun x hx => by rw [← map_mul, hx, map_one]
  have habc : a * b = b * a := by
    have h1 : (a * b)⁻¹ = a * b := inv_eq_of_mul_eq_one_right (hEmul a b ha hb)
    rw [mul_inv_rev, inv_eq_of_mul_eq_one_right ha, inv_eq_of_mul_eq_one_right hb] at h1
    exact h1.symm
  have hab1 : a * b ≠ 1 := fun h => hab (by
    calc a = a * (b * b) := by rw [hb, mul_one]
      _ = (a * b) * b := by group
      _ = b := by rw [h, one_mul])
  obtain ⟨w, hw, hw1, hσw⟩ : ∃ w : P, w * w = 1 ∧ w ≠ 1 ∧ σ w = w := by
    have h1 : σ a ≠ 1 := fun h => ha1 (σ.injective (by rw [h, map_one]))
    rcases hE (σ a) (hσsq a ha) with h | h | h | h
    · exact absurd h h1
    · exact ⟨a, ha, ha1, h⟩
    · refine ⟨a * b, hEmul a b ha hb, hab1, ?_⟩
      have hσb : σ b = a := by rw [← h, hσσ]
      rw [map_mul, h, hσb, habc]
    · refine ⟨b, hb, hb1, ?_⟩
      have hσab : σ (a * b) = a := by rw [← h, hσσ]
      have h2 : σ a * σ b = a := by rw [← map_mul]; exact hσab
      rw [h] at h2
      have h3 : σ b = (a * b)⁻¹ * a := by
        calc σ b = (a * b)⁻¹ * ((a * b) * σ b) := by group
          _ = (a * b)⁻¹ * a := by rw [h2]
      rw [h3, mul_inv_rev, inv_eq_of_mul_eq_one_right ha, inv_eq_of_mul_eq_one_right hb,
        mul_assoc, ha, mul_one]
  rw [eq_bot_iff]
  intro n hn
  rw [Subgroup.mem_bot]
  have hnC : n ∈ fixedSubgroup σ := oddCoreIn_le _ hn
  have hwC : w ∈ fixedSubgroup σ := hσw
  have hcomm : ⁅n, w⁆ = 1 := by
    have hc : n * w * n⁻¹ * w⁻¹ ∈ oddCoreIn (fixedSubgroup σ) := by
      have h1 : w * n⁻¹ * w⁻¹ ∈ oddCoreIn (fixedSubgroup σ) :=
        conj_mem_oddCoreIn hwC ((oddCoreIn _).inv_mem hn)
      have : n * w * n⁻¹ * w⁻¹ = n * (w * n⁻¹ * w⁻¹) := by group
      rw [this]
      exact (oddCoreIn _).mul_mem hn h1
    have hodd : Odd (orderOf (n * w * n⁻¹ * w⁻¹)) :=
      Odd.of_dvd_nat (odd_card_oddCoreIn _) (Subgroup.orderOf_dvd_natCard _ hc)
    have hwinv : w⁻¹ = w := inv_eq_of_mul_eq_one_right hw
    have hsq1 : (n * w * n⁻¹) * (n * w * n⁻¹) = 1 := by
      calc (n * w * n⁻¹) * (n * w * n⁻¹) = n * (w * w) * n⁻¹ := by group
        _ = 1 := by rw [hw]; group
    have := hEmul (n * w * n⁻¹) w⁻¹ hsq1 (by rw [hwinv]; exact hw)
    have hsq : (n * w * n⁻¹ * w⁻¹) * (n * w * n⁻¹ * w⁻¹) = 1 := by
      simpa [mul_assoc] using this
    have := eq_one_of_odd_orderOf_of_sq hodd hsq
    simpa [commutatorElement_def] using this
  have hnw : n * w = w * n := commutatorElement_eq_one_iff_mul_comm.mp hcomm
  have hnsq : n * n = 1 := hC w n hw hw1 hnw
  exact eq_one_of_odd_orderOf_of_sq
    (Odd.of_dvd_nat (odd_card_oddCoreIn _) (Subgroup.orderOf_dvd_natCard _ hn)) hnsq

end Klein


section SL23

theorem sl23_klein_exists : ∃ a b : SL(2, ZMod 3), a * a = -1 ∧ b * b = -1 ∧
    a * b * (a * b) = -1 ∧ a ≠ 1 ∧ a ≠ -1 ∧ b ≠ 1 ∧ b ≠ -1 ∧ a⁻¹ * b ≠ 1 ∧ a⁻¹ * b ≠ -1 := by
  decide +kernel

theorem sl23_klein_all : ∀ a b : SL(2, ZMod 3), a * a = -1 → b * b = -1 →
    a * b * (a * b) = -1 → ∀ g : SL(2, ZMod 3), (g * g = 1 ∨ g * g = -1) →
      g = 1 ∨ g = -1 ∨ g = a ∨ g = -a ∨ g = b ∨ g = -b ∨ g = a * b ∨ g = -(a * b) := by
  decide +kernel

theorem sl23_klein : ∃ a b : SL(2, ZMod 3), a * a = -1 ∧ b * b = -1 ∧ a * b * (a * b) = -1 ∧
    a ≠ 1 ∧ a ≠ -1 ∧ b ≠ 1 ∧ b ≠ -1 ∧ a⁻¹ * b ≠ 1 ∧ a⁻¹ * b ≠ -1 ∧
    ∀ g : SL(2, ZMod 3), (g * g = 1 ∨ g * g = -1) →
      g = 1 ∨ g = -1 ∨ g = a ∨ g = -a ∨ g = b ∨ g = -b ∨ g = a * b ∨ g = -(a * b) := by
  obtain ⟨a, b, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := sl23_klein_exists
  exact ⟨a, b, h1, h2, h3, h4, h5, h6, h7, h8, h9, sl23_klein_all a b h1 h2 h3⟩

theorem sl23_center_iff : ∀ z : SL(2, ZMod 3),
    (∀ g : SL(2, ZMod 3), g * z = z * g) ↔ (z = 1 ∨ z = -1) := by
  decide +kernel

theorem sl23_neg_inv_mul : ∀ g : SL(2, ZMod 3), (-g)⁻¹ * g = -1 := by decide +kernel

theorem sl23_mul_closed : ∀ g h : SL(2, ZMod 3), (g * g = 1 ∨ g * g = -1) →
    (h * h = 1 ∨ h * h = -1) → (g * h * (g * h) = 1 ∨ g * h * (g * h) = -1) := by
  decide +kernel

theorem sl23_self_cent : ∀ g h : SL(2, ZMod 3), (g * g = 1 ∨ g * g = -1) → ¬ (g = 1 ∨ g = -1) →
    ((h * g)⁻¹ * (g * h) = 1 ∨ (h * g)⁻¹ * (g * h) = -1) → (h * h = 1 ∨ h * h = -1) := by
  decide +kernel

theorem mem_center_sl23_iff (z : SL(2, ZMod 3)) :
    z ∈ Subgroup.center SL(2, ZMod 3) ↔ z = 1 ∨ z = -1 := by
  rw [Subgroup.mem_center_iff]
  exact sl23_center_iff z

theorem mk_eq_one_iff_sl23 (g : SL(2, ZMod 3)) :
    (QuotientGroup.mk g : SL(2, ZMod 3) ⧸ Subgroup.center SL(2, ZMod 3)) = 1 ↔
      g = 1 ∨ g = -1 := by
  rw [QuotientGroup.eq_one_iff, mem_center_sl23_iff]

theorem mk_eq_mk_iff_sl23 (g h : SL(2, ZMod 3)) :
    (QuotientGroup.mk g : SL(2, ZMod 3) ⧸ Subgroup.center SL(2, ZMod 3)) = QuotientGroup.mk h ↔
      g⁻¹ * h = 1 ∨ g⁻¹ * h = -1 := by
  rw [QuotientGroup.eq, mem_center_sl23_iff]

theorem fixedOddFree_sl23 :
    FixedOddFree (SL(2, ZMod 3) ⧸ Subgroup.center SL(2, ZMod 3)) := by
  obtain ⟨a, b, ha, hb, hab, ha1, ha2, hb1, hb2, hab1, hab2, hE⟩ := sl23_klein
  have hmk : ∀ g : SL(2, ZMod 3),
      (QuotientGroup.mk g : SL(2, ZMod 3) ⧸ Subgroup.center SL(2, ZMod 3)) * QuotientGroup.mk g =
        1 ↔ (g * g = 1 ∨ g * g = -1) := by
    intro g
    rw [← QuotientGroup.mk_mul, mk_eq_one_iff_sl23]
  refine fixedOddFree_of_klein (QuotientGroup.mk a) (QuotientGroup.mk b) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rw [hmk]
    exact Or.inr ha
  · rw [hmk]
    exact Or.inr hb
  · rw [Ne, mk_eq_one_iff_sl23]
    rintro (h | h)
    · exact ha1 h
    · exact ha2 h
  · rw [Ne, mk_eq_one_iff_sl23]
    rintro (h | h)
    · exact hb1 h
    · exact hb2 h
  · rw [Ne, mk_eq_mk_iff_sl23]
    rintro (h | h)
    · exact hab1 h
    · exact hab2 h
  · intro x hx
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
    rw [hmk] at hx
    rcases hE g hx with h | h | h | h | h | h | h | h
    · left
      rw [h]
      exact QuotientGroup.mk_one _
    · left
      rw [mk_eq_one_iff_sl23]
      exact Or.inr h
    · right; left
      rw [h]
    · right; left
      rw [h, mk_eq_mk_iff_sl23]
      exact Or.inr (sl23_neg_inv_mul a)
    · right; right; left
      rw [h]
    · right; right; left
      rw [h, mk_eq_mk_iff_sl23]
      exact Or.inr (sl23_neg_inv_mul b)
    · right; right; right
      rw [h, QuotientGroup.mk_mul]
    · right; right; right
      rw [← QuotientGroup.mk_mul, mk_eq_mk_iff_sl23, h]
      exact Or.inr (sl23_neg_inv_mul (a * b))
  · intro x y hx hy
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective y
    rw [hmk] at hx hy
    rw [← QuotientGroup.mk_mul, hmk]
    exact sl23_mul_closed g h hx hy
  · intro w y hw hw1 hyw
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective w
    obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective y
    rw [hmk] at hw
    rw [hmk]
    rw [Ne, mk_eq_one_iff_sl23] at hw1
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, mk_eq_mk_iff_sl23] at hyw
    exact sl23_self_cent g h hw hw1 hyw

end SL23

end CFSG.ClassicalInvolution.Q3.Q3NM
