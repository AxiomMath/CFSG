module

public import Mathlib.GroupTheory.SpecificGroups.Dihedral

public section

namespace CFSG.ComponentClassification.AutL2Facts

open Subgroup

theorem dihedral_odd_orderOf_iff {n : ℕ} (hn : Odd n) (g : DihedralGroup n) :
    Odd (orderOf g) ↔ ∃ i, g = DihedralGroup.r i := by
  have : NeZero n := ⟨by rintro rfl; exact Nat.not_odd_zero hn⟩
  cases g with
  | r i =>
    refine ⟨fun _ => ⟨i, rfl⟩, fun _ => ?_⟩
    rw [DihedralGroup.orderOf_r]
    exact Odd.of_dvd_nat hn (Nat.div_dvd_of_dvd (Nat.gcd_dvd_left _ _))
  | sr i =>
    rw [DihedralGroup.orderOf_sr]
    simp

theorem dihedral_rot_mul {n : ℕ} (g h : DihedralGroup n) :
    (∃ i, g * h = DihedralGroup.r i) ↔
      ((∃ i, g = DihedralGroup.r i) ↔ (∃ i, h = DihedralGroup.r i)) := by
  cases g <;> cases h <;>
    simp [DihedralGroup.r_mul_r, DihedralGroup.r_mul_sr, DihedralGroup.sr_mul_r,
      DihedralGroup.sr_mul_sr]

theorem odd_mul_of_dihedral {X : Type*} [Group X] [Finite X] (I : Subgroup X) [I.Normal]
    (hcomm : ∀ x y : X, x * y * x⁻¹ * y⁻¹ ∈ I) (α : X) {n : ℕ} (hn : Odd n)
    (hD : Nonempty (↥(I ⊓ Subgroup.centralizer ({α} : Set X)) ≃* DihedralGroup n))
    {x y : X} (hx : x ∈ Subgroup.centralizer ({α} : Set X))
    (hy : y ∈ Subgroup.centralizer ({α} : Set X))
    (hxo : Odd (orderOf x)) (hyo : Odd (orderOf y)) : Odd (orderOf (x * y)) := by
  obtain ⟨ρ⟩ := hD
  set D := I ⊓ Subgroup.centralizer ({α} : Set X) with hDdef
  have hrot : ∀ d (hd : d ∈ D), Odd (orderOf d) ↔ ∃ i, ρ ⟨d, hd⟩ = DihedralGroup.r i := by
    intro d hd
    rw [← dihedral_odd_orderOf_iff hn, MulEquiv.orderOf_eq, Subgroup.orderOf_mk]
  have hmulrot : ∀ a ∈ D, ∀ b ∈ D,
      (Odd (orderOf (a * b)) ↔ (Odd (orderOf a) ↔ Odd (orderOf b))) := by
    intro a ha b hb
    rw [hrot a ha, hrot b hb, hrot (a * b) (mul_mem ha hb)]
    have : ρ ⟨a * b, mul_mem ha hb⟩ = ρ ⟨a, ha⟩ * ρ ⟨b, hb⟩ := by rw [← map_mul]; rfl
    rw [this]
    exact dihedral_rot_mul _ _
  have hDconj : ∀ g ∈ Subgroup.centralizer ({α} : Set X), ∀ d ∈ D, g * d * g⁻¹ ∈ D := by
    intro g hg d hd
    have hd' := Subgroup.mem_inf.mp hd
    exact Subgroup.mem_inf.mpr
      ⟨‹I.Normal›.conj_mem d hd'.1 g, mul_mem (mul_mem hg hd'.2) (inv_mem hg)⟩
  have hordconj : ∀ g d : X, orderOf (g * d * g⁻¹) = orderOf d := fun g d => by
    have := MulEquiv.orderOf_eq (MulAut.conj g) d
    rwa [MulAut.conj_apply] at this
  set c := x * y * x⁻¹ * y⁻¹ with hc
  have hcD : c ∈ D := Subgroup.mem_inf.mpr
    ⟨hcomm x y, mul_mem (mul_mem (mul_mem hx hy) (inv_mem hx)) (inv_mem hy)⟩
  have hpow : ∀ j : ℕ, ∃ d ∈ D, (c * y) ^ j = d * y ^ j ∧
      (Odd (orderOf d) ↔ (Even j ∨ Odd (orderOf c))) := by
    intro j
    induction j with
    | zero => exact ⟨1, one_mem _, by simp, by simp⟩
    | succ j ih =>
      obtain ⟨d, hd, hdj, hdrot⟩ := ih
      have hcjD : y ^ j * c * (y ^ j)⁻¹ ∈ D := hDconj _ (pow_mem hy j) c hcD
      refine ⟨d * (y ^ j * c * (y ^ j)⁻¹), mul_mem hd hcjD, ?_, ?_⟩
      · rw [pow_succ, hdj, pow_succ]
        group
      · rw [hmulrot d hd _ hcjD, hdrot, hordconj, Nat.even_add_one]
        tauto
  obtain ⟨d, -, hdm, hdrot⟩ := hpow (orderOf y)
  have hcy : (c * y) ^ orderOf y = 1 := by
    have h1 : c * y = x * y * x⁻¹ := by rw [hc]; group
    rw [h1]
    have h2 : (x * y * x⁻¹) ^ orderOf y = x * y ^ orderOf y * x⁻¹ := by
      have := map_pow (MulAut.conj x) y (orderOf y)
      simp only [MulAut.conj_apply] at this
      exact this.symm
    rw [h2, pow_orderOf_eq_one, mul_one, mul_inv_cancel]
  rw [hcy, pow_orderOf_eq_one, mul_one] at hdm
  have hcodd : Odd (orderOf c) := by
    have h1 : Odd (orderOf d) := by rw [← hdm, orderOf_one]; exact odd_one
    rcases hdrot.mp h1 with h | h
    · exact absurd h (Nat.not_even_iff_odd.mpr hyo)
    · exact h
  set P : X → Prop := fun b => b ∈ D ∧ Odd (orderOf b) with hP
  have hPmul : ∀ a b, P a → P b → P (a * b) := fun a b ha hb =>
    ⟨mul_mem ha.1 hb.1, (hmulrot a ha.1 b hb.1).mpr (iff_of_true ha.2 hb.2)⟩
  have hPinv : ∀ a, P a → P a⁻¹ := fun a ha => ⟨inv_mem ha.1, by rw [orderOf_inv]; exact ha.2⟩
  have hPconj : ∀ g ∈ Subgroup.centralizer ({α} : Set X), ∀ a, P a → P (g * a * g⁻¹) :=
    fun g hg a ha => ⟨hDconj g hg a ha.1, by rw [hordconj]; exact ha.2⟩
  have hPc : P c := ⟨hcD, hcodd⟩
  have hyx : ∀ j : ℕ, ∃ b, P b ∧ y ^ j * x = b * x * y ^ j := by
    intro j
    induction j with
    | zero => exact ⟨1, ⟨one_mem _, by simp⟩, by simp⟩
    | succ j ih =>
      obtain ⟨b, hb, hbj⟩ := ih
      refine ⟨y * b * y⁻¹ * c⁻¹, hPmul _ _ (hPconj y hy b hb) (hPinv c hPc), ?_⟩
      calc y ^ (j + 1) * x = y * (y ^ j * x) := by rw [pow_succ', mul_assoc]
        _ = y * (b * x * y ^ j) := by rw [hbj]
        _ = y * b * y⁻¹ * c⁻¹ * x * y ^ (j + 1) := by rw [hc, pow_succ']; group
  have hxy : ∀ j : ℕ, ∃ b, P b ∧ (x * y) ^ j = b * x ^ j * y ^ j := by
    intro j
    induction j with
    | zero => exact ⟨1, ⟨one_mem _, by simp⟩, by simp⟩
    | succ j ih =>
      obtain ⟨b, hb, hbj⟩ := ih
      obtain ⟨b', hb', hb'j⟩ := hyx j
      refine ⟨b * (x ^ j * b' * (x ^ j)⁻¹), hPmul _ _ hb (hPconj _ (pow_mem hx j) b' hb'), ?_⟩
      calc (x * y) ^ (j + 1) = b * x ^ j * (y ^ j * x) * y := by rw [pow_succ, hbj]; group
        _ = b * x ^ j * (b' * x * y ^ j) * y := by rw [hb'j]
        _ = b * (x ^ j * b' * (x ^ j)⁻¹) * x ^ (j + 1) * y ^ (j + 1) := by
          rw [pow_succ, pow_succ]; group
  obtain ⟨b, hb, hbL⟩ := hxy (orderOf x * orderOf y)
  have hx1 : x ^ (orderOf x * orderOf y) = 1 := by rw [pow_mul, pow_orderOf_eq_one, one_pow]
  have hy1 : y ^ (orderOf x * orderOf y) = 1 := by
    rw [mul_comm, pow_mul, pow_orderOf_eq_one, one_pow]
  rw [hx1, hy1, mul_one, mul_one] at hbL
  have h1 : (x * y) ^ (orderOf x * orderOf y * orderOf b) = 1 := by
    rw [pow_mul, hbL, pow_orderOf_eq_one]
  exact Odd.of_dvd_nat ((hxo.mul hyo).mul hb.2) (orderOf_dvd_of_pow_eq_one h1)

end CFSG.ComponentClassification.AutL2Facts
