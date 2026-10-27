module

public import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Tactic.Group

public section

namespace CFSG.ClassicalInvolution.NDB.WC

variable {G : Type*} [Group G]

theorem inv_conj_of_odd {x o : G} (hx : x * x = 1) (ho : Odd (orderOf o))
    (hxo : x * o * (x * o) = 1) : ∃ w ∈ Subgroup.zpowers o, x * o = w⁻¹ * x * w := by
  obtain ⟨j, hj⟩ := ho
  have h1 : x * o * x = o⁻¹ := by
    have : x * o * x * o = 1 := by rw [← hxo]; group
    exact eq_inv_of_mul_eq_one_left this
  have h2 : ∀ n : ℕ, x * o ^ n * x = o⁻¹ ^ n := by
    intro n
    induction n with
    | zero => simpa using hx
    | succ n ih =>
      calc x * o ^ (n + 1) * x = x * o ^ n * (x * x) * o * x := by rw [hx, pow_succ]; group
        _ = (x * o ^ n * x) * (x * o * x) := by group
        _ = o⁻¹ ^ (n + 1) := by rw [ih, h1, pow_succ]
  refine ⟨o ^ (j + 1), pow_mem (Subgroup.mem_zpowers o) _, ?_⟩
  have hw2 : o ^ (j + 1) * o ^ (j + 1) = o := by
    rw [← pow_add, show j + 1 + (j + 1) = orderOf o + 1 by omega, pow_succ, pow_orderOf_eq_one,
      one_mul]
  have hxw : x * o ^ (j + 1) = (o ^ (j + 1))⁻¹ * x := by
    calc x * o ^ (j + 1) = (x * o ^ (j + 1) * x) * x := by rw [mul_assoc _ x x, hx, mul_one]
      _ = (o ^ (j + 1))⁻¹ * x := by rw [h2, inv_pow]
  have hxo' : x * o = o⁻¹ * x := by
    calc x * o = (x * o * x) * x := by rw [mul_assoc _ x x, hx, mul_one]
      _ = o⁻¹ * x := by rw [h1]
  calc x * o = o⁻¹ * x := hxo'
    _ = (o ^ (j + 1) * o ^ (j + 1))⁻¹ * x := by rw [hw2]
    _ = (o ^ (j + 1))⁻¹ * ((o ^ (j + 1))⁻¹ * x) := by group
    _ = (o ^ (j + 1))⁻¹ * (x * o ^ (j + 1)) := by rw [hxw]
    _ = (o ^ (j + 1))⁻¹ * x * o ^ (j + 1) := by group

theorem exists_conj_mem_zpowers {O : Subgroup G} (hO : Odd (Nat.card O)) {x : G}
    (hx : x * x = 1) (hxO : ∀ o ∈ O, x * o * x ∈ O) {o₀ : G} (ho₀ : o₀ ∈ O) :
    ∃ w ∈ O, w⁻¹ * x * w ∈ Subgroup.zpowers (x * o₀) := by
  set y := x * o₀ with hy
  have hyy : y * y ∈ O := by
    have e : y * y = (x * o₀ * x) * o₀ := by rw [hy]; group
    rw [e]
    exact O.mul_mem (hxO o₀ ho₀) ho₀
  obtain ⟨j, hj⟩ : Odd (orderOf (y * y)) :=
    Odd.of_dvd_nat hO (Subgroup.orderOf_dvd_natCard O hyy)
  set o₃ := x * (y * y) ^ j * x * o₀ with ho₃
  have ho₃O : o₃ ∈ O := O.mul_mem (hxO _ (O.pow_mem hyy j)) ho₀
  have hxo₃ : x * o₃ = y ^ (2 * j + 1) := by
    calc x * o₃ = (x * x) * (y * y) ^ j * (x * o₀) := by rw [ho₃]; group
      _ = y ^ (2 * j + 1) := by rw [hx, one_mul, ← hy, pow_succ, pow_mul, sq]
  have hsq : x * o₃ * (x * o₃) = 1 := by
    rw [hxo₃, ← pow_add, show 2 * j + 1 + (2 * j + 1) = 2 * (2 * j + 1) by ring, pow_mul, sq,
      ← hj, pow_orderOf_eq_one]
  obtain ⟨w, hw, hxw⟩ := inv_conj_of_odd hx (Odd.of_dvd_nat hO
    (Subgroup.orderOf_dvd_natCard O ho₃O)) hsq
  refine ⟨w, (Subgroup.zpowers_le.mpr ho₃O) hw, ?_⟩
  rw [← hxw, hxo₃]
  exact pow_mem (Subgroup.mem_zpowers y) _

theorem exists_mul_mem_centralizer {O : Subgroup G} (hO : Odd (Nat.card O)) {x m : G}
    (hx : x * x = 1) (hxO : ∀ o ∈ O, x * o * x ∈ O) (hm : m⁻¹ * x * m * x ∈ O) :
    ∃ w ∈ O, m * w⁻¹ ∈ Subgroup.centralizer ({x} : Set G) := by
  set o₁ := x * (m⁻¹ * x * m * x) * x with ho₁
  have ho₁O : o₁ ∈ O := hxO _ hm
  have he : x * o₁ = m⁻¹ * x * m := by
    rw [ho₁]
    calc x * (x * (m⁻¹ * x * m * x) * x) = (x * x) * (m⁻¹ * x * m) * (x * x) := by group
      _ = m⁻¹ * x * m := by rw [hx, one_mul, mul_one]
  have hsq : x * o₁ * (x * o₁) = 1 := by
    rw [he]
    calc m⁻¹ * x * m * (m⁻¹ * x * m) = m⁻¹ * (x * x) * m := by group
      _ = 1 := by rw [hx, mul_one, inv_mul_cancel]
  obtain ⟨w, hw, hxw⟩ := inv_conj_of_odd hx (Odd.of_dvd_nat hO
    (Subgroup.orderOf_dvd_natCard O ho₁O)) hsq
  refine ⟨w, (Subgroup.zpowers_le.mpr ho₁O) hw, ?_⟩
  rw [Subgroup.mem_centralizer_singleton_iff]
  have e2 : m⁻¹ * x * m = w⁻¹ * x * w := he.symm.trans hxw
  calc m * w⁻¹ * x = m * (w⁻¹ * x * w) * w⁻¹ := by group
    _ = m * (m⁻¹ * x * m) * w⁻¹ := by rw [e2]
    _ = x * (m * w⁻¹) := by group

end CFSG.ClassicalInvolution.NDB.WC
