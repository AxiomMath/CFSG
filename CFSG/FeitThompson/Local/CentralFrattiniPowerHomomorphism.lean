module
import CFSG.FeitThompson.Local.FrattiniQuotientPPowerElementaryAbelian
public import Mathlib.GroupTheory.Frattini
import CFSG.FeitThompson.Local.ClassTwoProductPowers

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open scoped commutatorElement

variable {p n : ℕ} {C : Type*} [Group C]

theorem commutator_le_center_of_frattini_le_center (hp : p.Prime) (hC : Nat.card C = p ^ n)
    (hΦ : frattini C ≤ Subgroup.center C) : commutator C ≤ Subgroup.center C :=
  (commutator_le_frattini hp hC).trans hΦ

theorem pow_mem_center_of_frattini_le_center (hp : p.Prime) (hC : Nat.card C = p ^ n)
    (hΦ : frattini C ≤ Subgroup.center C) (x : C) : x ^ p ∈ Subgroup.center C :=
  hΦ (pow_mem_frattini hp hC x)

theorem commutatorElement_pow_eq_one_of_frattini_le_center (hp : p.Prime)
    (hC : Nat.card C = p ^ n) (hΦ : frattini C ≤ Subgroup.center C) (a b : C) :
    ⁅a, b⁆ ^ p = 1 := by
  rw [← commutatorElement_pow_left_of_mem_center
    (commutatorElement_mem_center_of_commutator_le_center
      (commutator_le_center_of_frattini_le_center hp hC hΦ) a b) p,
    commutatorElement_eq_one_iff_commute]
  exact (Subgroup.mem_center_iff.mp (pow_mem_center_of_frattini_le_center hp hC hΦ a) b).symm

theorem pow_eq_one_of_mem_commutator_of_frattini_le_center (hp : p.Prime)
    (hC : Nat.card C = p ^ n) (hΦ : frattini C ≤ Subgroup.center C) {g : C}
    (hg : g ∈ commutator C) : g ^ p = 1 := by
  have hcen := commutator_le_center_of_frattini_le_center hp hC hΦ
  rw [commutator_eq_closure] at hg
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
      obtain ⟨a, b, rfl⟩ := hx
      exact commutatorElement_pow_eq_one_of_frattini_le_center hp hC hΦ a b
  | one => exact one_pow p
  | mul x y hx _ ihx ihy =>
      have hxc : x ∈ Subgroup.center C := hcen (by rwa [commutator_eq_closure])
      have hcom : Commute x y := (Subgroup.mem_center_iff.mp hxc y).symm
      rw [hcom.mul_pow, ihx, ihy, one_mul]
  | inv x _ ih => rw [inv_pow, ih, inv_one]

theorem mul_pow_of_frattini_le_center (hp : p.Prime) (hodd : Odd p) (hC : Nat.card C = p ^ n)
    (hΦ : frattini C ≤ Subgroup.center C) (x y : C) : (x * y) ^ p = x ^ p * y ^ p := by
  have h2 : 2 ∣ p - 1 := (Nat.Odd.sub_odd hodd odd_one).two_dvd
  rw [mul_pow_commutatorElement_of_commutator_le_center
      (commutator_le_center_of_frattini_le_center hp hC hΦ) x y p,
    Nat.mul_div_assoc _ h2, pow_mul,
    commutatorElement_pow_eq_one_of_frattini_le_center hp hC hΦ y x, one_pow, mul_one]

def powMonoidHomOfFrattiniLeCenter (hp : p.Prime) (hodd : Odd p) (hC : Nat.card C = p ^ n)
    (hΦ : frattini C ≤ Subgroup.center C) : C →* C :=
  MonoidHom.mk' (· ^ p) (mul_pow_of_frattini_le_center hp hodd hC hΦ)

@[simp]
theorem powMonoidHomOfFrattiniLeCenter_apply (hp : p.Prime) (hodd : Odd p)
    (hC : Nat.card C = p ^ n) (hΦ : frattini C ≤ Subgroup.center C) (x : C) :
    powMonoidHomOfFrattiniLeCenter hp hodd hC hΦ x = x ^ p := (rfl)

theorem commutator_le_center_of_frattini_le_center_of_isPGroup (hp : p.Prime) [Finite C]
    (hC : IsPGroup p C) (hΦ : frattini C ≤ Subgroup.center C) :
    commutator C ≤ Subgroup.center C := by
  have := Fact.mk hp
  obtain ⟨n, hn⟩ := hC.exists_card_eq
  exact commutator_le_center_of_frattini_le_center (n := n) hp hn hΦ

theorem pow_eq_one_of_mem_commutator_of_frattini_le_center_of_isPGroup (hp : p.Prime) [Finite C]
    (hC : IsPGroup p C) (hΦ : frattini C ≤ Subgroup.center C) {g : C} (hg : g ∈ commutator C) :
    g ^ p = 1 := by
  have := Fact.mk hp
  obtain ⟨n, hn⟩ := hC.exists_card_eq
  exact pow_eq_one_of_mem_commutator_of_frattini_le_center (n := n) hp hn hΦ hg

theorem mul_pow_of_frattini_le_center_of_isPGroup (hp : p.Prime) (hodd : Odd p) [Finite C]
    (hC : IsPGroup p C) (hΦ : frattini C ≤ Subgroup.center C) (x y : C) :
    (x * y) ^ p = x ^ p * y ^ p := by
  have := Fact.mk hp
  obtain ⟨n, hn⟩ := hC.exists_card_eq
  exact mul_pow_of_frattini_le_center (n := n) hp hodd hn hΦ x y

end

end CFSG.FeitThompson
