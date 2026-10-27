module
public import Mathlib.GroupTheory.PGroup
import CFSG.FeitThompson.Local.ClassTwoProductPowers

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

variable {C : Type*} [Group C] {p : ℕ}

def omega1 (p : ℕ) (C : Type*) [Group C] : Subgroup C := Subgroup.closure {x : C | x ^ p = 1}

theorem omega1_eq_closure : omega1 p C = Subgroup.closure {x : C | x ^ p = 1} := (rfl)

theorem mem_omega1_of_pow_eq_one {x : C} (hx : x ^ p = 1) : x ∈ omega1 p C :=
  Subgroup.subset_closure hx

theorem omega1_le {H : Subgroup C} (h : ∀ x : C, x ^ p = 1 → x ∈ H) : omega1 p C ≤ H :=
  (Subgroup.closure_le _).mpr fun _ hx => h _ hx

instance omega1_characteristic : (omega1 p C).Characteristic := by
  rw [Subgroup.characteristic_iff_map_le]
  intro φ
  rw [omega1_eq_closure, MonoidHom.map_closure]
  refine Subgroup.closure_mono ?_
  rintro y ⟨x, hx, rfl⟩
  simpa [← map_pow] using congrArg φ hx

theorem omega1_nontrivial_of_dvd_card [Finite C] (hpp : p.Prime) (hdvd : p ∣ Nat.card C) :
    Nontrivial (omega1 p C) := by
  have : Fact p.Prime := ⟨hpp⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' p hdvd
  refine (Subgroup.nontrivial_iff_exists_ne_one _).mpr
    ⟨x, mem_omega1_of_pow_eq_one (hx ▸ pow_orderOf_eq_one x), ?_⟩
  intro h
  rw [h, orderOf_one] at hx
  exact hpp.one_lt.ne hx

theorem omega1_nontrivial [Finite C] [Nontrivial C] (hpp : p.Prime) (hpg : IsPGroup p C) :
    Nontrivial (omega1 p C) := by
  have : Fact p.Prime := ⟨hpp⟩
  obtain ⟨n, hn, hcard⟩ := hpg.nontrivial_iff_card.mp ‹Nontrivial C›
  exact omega1_nontrivial_of_dvd_card hpp (hcard ▸ dvd_pow_self p hn.ne')

theorem inv_mul_inv_mul_mul_mem_center (hcl : commutator C ≤ Subgroup.center C) (x y : C) :
    y⁻¹ * x⁻¹ * y * x ∈ Subgroup.center C := by
  rw [inv_mul_inv_mul_mul_eq_commutatorElement_of_mem_center
    (commutatorElement_mem_center_of_commutator_le_center hcl y x)]
  exact commutatorElement_mem_center_of_commutator_le_center hcl y x

theorem mul_pow_eq_one_of_odd (hp : Odd p) (hcl : commutator C ≤ Subgroup.center C) {a b : C}
    (ha : a ^ p = 1) (hb : b ^ p = 1) : (a * b) ^ p = 1 := by
  have hcen := inv_mul_inv_mul_mul_mem_center hcl a b
  have hcp : (b⁻¹ * a⁻¹ * b * a) ^ p = 1 := by
    rw [← inv_mul_inv_mul_mul_pow_left_of_mem_center hcen p, hb]
    group
  have hdvd : 2 ∣ p - 1 := (Nat.Odd.sub_odd hp odd_one).two_dvd
  rw [mul_pow_of_commutator_le_center hcl a b p, ha, hb, Nat.mul_div_assoc p hdvd, pow_mul, hcp]
  simp

theorem pow_eq_one_of_mem_omega1 (hp : Odd p) (hcl : commutator C ≤ Subgroup.center C) {x : C}
    (hx : x ∈ omega1 p C) : x ^ p = 1 := by
  rw [omega1_eq_closure] at hx
  induction hx using Subgroup.closure_induction with
  | mem x hx => exact hx
  | one => exact one_pow p
  | mul a b _ _ ha hb => exact mul_pow_eq_one_of_odd hp hcl ha hb
  | inv a _ ha => rw [inv_pow, ha, inv_one]

theorem coe_omega1 (hp : Odd p) (hcl : commutator C ≤ Subgroup.center C) :
    (omega1 p C : Set C) = {x : C | x ^ p = 1} :=
  Set.Subset.antisymm (fun _ hx => pow_eq_one_of_mem_omega1 hp hcl hx)
    fun _ hx => mem_omega1_of_pow_eq_one hx

theorem mem_omega1_iff (hp : Odd p) (hcl : commutator C ≤ Subgroup.center C) {x : C} :
    x ∈ omega1 p C ↔ x ^ p = 1 := Set.ext_iff.mp (coe_omega1 hp hcl) x

theorem exponent_omega1_dvd (hp : Odd p) (hcl : commutator C ≤ Subgroup.center C) :
    Monoid.exponent (omega1 p C) ∣ p :=
  Monoid.exponent_dvd_of_forall_pow_eq_one fun g =>
    Subtype.ext (by simpa using pow_eq_one_of_mem_omega1 hp hcl g.2)

theorem omega1_characteristic_nontrivial_and_coe [Finite C] [Nontrivial C] (hpp : p.Prime)
    (hp : Odd p) (hpg : IsPGroup p C) (hcl : commutator C ≤ Subgroup.center C) :
    (omega1 p C).Characteristic ∧ Nontrivial (omega1 p C) ∧
      (omega1 p C : Set C) = {x : C | x ^ p = 1} :=
  ⟨omega1_characteristic, omega1_nontrivial hpp hpg, coe_omega1 hp hcl⟩

end CFSG.FeitThompson
