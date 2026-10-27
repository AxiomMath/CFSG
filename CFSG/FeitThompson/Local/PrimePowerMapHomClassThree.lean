module

import CFSG.FeitThompson.Local.TripleCommutatorsCentralProductCollection
public import CFSG.FeitThompson.Local.PrimePowerHomTorsionDetectsAutomorphisms
import Mathlib.Data.Nat.Choose.Dvd

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open scoped commutatorElement

variable {p : ℕ} {R : Type*} [Group R]

theorem pow_eq_one_of_mem_commutator (hexp : ∀ c ∈ commutator R, c ^ p = 1)
    {c : R} (hc : c ∈ commutator R) {n : ℕ} (hn : p ∣ n) : c ^ n = 1 := by
  obtain ⟨k, rfl⟩ := hn
  rw [pow_mul, hexp c hc, one_pow]

theorem inv_mul_inv_mul_mul_mem_commutator (a b : R) : a⁻¹ * b⁻¹ * a * b ∈ commutator R := by
  have h : a⁻¹ * b⁻¹ * a * b = ⁅a⁻¹, b⁻¹⁆ := by rw [commutatorElement_def]; group
  rw [h, commutator_def]
  exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)

theorem inv_mul_inv_mul_mul_mem_commutator_commutator {c : R} (hc : c ∈ commutator R) (b : R) :
    c⁻¹ * b⁻¹ * c * b ∈ ⁅commutator R, (⊤ : Subgroup R)⁆ := by
  have h : c⁻¹ * b⁻¹ * c * b = ⁅c⁻¹, b⁻¹⁆ := by rw [commutatorElement_def]; group
  rw [h]
  exact Subgroup.commutator_mem_commutator (inv_mem hc) (Subgroup.mem_top _)

theorem mul_pow_eq_pow_mul_pow_of_triple_commutator_le_center
    (hp : p.Prime) (hp3 : 3 < p)
    (hZ : ⁅commutator R, (⊤ : Subgroup R)⁆ ≤ Subgroup.center R)
    (hexp : ∀ c ∈ commutator R, c ^ p = 1) (x y : R) :
    (x * y) ^ p = x ^ p * y ^ p := by
  set c : R := y⁻¹ * x⁻¹ * y * x with hc
  set d : R := c⁻¹ * x⁻¹ * c * x with hd
  set e : R := c⁻¹ * y⁻¹ * c * y with he
  have hcmem : c ∈ commutator R := inv_mul_inv_mul_mul_mem_commutator y x
  have hdmem : d ∈ commutator R := inv_mul_inv_mul_mul_mem_commutator c x
  have hemem : e ∈ commutator R := inv_mul_inv_mul_mul_mem_commutator c y
  have hdcomm : ∀ g : R, Commute d g := fun g =>
    (Subgroup.mem_center_iff.mp (hZ (inv_mul_inv_mul_mul_mem_commutator_commutator hcmem x)) g).symm
  have hecomm : ∀ g : R, Commute e g := fun g =>
    (Subgroup.mem_center_iff.mp (hZ (inv_mul_inv_mul_mul_mem_commutator_commutator hcmem y)) g).symm
  rw [mul_pow_of_relations (x := x) (y := y) (c := c) (d := d) (e := e)
      (by rw [hc]; group) (by rw [hd]; group) (by rw [he]; group)
      (hdcomm x) (hdcomm y) (hdcomm c) (hdcomm e)
      (hecomm x) (hecomm y) (hecomm c) p]
  have h2 : p ∣ p.choose 2 := hp.dvd_choose_self (by norm_num) (by omega)
  have h3 : p ∣ p.choose 3 := hp.dvd_choose_self (by norm_num) (by omega)
  rw [pow_eq_one_of_mem_commutator hexp hcmem h2,
    pow_eq_one_of_mem_commutator hexp hdmem h3,
    pow_eq_one_of_mem_commutator hexp hemem ((h3.mul_left 2).add h2)]
  group

def powHomOfTripleCommutatorLeCenter (hp : p.Prime) (hp3 : 3 < p)
    (hZ : ⁅commutator R, (⊤ : Subgroup R)⁆ ≤ Subgroup.center R)
    (hexp : ∀ c ∈ commutator R, c ^ p = 1) : R →* R :=
  powHom p (mul_pow_eq_pow_mul_pow_of_triple_commutator_le_center hp hp3 hZ hexp)

@[simp] theorem powHomOfTripleCommutatorLeCenter_apply (hp : p.Prime) (hp3 : 3 < p)
    (hZ : ⁅commutator R, (⊤ : Subgroup R)⁆ ≤ Subgroup.center R)
    (hexp : ∀ c ∈ commutator R, c ^ p = 1) (x : R) :
    powHomOfTripleCommutatorLeCenter hp hp3 hZ hexp x = x ^ p :=
  powHom_apply _ x

theorem coe_ker_powHomOfTripleCommutatorLeCenter (hp : p.Prime) (hp3 : 3 < p)
    (hZ : ⁅commutator R, (⊤ : Subgroup R)⁆ ≤ Subgroup.center R)
    (hexp : ∀ c ∈ commutator R, c ^ p = 1) :
    ((powHomOfTripleCommutatorLeCenter hp hp3 hZ hexp).ker : Set R) = {x : R | x ^ p = 1} :=
  coe_ker_powHom _

theorem mul_pow_pow_eq_pow_mul_pow_of_triple_commutator_le_center
    (hp : p.Prime) (hp3 : 3 < p)
    (hZ : ⁅commutator R, (⊤ : Subgroup R)⁆ ≤ Subgroup.center R)
    (hexp : ∀ c ∈ commutator R, c ^ p = 1) (k : ℕ) (x y : R) :
    (x * y) ^ p ^ k = x ^ p ^ k * y ^ p ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, pow_mul, pow_mul, pow_mul, ih,
      mul_pow_eq_pow_mul_pow_of_triple_commutator_le_center hp hp3 hZ hexp]

end CFSG.FeitThompson
