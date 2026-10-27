module

public import CFSG.LocalAnalysis.RankThreeUC.ProofSupport.OddClassTwoBCH.OddClassTwoBCHDefs
import Mathlib.Tactic.Group
public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.Tactic.NormNum.GCD

public section

namespace CFSG.LocalAnalysis.RankThreeUC

namespace ProofSupport

namespace BCHCentralCommutatorLaws

open scoped commutatorElement

open OddClassTwoBCH

variable {E : Type*} [Group E]

@[expose] def CentralComm (E : Type*) [Group E] : Prop :=
  ∀ a b : E, ⁅a, b⁆ ∈ Subgroup.center E

variable (hc : CentralComm E)

include hc

theorem commute_comm (a b c : E) : Commute c ⁅a, b⁆ := by
  have := Subgroup.mem_center_iff.mp (hc a b) c
  exact this

theorem commutator_mul_left (x y z : E) : ⁅x * y, z⁆ = ⁅x, z⁆ * ⁅y, z⁆ := by
  rw [commutatorElement_mul_left_eq_conj_mul]
  have h := commute_comm hc y z x
  have : x * ⁅y, z⁆ * x⁻¹ = ⁅y, z⁆ := by
    rw [h.eq]; simp
  rw [this]; exact ((commute_comm hc y z _).eq).symm

theorem commutator_mul_right (x y z : E) : ⁅x, y * z⁆ = ⁅x, y⁆ * ⁅x, z⁆ := by
  rw [commutatorElement_mul_right_eq_mul_conj]
  have h := commute_comm hc x z y
  have : y * ⁅x, z⁆ * y⁻¹ = ⁅x, z⁆ := by
    rw [h.eq]; simp
  simp only [mul_assoc]
  rw [← mul_assoc y ⁅x, z⁆ y⁻¹, this]

theorem commutator_swap (x y : E) : ⁅y, x⁆ = ⁅x, y⁆⁻¹ := (commutatorElement_inv x y).symm

theorem commutator_pow_left (x y : E) (n : ℕ) : ⁅x ^ n, y⁆ = ⁅x, y⁆ ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, commutator_mul_left hc, ih, pow_succ]

theorem commutator_pow_right (x y : E) (n : ℕ) : ⁅x, y ^ n⁆ = ⁅x, y⁆ ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, commutator_mul_right hc, ih, pow_succ]

theorem commutator_pow_eq_one_left {p : ℕ} {x : E} (hx : x ^ p = 1) (y : E) :
    ⁅x, y⁆ ^ p = 1 := by
  rw [← commutator_pow_left hc, hx]; simp

omit hc in
theorem pow_two_mul_half_succ {p : ℕ} (hp : Odd p) {c : E} (hc : c ^ p = 1) :
    c ^ (2 * ((p + 1) / 2)) = c := by
  obtain ⟨k, rfl⟩ := hp
  have : 2 * ((2 * k + 1 + 1) / 2) = (2 * k + 1) + 1 := by omega
  rw [this, pow_succ, hc, one_mul]

omit hc in
theorem pow_half_pred {p : ℕ} (hp : Odd p) {c : E} (hcp : c ^ p = 1) :
    c ^ ((p + 1) / 2) * c ^ ((p + 1) / 2) = c := by
  rw [← pow_add, ← two_mul]; exact pow_two_mul_half_succ hp hcp

variable {p : ℕ}

theorem commutator_mul_central_left {c : E} (x z : E) (hcz : c ∈ Subgroup.center E) :
    ⁅x * c, z⁆ = ⁅x, z⁆ := by
  rw [commutator_mul_left hc]
  have : ⁅c, z⁆ = 1 := by
    rw [commutatorElement_eq_one_iff_mul_comm]; exact (Subgroup.mem_center_iff.mp hcz z).symm
  rw [this, mul_one]

theorem commutator_mul_central_right {c : E} (x z : E) (hcz : c ∈ Subgroup.center E) :
    ⁅x, z * c⁆ = ⁅x, z⁆ := by
  rw [commutator_mul_right hc]
  have : ⁅x, c⁆ = 1 := by
    rw [commutatorElement_eq_one_iff_mul_comm]; exact (Subgroup.mem_center_iff.mp hcz x)
  rw [this, mul_one]

theorem center_pow_inv_mem (a b : E) (n : ℕ) : (⁅a, b⁆ ^ n)⁻¹ ∈ Subgroup.center E :=
  Subgroup.inv_mem _ (Subgroup.pow_mem _ (hc a b) n)

theorem add_assoc (x y z : BCH p E) : add (add x y) z = add x (add y z) := by
  apply toGroup.injective
  simp only [toGroup_add]
  set h := (p + 1) / 2
  have hA := center_pow_inv_mem hc (toGroup x) (toGroup y) h
  have hB := center_pow_inv_mem hc (toGroup y) (toGroup z) h
  rw [commutator_mul_central_left hc _ _ hA, commutator_mul_central_right hc _ _ hB,
    commutator_mul_left hc, commutator_mul_right hc]
  generalize toGroup x = x, toGroup y = y, toGroup z = z at *
  have hC := center_pow_inv_mem hc x z h
  rw [Commute.mul_pow (commute_comm hc y z _), Commute.mul_pow (commute_comm hc x z _)]
  simp only [mul_inv_rev]
  have e1 : (⁅x, y⁆ ^ h)⁻¹ * z = z * (⁅x, y⁆ ^ h)⁻¹ := (Subgroup.mem_center_iff.mp hA z).symm
  have e2 : (⁅x, y⁆ ^ h)⁻¹ * (⁅y, z⁆ ^ h)⁻¹ = (⁅y, z⁆ ^ h)⁻¹ * (⁅x, y⁆ ^ h)⁻¹ :=
    Subgroup.mem_center_iff.mp hB _
  have e3 : (⁅x, y⁆ ^ h)⁻¹ * (⁅x, z⁆ ^ h)⁻¹ = (⁅x, z⁆ ^ h)⁻¹ * (⁅x, y⁆ ^ h)⁻¹ :=
    Subgroup.mem_center_iff.mp hC _
  simp only [mul_assoc]
  rw [← mul_assoc _ z, e1, mul_assoc z, ← mul_assoc _ (⁅y, z⁆ ^ h)⁻¹, e2, mul_assoc, e3]

theorem add_comm (hp : Odd p) (hexp : ∀ x : E, x ^ p = 1) (x y : BCH p E) :
    add x y = add y x := by
  apply toGroup.injective
  simp only [toGroup_add]
  generalize toGroup x = x, toGroup y = y
  set c := ⁅x, y⁆ with hcdef
  have hcp : c ^ p = 1 := commutator_pow_eq_one_left hc (hexp x) y
  have hxy : x * y = c * (y * x) := by
    rw [hcdef, commutatorElement_def]; group
  have hyx : ⁅y, x⁆ = c⁻¹ := commutator_swap hc x y
  have hh := pow_half_pred hp hcp
  set h := (p + 1) / 2
  have hcen : ∀ w : E, c * w = w * c := fun w =>
    (Subgroup.mem_center_iff.mp (hc x y) w).symm
  have hcenp : ∀ w : E, c ^ h * w = w * c ^ h := fun w => ((commute_comm hc x y w).symm.pow_left h).eq
  rw [hyx, inv_pow, inv_inv, hxy]
  have : c * (c ^ h)⁻¹ = c ^ h := by
    calc c * (c ^ h)⁻¹ = (c ^ h * c ^ h) * (c ^ h)⁻¹ := by rw [hh]
      _ = c ^ h := by simp
  calc c * (y * x) * (c ^ h)⁻¹ = (y * x) * (c * (c ^ h)⁻¹) := by
        calc c * (y * x) * (c ^ h)⁻¹ = (y * x * c) * (c ^ h)⁻¹ := by rw [hcen]
          _ = (y * x) * (c * (c ^ h)⁻¹) := mul_assoc _ _ _
    _ = y * x * c ^ h := by rw [this]

omit hc in
theorem add_zero (x : BCH p E) : add x zero = x := by
  apply toGroup.injective
  simp [toGroup_add]

omit hc in
theorem zero_add (x : BCH p E) : add zero x = x := by
  apply toGroup.injective
  simp [toGroup_add]

omit hc in
theorem neg_add (x : BCH p E) : add (neg x) x = zero := by
  apply toGroup.injective
  have : ⁅(toGroup x)⁻¹, toGroup x⁆ = 1 := by
    rw [commutatorElement_eq_one_iff_mul_comm]; simp
  simp [toGroup_add, this]

end BCHCentralCommutatorLaws
end ProofSupport
end CFSG.LocalAnalysis.RankThreeUC
