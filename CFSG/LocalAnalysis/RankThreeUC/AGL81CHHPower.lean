module

public import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.Group

public section

namespace CFSG.LocalAnalysis.RankThreeUC.AGL81C

open Subgroup
open scoped commutatorElement

variable {K : Type*} [Group K] {B Q : Subgroup K}

private theorem pow_conj_eq_commutator_pow {x y : K} (hc : Commute ⁅x, y⁆ x) :
    ∀ n : ℕ, x ^ n * y * (x ^ n)⁻¹ = ⁅x, y⁆ ^ n * y
  | 0 => by simp
  | n + 1 => by
    have ih := pow_conj_eq_commutator_pow hc n
    have hxy : x * y * x⁻¹ = ⁅x, y⁆ * y := by rw [commutatorElement_def]; group
    calc x ^ (n + 1) * y * (x ^ (n + 1))⁻¹ = x * (x ^ n * y * (x ^ n)⁻¹) * x⁻¹ := by
          rw [pow_succ']; group
      _ = x * (⁅x, y⁆ ^ n * y) * x⁻¹ := by rw [ih]
      _ = ⁅x, y⁆ ^ n * (x * y * x⁻¹) := by
          rw [show x * (⁅x, y⁆ ^ n * y) * x⁻¹ = (x * ⁅x, y⁆ ^ n) * y * x⁻¹ by group,
            ((hc.pow_left n).eq).symm]
          group
      _ = ⁅x, y⁆ ^ (n + 1) * y := by rw [hxy, pow_succ, mul_assoc]

private theorem mul_pow_commutator_choose {x y : K} (hx : Commute ⁅y, x⁆ x)
    (hy : Commute ⁅y, x⁆ y) : ∀ n : ℕ, (x * y) ^ n = x ^ n * y ^ n * ⁅y, x⁆ ^ (n.choose 2)
  | 0 => by simp
  | n + 1 => by
    have ih := mul_pow_commutator_choose hx hy n
    set c := ⁅y, x⁆ with hc
    have hyn : y ^ n * x = c ^ n * x * y ^ n := by
      have h := pow_conj_eq_commutator_pow (x := y) (y := x) hy n
      calc y ^ n * x = (y ^ n * x * (y ^ n)⁻¹) * y ^ n := by group
        _ = c ^ n * x * y ^ n := by rw [h]
    have hcC : Commute (c ^ (n.choose 2)) (x * y) := (hx.pow_left _).mul_right (hy.pow_left _)
    have h1 : Commute (c ^ n) (x ^ (n + 1)) := (hx.pow_left _).pow_right _
    have h2 : Commute (c ^ n) (y ^ (n + 1)) := (hy.pow_left _).pow_right _
    have hch : (n + 1).choose 2 = n + n.choose 2 := by
      rw [Nat.choose_succ_succ', Nat.choose_one_right]
    calc (x * y) ^ (n + 1) = x ^ n * y ^ n * c ^ (n.choose 2) * (x * y) := by rw [pow_succ, ih]
      _ = x ^ n * (y ^ n * x) * y * c ^ (n.choose 2) := by
          rw [mul_assoc (x ^ n * y ^ n), hcC.eq]; group
      _ = c ^ n * x ^ (n + 1) * y ^ (n + 1) * c ^ (n.choose 2) := by
          rw [hyn, pow_succ, pow_succ]
          have h0 : Commute (c ^ n) (x ^ n) := (hx.pow_left _).pow_right _
          calc x ^ n * (c ^ n * x * y ^ n) * y * c ^ n.choose 2
              = (x ^ n * c ^ n) * x * (y ^ n * y) * c ^ n.choose 2 := by group
            _ = (c ^ n * x ^ n) * x * (y ^ n * y) * c ^ n.choose 2 := by rw [h0.eq]
            _ = c ^ n * (x ^ n * x) * (y ^ n * y) * c ^ n.choose 2 := by group
      _ = x ^ (n + 1) * y ^ (n + 1) * c ^ ((n + 1).choose 2) := by
          rw [h1.eq, mul_assoc (x ^ (n + 1)), h2.eq, hch, pow_add]
          group

private theorem commutator_cube_of_commute {x y : K} (hzx : Commute ⁅x, y⁆ x)
    (hx3y : x ^ 3 * y = y * x ^ 3) : ⁅x, y⁆ ^ 3 = 1 := by
  have h := pow_conj_eq_commutator_pow hzx 3
  rw [show x ^ 3 * y * (x ^ 3)⁻¹ = y by rw [hx3y]; group] at h
  exact mul_right_cancel_iff.mp (by rw [← h, one_mul])

private theorem mul_cube_of_central {x y : K} (hcx : Commute ⁅y, x⁆ x)
    (hcy : Commute ⁅y, x⁆ y) (hc3 : ⁅y, x⁆ ^ 3 = 1) : (x * y) ^ 3 = x ^ 3 * y ^ 3 := by
  have h := mul_pow_commutator_choose hcx hcy 3
  have h32 : (3 : ℕ).choose 2 = 3 := by decide
  rw [h, h32, hc3, mul_one]

private theorem cube_mul_cube (hclass : ⁅Q, Q⁆ ≤ centralizer (Q : Set K))
    (hZ : ∀ x ∈ Q, x ^ 3 ∈ centralizer (Q : Set K)) {x y : K} (hx : x ∈ Q) (hy : y ∈ Q) :
    (x * y) ^ 3 = x ^ 3 * y ^ 3 := by
  have hz_mem : ⁅x, y⁆ ∈ ⁅Q, Q⁆ := Subgroup.commutator_mem_commutator hx hy
  have hzx : Commute ⁅x, y⁆ x :=
    ((Subgroup.mem_centralizer_iff.mp (hclass hz_mem)) x hx).symm
  have hzy : Commute ⁅x, y⁆ y :=
    ((Subgroup.mem_centralizer_iff.mp (hclass hz_mem)) y hy).symm
  have hx3y : x ^ 3 * y = y * x ^ 3 :=
    ((Subgroup.mem_centralizer_iff.mp (hZ x hx)) y hy).symm
  have hz3 : ⁅x, y⁆ ^ 3 = 1 := commutator_cube_of_commute hzx hx3y
  have hc_eq : ⁅y, x⁆ = ⁅x, y⁆⁻¹ := by rw [commutatorElement_inv]
  have hcx : Commute ⁅y, x⁆ x := by rw [hc_eq]; exact hzx.inv_left
  have hcy : Commute ⁅y, x⁆ y := by rw [hc_eq]; exact hzy.inv_left
  have hc3 : ⁅y, x⁆ ^ 3 = 1 := by rw [hc_eq, inv_pow, hz3, inv_one]
  exact mul_cube_of_central hcx hcy hc3

theorem inf_centralizer_le_centralizer_self (hBQ : B ≤ normalizer (Q : Set K))
    (hcomm : ⁅Q, B⁆ = Q) (hclass : ⁅Q, Q⁆ ≤ centralizer (Q : Set K))
    (hQ'B : ⁅Q, Q⁆ ≤ centralizer (B : Set K)) :
    Q ⊓ centralizer (B : Set K) ≤ centralizer (Q : Set K) := by
  have hBQ' : ⁅Q, B⁆ ≤ Q := Subgroup.commutator_comm B Q ▸
    (Subgroup.le_normalizer_iff_commutator_le_right (H := B) (K := Q)).mp hBQ
  intro g hg
  rw [Subgroup.mem_inf] at hg
  obtain ⟨hgQ, hgB⟩ := hg
  rw [Subgroup.mem_centralizer_iff]
  intro q hq
  have hQle : Q ≤ Subgroup.centralizer ({g} : Set K) := by
    rw [← hcomm]
    refine Subgroup.commutator_le.mpr ?_
    intro y hy b hb
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hgb : g * b * g⁻¹ = b := by rw [← hgB b hb]; group
    have hgy : g * y * g⁻¹ = ⁅g, y⁆ * y := by
      rw [← MulAut.conj_apply, conj_eq_commutatorElement_mul]
    have hz_mem : ⁅g, y⁆ ∈ ⁅Q, Q⁆ := Subgroup.commutator_mem_commutator hgQ hy
    have hzQ : ⁅g, y⁆ ∈ centralizer (Q : Set K) := hclass hz_mem
    have hzB : ⁅g, y⁆ ∈ centralizer (B : Set K) := hQ'B hz_mem
    have hzyb : ⁅g, y⁆ * ⁅y, b⁆ = ⁅y, b⁆ * ⁅g, y⁆ :=
      ((Subgroup.mem_centralizer_iff.mp hzQ) ⁅y, b⁆
        (hBQ' (Subgroup.commutator_mem_commutator hy hb))).symm
    have hzbc : ⁅⁅g, y⁆, b⁆ = 1 :=
      Commute.commutator_eq (((Subgroup.mem_centralizer_iff.mp hzB) b hb).symm)
    have hqg : g * ⁅y, b⁆ * g⁻¹ = ⁅y, b⁆ := by
      calc g * ⁅y, b⁆ * g⁻¹ = ⁅g * y * g⁻¹, g * b * g⁻¹⁆ :=
            conjugate_commutatorElement y b g
        _ = ⁅⁅g, y⁆ * y, b⁆ := by rw [hgy, hgb]
        _ = ⁅g, y⁆ * ⁅y, b⁆ * ⁅g, y⁆⁻¹ * ⁅⁅g, y⁆, b⁆ :=
            commutatorElement_mul_left_eq_conj_mul ⁅g, y⁆ y b
        _ = ⁅y, b⁆ := by rw [hzbc, mul_one, hzyb]; group
    exact (mul_inv_eq_iff_eq_mul.mp hqg).symm
  exact Subgroup.mem_centralizer_singleton_iff.mp (hQle hq)

theorem pow_three_eq_one (hBQ : B ≤ normalizer (Q : Set K)) (hcomm : ⁅Q, B⁆ = Q)
    (hclass : ⁅Q, Q⁆ ≤ centralizer (Q : Set K))
    (hB : ∀ x ∈ Q, x ^ 3 ∈ centralizer (B : Set K))
    (hZ : ∀ x ∈ Q, x ^ 3 ∈ centralizer (Q : Set K)) : ∀ x ∈ Q, x ^ 3 = 1 := by
  have hcube : ∀ {x y : K}, x ∈ Q → y ∈ Q → (x * y) ^ 3 = x ^ 3 * y ^ 3 :=
    fun {x y} hx hy => cube_mul_cube hclass hZ hx hy
  let Ω : Subgroup K :=
    { carrier := {x : K | x ∈ Q ∧ x ^ 3 = 1}
      mul_mem' := by
        rintro a b ⟨haQ, ha3⟩ ⟨hbQ, hb3⟩
        exact ⟨Q.mul_mem haQ hbQ, by rw [hcube haQ hbQ, ha3, hb3, mul_one]⟩
      one_mem' := ⟨Q.one_mem, one_pow 3⟩
      inv_mem' := by
        rintro a ⟨haQ, ha3⟩
        exact ⟨Q.inv_mem haQ, by rw [inv_pow, ha3, inv_one]⟩ }
  have hQΩ : Q ≤ Ω := by
    rw [← hcomm]
    refine Subgroup.commutator_le.mpr ?_
    intro y hy b hb
    have hy'Q : b * y⁻¹ * b⁻¹ ∈ Q :=
      ((Subgroup.mem_normalizer_iff.mp (hBQ hb)) y⁻¹).mp (Q.inv_mem hy)
    have hyb : ⁅y, b⁆ = y * (b * y⁻¹ * b⁻¹) := by rw [commutatorElement_def]; group
    have hby : b * y ^ 3 * b⁻¹ = y ^ 3 := by
      rw [(Subgroup.mem_centralizer_iff.mp (hB y hy)) b hb]; group
    have hy'3 : (b * y⁻¹ * b⁻¹) ^ 3 = (y ^ 3)⁻¹ := by
      rw [conj_pow, inv_pow]
      rw [show b * (y ^ 3)⁻¹ * b⁻¹ = (b * y ^ 3 * b⁻¹)⁻¹ by group, hby]
    refine ⟨?_, ?_⟩
    · rw [← hcomm]
      exact Subgroup.commutator_mem_commutator hy hb
    · rw [hyb, hcube hy hy'Q, hy'3, mul_inv_cancel]
  intro x hx
  exact (hQΩ hx).2

end CFSG.LocalAnalysis.RankThreeUC.AGL81C
