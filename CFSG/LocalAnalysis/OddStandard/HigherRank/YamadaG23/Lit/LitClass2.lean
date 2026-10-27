module

public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.Data.Set.Card
public import Mathlib.Tactic.Group

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup
open scoped commutatorElement

variable {X : Type*} [Group X] [Finite X]

private lemma mul_eq_commutator_mul (x y : X) :
    x * y = ⁅x, y⁆ * (y * x) := by
  rw [commutatorElement_def]
  group

private lemma sq_mul_eq_of_commutator {x y c : X} (hxy : x * y = c * (y * x))
    (hcx : c * x = x * c) (hcinv : c⁻¹ = c) :
    (x * y) ^ 2 = c * x ^ 2 * y ^ 2 := by
  have hyx : y * x = c * (x * y) := by
    have h : y * x = c⁻¹ * (x * y) := by
      rw [hxy, ← mul_assoc, inv_mul_cancel, one_mul]
    rw [h, hcinv]
  calc
    (x * y) ^ 2 = x * (y * x) * y := by rw [pow_two]; group
    _ = x * (c * (x * y)) * y := by rw [hyx]
    _ = (x * c) * (x * y) * y := by group
    _ = (c * x) * (x * y) * y := by rw [← hcx]
    _ = c * x ^ 2 * y ^ 2 := by rw [pow_two, pow_two]; group

private lemma commutatorElement_mul_right_of_central {a b c : X}
    (h : ⁅a, c⁆ * b = b * ⁅a, c⁆) :
    ⁅a, b * c⁆ = ⁅a, b⁆ * ⁅a, c⁆ := by
  rw [commutatorElement_mul_right_eq_mul_conj, mul_assoc ⁅a, b⁆ b ⁅a, c⁆, h.symm,
    ← mul_assoc ⁅a, b⁆ ⁅a, c⁆ b, mul_inv_cancel_right]

private lemma ncard_mul_right_image (H : Subgroup X) (g : X) :
    ((fun z : X => z * g) '' (H : Set X)).ncard = Nat.card H := by
  rw [Set.ncard_image_of_injective (H : Set X) (mul_left_injective g)]
  exact (Nat.card_coe_set_eq (H : Set X)).symm

private lemma key_claim {B Z1 : Subgroup X}
    (hcent : ∀ z ∈ Z1, ∀ b ∈ B, z * b = b * z)
    (hsq1 : ∀ z ∈ Z1, z ^ 2 = 1)
    (hcomm : ∀ a ∈ B, ∀ b ∈ B, ⁅a, b⁆ ∈ Z1)
    (hsq : ∀ b ∈ B, b ^ 2 ∈ Z1)
    (hconst : ∀ b ∈ B, ∀ c ∈ B, b ∉ Z1 → c ∉ Z1 → b ^ 2 = c ^ 2)
    {x y : X} (hx : x ∈ B) (hy : y ∈ B) (hxZ : x ∉ Z1) (hyZ : y ∉ Z1)
    (hxyZ : x * y ∉ Z1) :
    ⁅x, y⁆ = x ^ 2 := by
  have hcZ : ⁅x, y⁆ ∈ Z1 := hcomm x hx y hy
  have hcinv : ⁅x, y⁆⁻¹ = ⁅x, y⁆ := by
    have h2 : ⁅x, y⁆ * ⁅x, y⁆ = 1 := by simpa [pow_two] using hsq1 (⁅x, y⁆) hcZ
    exact inv_eq_of_mul_eq_one_right h2
  have hcx : ⁅x, y⁆ * x = x * ⁅x, y⁆ := hcent (⁅x, y⁆) hcZ x hx
  have hsq_eq : (x * y) ^ 2 = ⁅x, y⁆ * x ^ 2 * y ^ 2 :=
    sq_mul_eq_of_commutator (mul_eq_commutator_mul x y) hcx hcinv
  have hx2Z : x ^ 2 ∈ Z1 := hsq x hx
  have hy2 : y ^ 2 = x ^ 2 := hconst y hy x hx hyZ hxZ
  have hxy2 : (x * y) ^ 2 = x ^ 2 := hconst (x * y) (mul_mem hx hy) x hx hxyZ hxZ
  have hs : x ^ 2 = ⁅x, y⁆ * x ^ 2 * x ^ 2 := by
    calc
      x ^ 2 = (x * y) ^ 2 := hxy2.symm
      _ = ⁅x, y⁆ * x ^ 2 * y ^ 2 := hsq_eq
      _ = ⁅x, y⁆ * x ^ 2 * x ^ 2 := by rw [hy2]
  have hs2 : (x ^ 2) ^ 2 = 1 := hsq1 (x ^ 2) hx2Z
  have hss : x ^ 2 * x ^ 2 = 1 := by simpa [pow_two] using hs2
  have hsinv : (x ^ 2)⁻¹ = x ^ 2 := inv_eq_of_mul_eq_one_right hss
  have h1 : ⁅x, y⁆ * (x ^ 2 * x ^ 2) = x ^ 2 := by
    rw [← mul_assoc]
    exact hs.symm
  have h2 : ⁅x, y⁆ = x ^ 2 * (x ^ 2 * x ^ 2)⁻¹ := by
    have := congrArg (· * (x ^ 2 * x ^ 2)⁻¹) h1
    simpa only [mul_inv_cancel_right] using this
  rw [h2, mul_inv_rev, hsinv, ← mul_assoc, hss, one_mul]

theorem lit_class2_abelian {B Z1 : Subgroup X} (hZB : Z1 ≤ B)
    (hcent : ∀ z ∈ Z1, ∀ b ∈ B, z * b = b * z) (hsq1 : ∀ z ∈ Z1, z ^ 2 = 1)
    (hcomm : ∀ a ∈ B, ∀ b ∈ B, ⁅a, b⁆ ∈ Z1) (hsq : ∀ b ∈ B, b ^ 2 ∈ Z1)
    (hcard : Nat.card B = 16 * Nat.card Z1)
    (hconst : ∀ b ∈ B, ∀ c ∈ B, b ∉ Z1 → c ∉ Z1 → b ^ 2 = c ^ 2) :
    ∀ a ∈ B, ∀ b ∈ B, a * b = b * a := by
  intro a ha b hb
  rw [← commutatorElement_eq_one_iff_mul_comm]
  by_contra hne
  have haZ : a ∉ Z1 := fun hz =>
    hne (commutatorElement_eq_one_iff_mul_comm.mpr (hcent a hz b hb))
  have hbZ : b ∉ Z1 := fun hz =>
    hne (commutatorElement_eq_one_iff_mul_comm.mpr (hcent b hz a ha).symm)
  have habZ : a * b ∉ Z1 := by
    intro hab
    refine hne ?_
    rw [commutatorElement_eq_one_iff_mul_comm]
    have h1 : (a * b) * b = b * (a * b) := hcent (a * b) hab b hb
    have h2 : a * b * b = b * a * b := by
      calc
        a * b * b = (a * b) * b := by group
        _ = b * (a * b) := h1
        _ = b * a * b := by group
    exact mul_right_cancel h2
  have hab_comm : ⁅a, b⁆ = a ^ 2 :=
    key_claim hcent hsq1 hcomm hsq hconst ha hb haZ hbZ habZ
  let C1 : Set X := (Z1 : Set X)
  let C2 : Set X := (fun z : X => z * a) '' (Z1 : Set X)
  let C3 : Set X := (fun z : X => z * b) '' (Z1 : Set X)
  let C4 : Set X := (fun z : X => z * (a * b)) '' (Z1 : Set X)
  let U : Set X := (C1 ∪ C2) ∪ (C3 ∪ C4)
  have hmemU : ∀ x : X, x ∈ U ↔
      x ∈ Z1 ∨ x ∈ (fun z : X => z * a) '' (Z1 : Set X) ∨
      x ∈ (fun z : X => z * b) '' (Z1 : Set X) ∨
      x ∈ (fun z : X => z * (a * b)) '' (Z1 : Set X) := by
    intro x
    simp only [U, C1, C2, C3, C4, Set.mem_union, SetLike.mem_coe]
    tauto
  have hC1 : C1.ncard = Nat.card Z1 := by
    change (Z1 : Set X).ncard = Nat.card Z1
    exact (Nat.card_coe_set_eq (Z1 : Set X)).symm
  have hC2 : C2.ncard = Nat.card Z1 := by
    change ((fun z : X => z * a) '' (Z1 : Set X)).ncard = Nat.card Z1
    exact ncard_mul_right_image Z1 a
  have hC3 : C3.ncard = Nat.card Z1 := by
    change ((fun z : X => z * b) '' (Z1 : Set X)).ncard = Nat.card Z1
    exact ncard_mul_right_image Z1 b
  have hC4 : C4.ncard = Nat.card Z1 := by
    change ((fun z : X => z * (a * b)) '' (Z1 : Set X)).ncard = Nat.card Z1
    exact ncard_mul_right_image Z1 (a * b)
  have hU_bound : U.ncard ≤ 4 * Nat.card Z1 := by
    have h1 : U.ncard ≤ (C1 ∪ C2).ncard + (C3 ∪ C4).ncard := by
      change ((C1 ∪ C2) ∪ (C3 ∪ C4)).ncard ≤
        (C1 ∪ C2).ncard + (C3 ∪ C4).ncard
      exact Set.ncard_union_le _ _
    have h2 : (C1 ∪ C2).ncard ≤ C1.ncard + C2.ncard := Set.ncard_union_le _ _
    have h3 : (C3 ∪ C4).ncard ≤ C3.ncard + C4.ncard := Set.ncard_union_le _ _
    calc
      U.ncard ≤ (C1 ∪ C2).ncard + (C3 ∪ C4).ncard := h1
      _ ≤ (C1.ncard + C2.ncard) + (C3.ncard + C4.ncard) := add_le_add h2 h3
      _ = 4 * Nat.card Z1 := by rw [hC1, hC2, hC3, hC4]; ring
  haveI : Nonempty B := ⟨⟨1, B.one_mem⟩⟩
  haveI : Nonempty Z1 := ⟨⟨1, Z1.one_mem⟩⟩
  have hzpos : 0 < Nat.card Z1 := Nat.card_pos
  have hU_lt : U.ncard < Nat.card B :=
    lt_of_le_of_lt hU_bound (by rw [hcard]; omega)
  obtain ⟨e, heB, heU⟩ :=
    Set.exists_mem_notMem_of_ncard_lt_ncard (s := U) (t := (B : Set X)) hU_lt
  have heZ : e ∉ Z1 := fun h => heU (by rw [hmemU e]; tauto)
  have heaZ : e * a ∉ Z1 := by
    intro h
    refine heU ?_
    rw [hmemU e]
    have hmem : e ∈ (fun z : X => z * a) '' (Z1 : Set X) :=
      ⟨e * a * (a ^ 2)⁻¹, mul_mem h (inv_mem (hsq a ha)), by group⟩
    tauto
  have hebZ : e * b ∉ Z1 := by
    intro h
    refine heU ?_
    rw [hmemU e]
    have hmem : e ∈ (fun z : X => z * b) '' (Z1 : Set X) :=
      ⟨e * b * (b ^ 2)⁻¹, mul_mem h (inv_mem (hsq b hb)), by group⟩
    tauto
  have heabZ : e * (a * b) ∉ Z1 := by
    intro h
    refine heU ?_
    rw [hmemU e]
    have hmem : e ∈ (fun z : X => z * (a * b)) '' (Z1 : Set X) :=
      ⟨e * (a * b) * ((a * b) ^ 2)⁻¹,
        mul_mem h (inv_mem (hsq (a * b) (mul_mem ha hb))), by rw [pow_two]; group⟩
    tauto
  have kea : ⁅e, a⁆ = e ^ 2 :=
    key_claim hcent hsq1 hcomm hsq hconst heB ha heZ haZ heaZ
  have keb : ⁅e, b⁆ = e ^ 2 :=
    key_claim hcent hsq1 hcomm hsq hconst heB hb heZ hbZ hebZ
  have keab : ⁅e, a * b⁆ = e ^ 2 :=
    key_claim hcent hsq1 hcomm hsq hconst heB (mul_mem ha hb) heZ habZ heabZ
  have hmult : ⁅e, a * b⁆ = ⁅e, a⁆ * ⁅e, b⁆ :=
    commutatorElement_mul_right_of_central
      (hcent (⁅e, b⁆) (hcomm e heB b hb) a ha)
  have he2 : e ^ 2 = a ^ 2 := hconst e heB a ha heZ haZ
  have hsq_e : e ^ 2 = 1 := by
    have h : e ^ 2 = e ^ 2 * e ^ 2 := by
      calc
        e ^ 2 = ⁅e, a * b⁆ := keab.symm
        _ = ⁅e, a⁆ * ⁅e, b⁆ := hmult
        _ = e ^ 2 * e ^ 2 := by rw [kea, keb]
    have h2 : (1 : X) = e ^ 2 := by
      calc
        (1 : X) = (e ^ 2)⁻¹ * e ^ 2 := (inv_mul_cancel _).symm
        _ = (e ^ 2)⁻¹ * (e ^ 2 * e ^ 2) := by rw [← h]
        _ = e ^ 2 := by rw [← mul_assoc, inv_mul_cancel, one_mul]
    exact h2.symm
  exact hne (by rw [hab_comm, ← he2, hsq_e])

end CFSG.OddStandard.HigherRank.YamadaG23
