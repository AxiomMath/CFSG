module

public import CFSG.GH74.GLS.C3.Prop121.Card7Defs
public import CFSG.GH74.GLS.C3.Prop121.Card7List
public import CFSG.GH74.GLS.C3.Layer2.FinModelCard
public meta import CFSG.GH74.GLS.C3.Prop121.MooreFinite7
public meta import CFSG.GH74.GLS.C3.Prop121.Card7Defs
public meta import CFSG.GH74.GLS.C3.Layer2.FinModelDefs
public meta import CFSG.GH74.GLS.C3.Layer2.NumMoved
public meta import Mathlib.Algebra.Group.End
public meta import Mathlib.Algebra.Group.Subgroup.Defs
public meta import Mathlib.GroupTheory.Perm.Sign
public meta import Mathlib.GroupTheory.Perm.Basic
public meta import Mathlib.GroupTheory.Perm.Fin
public meta import Mathlib.GroupTheory.Perm.Support
public meta import Mathlib.GroupTheory.Perm.Cycle.Basic
public meta import Mathlib.GroupTheory.Perm.Cycle.Type
public meta import Mathlib.GroupTheory.SpecificGroups.Alternating
public meta import Mathlib.Logic.Equiv.Fin.Basic
public meta import Mathlib.Logic.Equiv.Option
public meta import Mathlib.Data.List.FinRange
public meta import CFSG.GH74.GLS.C3.Layer3.Basic
public import CFSG.GH74.GLS.C3.Layer3.Basic
public import CFSG.GH74.GLS.C3.Prop121.MooreFinite7
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.InvolutionCountingOrderFormula
public meta import CFSG.LocalAnalysis.ShultStronglyClosedTI.InvolutionCountingOrderFormula
public meta import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Algebra.BigOperators.Field

public section

namespace CFSG.GH74.GLS.C3.Prop121.Card7.FF

open Subgroup Equiv Perm CFSG.GH74.GLS.C3.Layer2 CFSG.GH74.GLS.C3.Layer2.Model

section Lists

@[expose] def DL : List (Perm (Fin 4)) := (allPerms 4).filter fun d => d * x4 = x4 * d

@[expose] def F7AL : List (Amb 7) :=
  (allPerms 7).flatMap fun r =>
    let s := sign r
    (DL.filter fun d => decide (s = sign d)).map fun d => (r, d)

theorem mem_DL {d : Perm (Fin 4)} : d ∈ DL ↔ d * x4 = x4 * d := by
  simp [DL, mem_allPerms]

theorem mem_F7AL {a : Amb 7} : a ∈ F7AL ↔ a ∈ Fgrp 7 := by
  obtain ⟨r, d⟩ := a
  simp only [F7AL, List.mem_flatMap, List.mem_map, List.mem_filter, decide_eq_true_eq, mem_DL,
    mem_allPerms, true_and, Prod.mk.injEq]
  constructor
  · rintro ⟨a, a1, h, rfl, rfl⟩
    exact ⟨h.1, h.2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨r, d, ⟨h1, h2⟩, rfl, rfl⟩

theorem DL_nodup : DL.Nodup := (allPerms_nodup 4).filter _

theorem F7AL_nodup : F7AL.Nodup := by
  unfold F7AL
  rw [List.nodup_flatMap]
  refine ⟨fun r _ => ?_, ?_⟩
  · exact ((DL_nodup.filter _).map (fun d d' h => (Prod.mk.inj h).2))
  · refine (allPerms_nodup 7).imp (fun {a b} hab => ?_)
    intro l h1 h2
    simp only [List.mem_map] at h1 h2
    obtain ⟨d1, -, rfl⟩ := h1
    obtain ⟨d2, -, h⟩ := h2
    exact hab (Prod.mk.inj h).1.symm

@[expose] def F7L : List F7 := F7AL.pmap (fun a h => ⟨a, mem_F7AL.1 h⟩) (fun _ h => h)

theorem mem_F7L (f : F7) : f ∈ F7L := by
  obtain ⟨a, ha⟩ := f
  unfold F7L
  rw [List.mem_pmap]
  exact ⟨a, mem_F7AL.2 ha, rfl⟩

theorem F7L_nodup : F7L.Nodup := by
  unfold F7L
  refine List.Nodup.pmap (fun a ha b hb h => ?_) F7AL_nodup
  exact congrArg Subtype.val h

end Lists

theorem card_subtype_eq_countP {M : Type*} (L : List M) (hnd : L.Nodup) (P : M → Prop) (Q : M → Bool)
    (h : ∀ m, P m ↔ m ∈ L ∧ Q m = true) : Nat.card {m // P m} = L.countP Q := by
  classical
  have h1 : L.countP Q = (L.filter Q).length := List.countP_eq_length_filter
  rw [h1]
  have hnd' : (L.filter Q).Nodup := hnd.filter _
  have h2 : Nat.card {m // P m} = Nat.card {m // m ∈ (L.filter Q).toFinset} := by
    apply Nat.card_congr
    exact Equiv.subtypeEquivRight (fun m => by simp [h m])
  rw [h2, Nat.card_eq_fintype_card, Fintype.card_coe, List.toFinset_card_of_nodup hnd']

@[expose] def ccardB (u v : F7) : ℕ := F7L.countP fun c => decide (c * u = u * c ∧ c * v = v * c)

theorem ccard_eq_ccardB (u v : F7) : ccard F7 u v = ccardB u v :=
  card_subtype_eq_countP F7L F7L_nodup _ _ (fun c => by simp [mem_F7L])

section Conj

variable {M : Type*} [Group M]

theorem ccard_conj (k u v : M) : ccard M (k * u * k⁻¹) (k * v * k⁻¹) = ccard M u v := by
  unfold ccard
  refine Nat.card_congr ?_
  refine
    { toFun := fun c => ⟨k⁻¹ * c.1 * k, ?_⟩
      invFun := fun c => ⟨k * c.1 * k⁻¹, ?_⟩
      left_inv := fun c => by ext; simp [mul_assoc]
      right_inv := fun c => by ext; simp [mul_assoc] }
  · obtain ⟨c, h1, h2⟩ := c
    constructor
    · calc k⁻¹ * c * k * u = k⁻¹ * (c * (k * u * k⁻¹)) * k := by group
        _ = k⁻¹ * ((k * u * k⁻¹) * c) * k := by rw [h1]
        _ = u * (k⁻¹ * c * k) := by group
    · calc k⁻¹ * c * k * v = k⁻¹ * (c * (k * v * k⁻¹)) * k := by group
        _ = k⁻¹ * ((k * v * k⁻¹) * c) * k := by rw [h2]
        _ = v * (k⁻¹ * c * k) := by group
  · obtain ⟨c, h1, h2⟩ := c
    constructor
    · calc k * c * k⁻¹ * (k * u * k⁻¹) = k * (c * u) * k⁻¹ := by group
        _ = k * (u * c) * k⁻¹ := by rw [h1]
        _ = (k * u * k⁻¹) * (k * c * k⁻¹) := by group
    · calc k * c * k⁻¹ * (k * v * k⁻¹) = k * (c * v) * k⁻¹ := by group
        _ = k * (v * c) * k⁻¹ := by rw [h2]
        _ = (k * v * k⁻¹) * (k * c * k⁻¹) := by group

theorem isInv_conj_iff (k a : M) : IsInv (k * a * k⁻¹) ↔ IsInv a := by
  unfold IsInv
  simp only [conj_pow, ne_eq, conj_eq_one_iff]

theorem commute_conj_iff (k a b : M) :
    (k * a * k⁻¹) * (k * b * k⁻¹) = (k * b * k⁻¹) * (k * a * k⁻¹) ↔ a * b = b * a := by
  have h1 : (k * a * k⁻¹) * (k * b * k⁻¹) = k * (a * b) * k⁻¹ := by group
  have h2 : (k * b * k⁻¹) * (k * a * k⁻¹) = k * (b * a) * k⁻¹ := by group
  rw [h1, h2]
  constructor
  · intro h
    have := mul_right_cancel h
    exact mul_left_cancel this
  · intro h
    rw [h]

end Conj

theorem nm7_conj (k f : F7) : nm7 ((k * f * k⁻¹ : F7) : Amb 7) = nm7 (f : Amb 7) := by
  unfold nm7
  have h1 : ((k * f * k⁻¹ : F7) : Amb 7).1 = (k : Amb 7).1 * (f : Amb 7).1 * (k : Amb 7).1⁻¹ := rfl
  have h2 : ((k * f * k⁻¹ : F7) : Amb 7).2 = (k : Amb 7).2 * (f : Amb 7).2 * (k : Amb 7).2⁻¹ := rfl
  rw [h1, h2, numMoved_conj, numMoved_conj]

theorem xf_conj_iff (k f : F7) : XF (k * f * k⁻¹) ↔ XF f := by
  unfold XF; rw [isInv_conj_iff, nm7_conj]

theorem yf_conj_iff (k f : F7) : YF (k * f * k⁻¹) ↔ YF f := by
  unfold YF; rw [isInv_conj_iff, nm7_conj]

instance decIsInv {M : Type*} [Group M] [DecidableEq M] (a : M) : Decidable (IsInv a) :=
  inferInstanceAs (Decidable (a ^ 2 = 1 ∧ a ≠ 1))

instance decXF (f : F7) : Decidable (XF f) :=
  inferInstanceAs (Decidable (IsInv f ∧ nm7 (f : Amb 7) = 4))

instance decYF (f : F7) : Decidable (YF f) :=
  inferInstanceAs (Decidable (IsInv f ∧ nm7 (f : Amb 7) = 8))

instance decTy3 (f : F7) : Decidable (Ty3 f) :=
  inferInstanceAs (Decidable ((f : Amb 7).2 = 1 ∧ f ^ 3 = 1 ∧ numMoved (f : Amb 7).1 = 3))

instance decTy33 (f : F7) : Decidable (Ty33 f) :=
  inferInstanceAs (Decidable ((f : Amb 7).2 = 1 ∧ f ^ 3 = 1 ∧ numMoved (f : Amb 7).1 = 6))

theorem mem_zpowers_iff_exists_pow_lt {G : Type*} [Group G] [Finite G] {g x : G} {N : ℕ}
    (hN : 0 < N) (h : g ^ N = 1) : x ∈ zpowers g ↔ ∃ n < N, g ^ n = x := by
  classical
  constructor
  · intro hx
    rw [mem_zpowers_iff_mem_range_orderOf] at hx
    simp only [Finset.mem_image, Finset.mem_range] at hx
    obtain ⟨n, hn, rfl⟩ := hx
    exact ⟨n, lt_of_lt_of_le hn (Nat.le_of_dvd hN (orderOf_dvd_of_pow_eq_one h)), rfl⟩
  · rintro ⟨n, -, rfl⟩
    exact Subgroup.pow_mem _ (mem_zpowers g) n

@[expose] def g0 : F7 :=
  ⟨(swap 0 1 * swap 1 2 * (swap 3 4 * swap 4 5), 1), by
    refine ⟨by simp, ?_⟩
    show sign (swap (0 : Fin 7) 1 * swap 1 2 * (swap 3 4 * swap 4 5)) = sign (1 : Perm (Fin 4))
    simp [Perm.sign_mul]⟩

@[expose] def u0 : F7 :=
  ⟨(swap 0 1 * swap 2 3, 1), by
    refine ⟨by simp, ?_⟩
    show sign (swap (0 : Fin 7) 1 * swap 2 3) = sign (1 : Perm (Fin 4))
    simp [Perm.sign_mul]⟩

end CFSG.GH74.GLS.C3.Prop121.Card7.FF
