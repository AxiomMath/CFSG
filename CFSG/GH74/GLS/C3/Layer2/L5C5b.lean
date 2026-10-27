
module

public import CFSG.GH74.GLS.C3.Layer2.L5C5bBase

public import CFSG.GH74.GLS.C3.Layer2.L5C5a
public import CFSG.GH74.GLS.C3.Layer2.L5C0
public meta import Mathlib.GroupTheory.SpecificGroups.Alternating
public meta import CFSG.GH74.GLS.C3.Prop121.ModelFive
public meta import CFSG.GH74.GLS.C3.Prop121.ModelFiveS
public meta import CFSG.GH74.GLS.C3.Layer2.FinModelDefs
public meta import CFSG.GH74.GLS.C3.Layer2.FinModelEmb
public meta import CFSG.GH74.GLS.C3.Layer2.FinModelEnum
public meta import CFSG.GH74.GLS.C3.Layer2.NumMoved
public meta import CFSG.GH74.GLS.C3.Layer2.L5Fin
public meta import CFSG.GH74.GLS.C3.Layer2.L5A1
public meta import CFSG.GH74.GLS.C3.Layer2.L5B2
public meta import CFSG.GH74.GLS.C3.Layer2.L5C0
public import CFSG.GH74.GLS.C3.Layer2.L5C5bInputs
public meta import CFSG.GH74.GLS.C3.Layer2.L5C5bInputs
public import CFSG.GH74.GLS.C3.Layer2.L5B2
public import CFSG.GH74.GLS.C3.Layer2.FinModelEnum
public import CFSG.GH74.GLS.C3.Layer2.L5C0Inputs
public import Certificates.Certificate5065

public section

namespace CFSG.GH74.GLS.C3.Layer2.L5

open Equiv Perm Subgroup CFSG.GH74.GLS.C3.Prop121 CFSG.GH74.GLS.C3.Layer2
  CFSG.GH74.GLS.C3.Layer2.Model

theorem mt0Chk_true : mt0Chk = true :=
  Certificates.certificate5065.1

theorem inv0Chk_true : inv0Chk = true :=
  Certificates.certificate5065.2.1

theorem one0Chk_true :
    decide (Sh0L.getD 0 1 = 1) = true :=
  Certificates.certificate5065.2.2.1

theorem getD_mem_Sh0L (i : Nat) : Sh0L.getD i 1 ∈ Sh0L := by
  by_cases h : i < Sh0L.length
  · rw [getD_of_lt h]
    exact List.getElem_mem h
  · rw [getD_of_ge (Nat.le_of_not_lt h)]
    exact one_mem_Sh0L

@[expose] def dec0
    (i : Nat) : ↥Sh0 := ⟨Sh0L.getD i 1, getD_mem_Sh0L i⟩

theorem dec0_val
    (i : Nat) : ((dec0 i : ↥Sh0) : Perm (Fin 16)) = Sh0L.getD i 1 := rfl

theorem mt0_lt
    {a b : Nat} (ha : a < 128) (hb : b < 128) : mt0.getD (a * 128 + b) 0 < 128 := by
  have h := mt0Chk_true
  simp only [mt0Chk, List.all_eq_true, List.mem_range, Bool.and_eq_true, decide_eq_true_eq] at h
  exact (h a ha b hb).1

theorem dec0_mul
    {a b : Nat} (ha : a < 128) (hb : b < 128) :
    dec0 (mt0.getD (a * 128 + b) 0) = dec0 a * dec0 b := by
  have h := mt0Chk_true
  simp only [mt0Chk, List.all_eq_true, List.mem_range, Bool.and_eq_true, decide_eq_true_eq] at h
  apply Subtype.ext
  rw [Subgroup.coe_mul, dec0_val, dec0_val, dec0_val]
  exact (h a ha b hb).2

theorem inv0_lt {a : Nat} (ha : a < 128) : inv0.getD a 0 < 128 := by
  have h := inv0Chk_true
  simp only [inv0Chk, List.all_eq_true, List.mem_range, Bool.and_eq_true, decide_eq_true_eq] at h
  exact (h a ha).1

theorem dec0_inv
    {a : Nat} (ha : a < 128) : dec0 (inv0.getD a 0) = (dec0 a)⁻¹ := by
  have h := inv0Chk_true
  simp only [inv0Chk, List.all_eq_true, List.mem_range, Bool.and_eq_true, decide_eq_true_eq] at h
  apply Subtype.ext
  rw [Subgroup.coe_inv, dec0_val, dec0_val]
  exact (h a ha).2

theorem dec0_zero : dec0 0 = 1 := by
  have h := one0Chk_true
  apply Subtype.ext
  rw [dec0_val, Subgroup.coe_one]
  exact of_decide_eq_true h

theorem dec0_inj
    {a b : Nat} (ha : a < 128) (hb : b < 128) (h : dec0 a = dec0 b) : a = b := by
  have h1 : Sh0L.getD a 1 = Sh0L.getD b 1 := congrArg Subtype.val h
  rw [getD_of_lt (by rw [Sh0L_length]; exact ha), getD_of_lt (by rw [Sh0L_length]; exact hb)] at h1
  exact (Sh0L_nodup.getElem_inj_iff).1 h1

theorem dec0_surj (h : ↥Sh0) : ∃ i, i < 128 ∧ dec0 i = h := by
  obtain ⟨i, hi, hh⟩ := List.mem_iff_getElem.1 h.2
  refine ⟨i, by rw [← Sh0L_length]; exact hi, Subtype.ext ?_⟩
  rw [dec0_val, getD_of_lt hi]
  exact hh

theorem idx0Chk_true : idx0Chk = true :=
  Certificates.certificate5065.2.2.2

theorem idx0_dec0
    {i : Nat} (hi : i < 128) : idx0 (dec0 i : Perm (Fin 16)) = i := by
  have h := idx0Chk_true
  simp only [idx0Chk, List.all_eq_true, List.mem_range, decide_eq_true_eq] at h
  exact h i hi

theorem idx0_lt
    (h : ↥Sh0) : idx0 (h : Perm (Fin 16)) < 128 := by
  obtain ⟨i, hi, rfl⟩ := dec0_surj h
  rw [idx0_dec0 hi]
  exact hi

theorem dec0_idx0
    (h : ↥Sh0) : dec0 (idx0 (h : Perm (Fin 16))) = h := by
  obtain ⟨i, hi, rfl⟩ := dec0_surj h
  rw [idx0_dec0 hi]

theorem evFrom_lt
    {x : List Nat} (hx : ∀ k, x.getD k 0 < 128) (w : List Nat) :
    ∀ {a : Nat}, a < 128 → evFrom x a w < 128 := by
  induction w with
  | nil => intro a ha; exact ha
  | cons k w ih =>
    intro a ha
    exact ih (mt0_lt ha (hx k))

theorem dec0_evFrom
    {x : List Nat} (hx : ∀ k, x.getD k 0 < 128) (w : List Nat) :
    ∀ {a : Nat}, a < 128 →
      dec0 (evFrom x a w) = w.foldl (fun A k => A * dec0 (x.getD k 0)) (dec0 a) := by
  induction w with
  | nil => intro a ha; rfl
  | cons k w ih =>
    intro a ha
    simp only [evFrom, List.foldl_cons] at ih ⊢
    rw [ih (mt0_lt ha (hx k)), dec0_mul ha (hx k)]

theorem dec0_evI
    {x : List Nat} (hx : ∀ k, x.getD k 0 < 128) (w : List Nat) :
    dec0 (evI x w) = evH (fun k => dec0 (x.getD k 0)) w := by
  have := dec0_evFrom hx w (a := 0) (by norm_num)
  rw [dec0_zero] at this
  exact this

theorem evI_lt
    {x : List Nat} (hx : ∀ k, x.getD k 0 < 128) (w : List Nat) : evI x w < 128 :=
  evFrom_lt hx w (by norm_num)

end CFSG.GH74.GLS.C3.Layer2.L5
