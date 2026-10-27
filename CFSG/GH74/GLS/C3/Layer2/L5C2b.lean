module

public import CFSG.GH74.GLS.C3.Layer2.L5FinInputs
public import Mathlib.Tactic.ContinuousFunctionalCalculus
public import Mathlib.Tactic.Positivity.Finset

public section

namespace CFSG.GH74.GLS.C3.Layer2.L5

open Equiv Perm Subgroup

namespace Fus

structure Idx (n : Nat) where
  i : Fin n

namespace Idx

@[expose] def v {n : Nat} (a : Idx n) : Nat := a.i.val

instance {n : Nat} : DecidableEq (Idx n) := fun a b =>
  decidable_of_iff (a.i = b.i) ⟨fun h => by cases a; cases b; simp_all, fun h => by rw [h]⟩

instance {n : Nat} : Finite (Idx n) :=
  Finite.of_injective Idx.i (fun a b h => by cases a; cases b; simp_all)

@[expose] def equivFin (n : Nat) : Idx n ≃ Fin n where
  toFun := Idx.i
  invFun := Idx.mk
  left_inv a := by cases a; rfl
  right_inv _ := rfl

theorem v_lt {n : Nat} (a : Idx n) : a.v < n := a.i.isLt

theorem ext {n : Nat} {a b : Idx n} (h : a.v = b.v) : a = b := by
  cases a; cases b; simp_all [v, Fin.ext_iff]

end Idx

@[expose] def elemsI (n : Nat) : List (Idx n) := (List.finRange n).map Idx.mk

theorem mem_elemsI {n : Nat} (a : Idx n) : a ∈ elemsI n := by
  simp [elemsI]

theorem nodup_elemsI (n : Nat) : (elemsI n).Nodup :=
  (List.nodup_finRange n).map (fun a b h => by simpa using h)

structure TabData (M : Type) [Group M] where
  n : Nat
  e : Idx n ≃ M
  idxFn : M → Nat
  tab : Array Nat
  invT : Array Nat
  oneI : Nat
  idxFn_spec : ∀ a : Idx n, idxFn (e a) = a.v
  lt_tab : ∀ a b : Idx n, tab.getD (a.v * n + b.v) 0 < n
  tab_spec : ∀ a b : Idx n, e ⟨⟨tab.getD (a.v * n + b.v) 0, lt_tab a b⟩⟩ = e a * e b
  lt_inv : ∀ a : Idx n, invT.getD a.v 0 < n
  inv_spec : ∀ a : Idx n, e ⟨⟨invT.getD a.v 0, lt_inv a⟩⟩ = (e a)⁻¹
  lt_one : oneI < n
  one_spec : e ⟨⟨oneI, lt_one⟩⟩ = 1

namespace TabData

variable {M : Type} [Group M] (D : TabData M)

theorem idxFn_lt (m : M) : D.idxFn m < D.n := by
  have := D.idxFn_spec (D.e.symm m)
  rw [D.e.apply_symm_apply] at this
  rw [this]
  exact Idx.v_lt _

@[expose] def idx (m : M) : Idx D.n := ⟨⟨D.idxFn m, D.idxFn_lt m⟩⟩

theorem e_idx (m : M) : D.e (D.idx m) = m := by
  have h : D.idx m = D.e.symm m := by
    apply Idx.ext
    have := D.idxFn_spec (D.e.symm m)
    rw [D.e.apply_symm_apply] at this
    exact this
  rw [h, D.e.apply_symm_apply]

theorem idx_e (a : Idx D.n) : D.idx (D.e a) = a := by
  apply Idx.ext
  exact D.idxFn_spec a

@[expose] def mulI (a b : Idx D.n) : Idx D.n := ⟨⟨D.tab.getD (a.v * D.n + b.v) 0, D.lt_tab a b⟩⟩

@[expose] def invI (a : Idx D.n) : Idx D.n := ⟨⟨D.invT.getD a.v 0, D.lt_inv a⟩⟩

@[expose] def unitI : Idx D.n := ⟨⟨D.oneI, D.lt_one⟩⟩

theorem e_mulI (a b : Idx D.n) : D.e (D.mulI a b) = D.e a * D.e b := D.tab_spec a b

theorem e_invI (a : Idx D.n) : D.e (D.invI a) = (D.e a)⁻¹ := D.inv_spec a

theorem e_unitI : D.e D.unitI = 1 := D.one_spec

@[expose, instance_reducible] def grp : Group (Idx D.n) where
  mul := D.mulI
  one := D.unitI
  inv := D.invI
  mul_assoc a b c := D.e.injective (by
    show D.e (D.mulI (D.mulI a b) c) = D.e (D.mulI a (D.mulI b c))
    rw [D.e_mulI, D.e_mulI, D.e_mulI, D.e_mulI, mul_assoc])
  one_mul a := D.e.injective (by
    show D.e (D.mulI D.unitI a) = D.e a
    rw [D.e_mulI, D.e_unitI, one_mul])
  mul_one a := D.e.injective (by
    show D.e (D.mulI a D.unitI) = D.e a
    rw [D.e_mulI, D.e_unitI, mul_one])
  inv_mul_cancel a := D.e.injective (by
    show D.e (D.mulI (D.invI a) a) = D.e D.unitI
    rw [D.e_mulI, D.e_invI, D.e_unitI, inv_mul_cancel])

@[expose] def iso : letI := D.grp; M ≃* Idx D.n :=
  letI := D.grp
  { toFun := D.idx
    invFun := fun a => D.e a
    left_inv := fun m => D.e_idx m
    right_inv := fun a => D.idx_e a
    map_mul' := fun a b => D.e.injective (by
      show D.e (D.idx (a * b)) = D.e (D.mulI (D.idx a) (D.idx b))
      rw [D.e_mulI, D.e_idx, D.e_idx, D.e_idx]) }

end TabData

@[expose] def buildTab {M : Type} [Group M] (elems : List M) (code : M → Nat) : Array Nat :=
  let codes := elems.map code
  let arr := elems.toArray
  let n := elems.length
  Id.run do
    let mut t : Array Nat := Array.mkEmpty (n * n)
    for a in [0:n] do
      for b in [0:n] do
        t := t.push (codes.idxOf (code (arr.getD a 1 * arr.getD b 1)))
    return t

@[expose] def buildInv {M : Type} [Group M] (elems : List M) (code : M → Nat) : Array Nat :=
  let codes := elems.map code
  (elems.map fun m => codes.idxOf (code m⁻¹)).toArray

@[expose] def buildOne {M : Type} [Group M] (elems : List M) (code : M → Nat) : Nat :=
  (elems.map code).idxOf (code 1)

@[expose] def tabCheck {M : Type} [Group M] [DecidableEq M] (elems : List M) (code : M → Nat)
    (tab invT : Array Nat) (oneI : Nat) : Bool :=
  decide (elems.map code).Nodup &&
    (List.range elems.length).all (fun a => (List.range elems.length).all fun b =>
      decide (tab.getD (a * elems.length + b) 0 < elems.length) &&
        decide (elems.getD (tab.getD (a * elems.length + b) 0) 1 =
          elems.getD a 1 * elems.getD b 1)) &&
    (List.range elems.length).all (fun a =>
      decide (invT.getD a 0 < elems.length) &&
        decide (elems.getD (invT.getD a 0) 1 = (elems.getD a 1)⁻¹)) &&
    decide (oneI < elems.length) && decide (elems.getD oneI 1 = 1)

theorem tabCheck_spec {M : Type} [Group M] [DecidableEq M] {elems : List M} {code : M → Nat}
    {tab invT : Array Nat} {oneI : Nat} (h : tabCheck elems code tab invT oneI = true) :
    (elems.map code).Nodup ∧
    ((∀ a < elems.length, ∀ b < elems.length,
        tab.getD (a * elems.length + b) 0 < elems.length ∧
          elems.getD (tab.getD (a * elems.length + b) 0) 1 = elems.getD a 1 * elems.getD b 1) ∧
      (∀ a < elems.length, invT.getD a 0 < elems.length ∧
        elems.getD (invT.getD a 0) 1 = (elems.getD a 1)⁻¹)) ∧
    oneI < elems.length ∧ elems.getD oneI 1 = 1 := by
  simp only [tabCheck, Bool.and_eq_true, List.all_eq_true, List.mem_range,
    decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨hnd, hm⟩, hi⟩, ho1⟩, ho2⟩ := h
  exact ⟨hnd, ⟨hm, hi⟩, ho1, ho2⟩

@[expose] def mkTabData {M : Type} [Group M] [DecidableEq M] (elems : List M) (code : M → Nat)
    (hc : ∀ m : M, m ∈ elems) (tab invT : Array Nat) (oneI : Nat)
    (hchk : tabCheck elems code tab invT oneI = true) : TabData M :=
  have hs := tabCheck_spec hchk
  have hn : elems.Nodup := List.Nodup.of_map code hs.1
  let e : Idx elems.length ≃ M := (Idx.equivFin _).trans (hn.getEquivOfForallMemList elems hc)
  have he : ∀ a : Idx elems.length, e a = elems.getD a.v 1 := fun a => by
    show elems.get a.i = _
    simp [Idx.v, List.getD_eq_getElem?_getD]
  let codes := elems.map code
  { n := elems.length
    e := e
    idxFn := fun m => codes.idxOf (code m)
    tab := tab
    invT := invT
    oneI := oneI
    idxFn_spec := fun a => by
      show (elems.map code).idxOf (code (elems.get a.i)) = a.i.val
      have h1 := hs.1.idxOf_getElem a.i.val (by simp)
      simpa [List.getElem_map] using h1
    lt_tab := fun a b => (hs.2.1.1 a.v a.v_lt b.v b.v_lt).1
    tab_spec := fun a b => by
      rw [he, he, he]
      exact (hs.2.1.1 a.v a.v_lt b.v b.v_lt).2
    lt_inv := fun a => (hs.2.1.2 a.v a.v_lt).1
    inv_spec := fun a => by
      rw [he, he]
      exact (hs.2.1.2 a.v a.v_lt).2
    lt_one := hs.2.2.1
    one_spec := by
      rw [he]
      exact hs.2.2.2 }

end Fus

end CFSG.GH74.GLS.C3.Layer2.L5
