module

public import Certificates.Data.Kernel.U38NoE81K
public import CFSG.Certificates.Kernel.Spor.RawOrbEval
public import CFSG.Certificates.Kernel.Spor.Loops
public import Aesop.BuiltinRules
public import Batteries.Data.List.Basic
public import Mathlib.Tactic.Attr.Core
public import Mathlib.Tactic.Push

public section

namespace CFSG.KC.U38QK

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw

theorem allL_eq (f : Nat → Bool) : ∀ L : List Nat, allL f L = L.all f
  | [] => rfl
  | x :: xs => by
    change Bool.rec (motive := fun _ => Bool) false (allL f xs) (f x) = _
    rw [Orb.bAnd_eq, allL_eq f xs, List.all_cons]

theorem forall₂_of_pairK {f : Nat → Nat → Bool} :
    ∀ {I J : List Nat}, pairK f I J = true → List.Forall₂ (fun i j => f i j = true) I J
  | [], [], _ => List.Forall₂.nil
  | [], _ :: _, h => absurd (h : false = true) Bool.false_ne_true
  | _ :: _, [], h => absurd (h : false = true) Bool.false_ne_true
  | i :: is, j :: js, h => by
    have h' : Bool.rec (motive := fun _ => Bool) false (pairK f is js) (f i j) = true := h
    obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 h'
    exact List.Forall₂.cons h1 (forall₂_of_pairK h2)

theorem map_eq_of_forall₂ {R : Nat → Nat → Prop} {α : Type} {g h : Nat → α} :
    ∀ {I J : List Nat}, List.Forall₂ R I J → (∀ i ∈ I, ∀ j ∈ J, R i j → g i = h j) →
      I.map g = J.map h
  | _, _, .nil, _ => rfl
  | _, _, .cons hij hr, e => by
    rw [List.map_cons, List.map_cons, e _ (List.mem_cons.2 (Or.inl rfl)) _
      (List.mem_cons.2 (Or.inl rfl)) hij, map_eq_of_forall₂ hr fun i hi j hj =>
        e i (List.mem_cons_of_mem _ hi) j (List.mem_cons_of_mem _ hj)]

theorem filter_length_of_forall₂ {R : Nat → Nat → Prop} {p q : Nat → Bool} :
    ∀ {I J : List Nat}, List.Forall₂ R I J → (∀ i ∈ I, ∀ j ∈ J, R i j → p i = q j) →
      (I.filter p).length = (J.filter q).length
  | _, _, .nil, _ => rfl
  | _, _, .cons hij hr, e => by
    rw [List.filter_cons, List.filter_cons, e _ (List.mem_cons.2 (Or.inl rfl)) _
      (List.mem_cons.2 (Or.inl rfl)) hij]
    have := filter_length_of_forall₂ hr fun i hi j hj =>
      e i (List.mem_cons_of_mem _ hi) j (List.mem_cons_of_mem _ hj)
    split <;> simp [this]

theorem exists_of_forall₂ {R : Nat → Nat → Prop} :
    ∀ {I J : List Nat}, List.Forall₂ R I J → ∀ i ∈ I, ∃ j ∈ J, R i j
  | _, _, .nil => fun _ h => absurd h List.not_mem_nil
  | _, _, .cons (b := j) hij hr => fun x hx => by
    rcases List.mem_cons.1 hx with rfl | hx
    · exact ⟨j, List.mem_cons_self .., hij⟩
    · obtain ⟨y, hy, r⟩ := exists_of_forall₂ hr x hx
      exact ⟨y, List.mem_cons_of_mem _ hy, r⟩

theorem filter_of_selL {q : Nat → Bool} : ∀ {L S : List Nat}, selL q L S = true → L.filter q = S
  | [], [], _ => rfl
  | [], _ :: _, h => absurd (h : false = true) Bool.false_ne_true
  | x :: xs, S, h => by
    have h' : Bool.rec (motive := fun _ => Bool) (selL q xs S)
        (List.rec (motive := fun _ => Bool) false
          (fun y ys _ => Bool.rec (motive := fun _ => Bool) false (selL q xs ys) (Nat.beq y x)) S)
        (q x) = true := h
    rw [List.filter_cons]
    cases hq : q x
    · rw [hq] at h'
      exact filter_of_selL h'
    · rw [hq] at h'
      cases S with
      | nil => exact absurd (h' : false = true) Bool.false_ne_true
      | cons y ys =>
        obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 h'
        rw [if_pos rfl, Nat.eq_of_beq_eq_true h1, filter_of_selL h2]

end CFSG.KC.U38QK

namespace CFSG.KC.U38NoE81K

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.Co2Mem

theorem cntK_eq_length (f : Nat → Bool) : ∀ N, cntK N f = ((List.range N).filter f).length
  | 0 => rfl
  | N + 1 => by
    change cntK N f + Bool.rec (motive := fun _ => Nat) 0 1 (f N) = _
    rw [cntK_eq_length f N, List.range_succ, List.filter_append, List.length_append]
    cases h : f N <;> simp [h]

theorem bigK_eq : ∀ L : List Nat,
    bigK L = (L.filter fun v => Nat.ble 243 (Nat.div v 1048576)).length
  | [] => rfl
  | v :: L => by
    change bigK L + Bool.rec (motive := fun _ => Nat) 0 1 (Nat.ble 243 (Nat.div v 1048576)) = _
    rw [bigK_eq L, List.filter_cons]
    cases Nat.ble 243 (Nat.div v 1048576) <;> simp [Nat.add_comm]

end CFSG.KC.U38NoE81K

end
