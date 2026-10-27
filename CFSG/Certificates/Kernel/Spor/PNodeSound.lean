module

public import Certificates.Data.Kernel.Spor.PNode
public import Aesop.BuiltinRules
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Tactic.Push
public import Mathlib.Tactic.ToDual

public section

namespace CFSG.KS.PNode

open CFSG.KC.Enum CFSG.KS CFSG.KS.PEnum

theorem ff {P : Prop} (h : false = true) : P := absurd h (by decide)

theorem beq_false {a b : Nat} (h : a ≠ b) : Nat.beq a b = false := by
  cases hb : Nat.beq a b
  · rfl
  · exact absurd (Nat.eq_of_beq_eq_true hb) h

theorem pathK_zero (PL : Nat → Nat) (i : Nat) : pathK PL 0 i = [] := rfl

theorem pathK_succ (PL : Nat → Nat) (f i : Nat) :
    pathK PL (f + 1) i = if i = 0 then [] else labOf PL i :: pathK PL f (parOf PL i) := by
  change Bool.rec (motive := fun _ => List Nat) (List.cons (labOf PL i) (pathK PL f (parOf PL i)))
    List.nil (Nat.beq i 0) = _
  by_cases h : i = 0
  · subst h
    rfl
  · rw [if_neg h]
    have hb : Nat.beq i 0 = false := beq_false h
    rw [hb]

theorem getK_eq (l : List Nat) (j : Nat) : getK l j = l.getD j 0 := by
  induction l generalizing j with
  | nil => rfl
  | cons x l ih =>
    cases j with
    | zero => rfl
    | succ k =>
      change getK l k = _
      rw [ih]
      rfl

theorem memK_spec {x : Nat} {l : List Nat} (h : memK x l = true) : x ∈ l := by
  induction l with
  | nil => exact ff h
  | cons y l ih =>
    change bIf(Nat.beq x y, true, memK x l) = true at h
    by_cases hxy : x = y
    · subst hxy
      exact List.mem_cons_self
    · rw [beq_false hxy] at h
      exact List.mem_cons_of_mem _ (ih h)

theorem parK_eq (PP p : List Nat) : parK PP p = (p.map fun j => PP.getD j 0).sum % 2 := by
  unfold parK
  congr 1
  induction p with
  | nil => rfl
  | cons j p ih =>
    change Nat.add (getK PP j) _ = _
    rw [ih, getK_eq, List.map_cons, List.sum_cons]
    rfl

theorem pathCodes_eq (PL : Nat → Nat) (PR : List Nat) (i : Nat) :
    pathCodes PL PR i = (pathK PL i i).map fun j => 2 * PR.getD j 0 + 1 := by
  unfold pathCodes
  induction pathK PL i i with
  | nil => rfl
  | cons j p ih =>
    change List.cons (Nat.succ (Nat.mul 2 (getK PR j))) _ = _
    rw [ih, getK_eq, List.map_cons]
    rfl

theorem eqLK_spec : ∀ {u v : List Nat}, eqLK u v = true → u = v
  | [], [], _ => rfl
  | [], _ :: _, h => ff h
  | _ :: _, [], h => ff h
  | x :: u, y :: v, h => by
    change bAnd(Nat.beq x y, eqLK u v) = true at h
    cases hb : Nat.beq x y
    · rw [hb] at h
      exact ff h
    · rw [hb] at h
      rw [Nat.eq_of_beq_eq_true hb, eqLK_spec h]

theorem nodesK_spec {n w m : Nat} {T PL : Nat → Nat} {PP INV : List Nat} :
    ∀ (NW : List Nat) (i0 : Nat), nodesK n w m T PL PP INV NW i0 = true →
      ∀ k < NW.length, nodeK n w m T PL PP INV (i0 + k) (NW.getD k 0) = true
  | [], _, _, k, hk => absurd hk (by simp)
  | nw :: NW, i0, h, k, hk => by
    change bAnd(nodeK n w m T PL PP INV i0 nw, nodesK n w m T PL PP INV NW (Nat.succ i0)) =
      true at h
    cases h1 : nodeK n w m T PL PP INV i0 nw
    · rw [h1] at h
      exact ff h
    · rw [h1] at h
      cases k with
      | zero => exact h1
      | succ k =>
        have := nodesK_spec NW (Nat.succ i0) h k (by simpa using hk)
        rw [show i0 + (k + 1) = Nat.succ i0 + k by omega]
        exact this

theorem strictB_app (y : Nat) (k : Nat → Bool) : strictB y k = k y := by cases y <;> rfl

theorem nodeK_odd {n w m : Nat} {T PL : Nat → Nat} {PP INV : List Nat} {i nw : Nat}
    (h : nodeK n w m T PL PP INV i nw = true) (hodd : parK PP (pathK PL i i) = 1) :
    i ∈ INV ∨ ∃ x < n, pg w m (T i) (pg w m (T i) x) ≠ x := by
  unfold nodeK at h
  rw [show Nat.beq (parK PP (pathK PL i i)) 1 = true from by rw [hodd]; rfl] at h
  change bIf(Nat.beq nw 0, memK i INV, strictB (Nat.sub nw 1) (fun x => strictB (T i) (fun t =>
    bAnd(Nat.blt x n, bIf(Nat.beq (pg w m t (pg w m t x)) x, false, true))))) = true at h
  cases hb : Nat.beq nw 0
  · rw [hb] at h
    change strictB (Nat.sub nw 1) _ = true at h
    rw [strictB_app, strictB_app] at h
    change bAnd(Nat.blt (nw - 1) n, bIf(Nat.beq (pg w m (T i) (pg w m (T i) (nw - 1))) (nw - 1),
      false, true)) = true at h
    cases h1 : Nat.blt (nw - 1) n
    · rw [h1] at h
      exact ff h
    · rw [h1] at h
      refine Or.inr ⟨nw - 1, Nat.le_of_ble_eq_true h1, fun he => ?_⟩
      rw [he, Nat.beq_refl] at h
      exact ff h
  · rw [hb] at h
    exact Or.inl (memK_spec h)

theorem sqPathsK_spec {PL : Nat → Nat} {PR : List Nat} :
    ∀ (INV : List Nat) (R : List (List Nat)), sqPathsK PL PR INV R = true →
      ∀ i ∈ INV, pathCodes PL PR i ++ pathCodes PL PR i ∈ R
  | [], _, _, i, hi => absurd hi (by simp)
  | j :: INV, [], h, _, _ => ff h
  | j :: INV, r :: R, h, i, hi => by
    change bAnd(eqLK r (List.append (pathCodes PL PR j) (pathCodes PL PR j)),
      sqPathsK PL PR INV R) = true at h
    cases h1 : eqLK r (List.append (pathCodes PL PR j) (pathCodes PL PR j))
    · rw [h1] at h
      exact ff h
    · rw [h1] at h
      rcases List.mem_cons.1 hi with rfl | hi
      · rw [eqLK_spec h1]
        exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (sqPathsK_spec INV R h i hi)

end CFSG.KS.PNode

end
