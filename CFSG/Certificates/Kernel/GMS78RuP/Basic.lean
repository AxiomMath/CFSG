module

public import Certificates.Data.Kernel.GMS78RuP117

public section

namespace CFSG.KC.GMS.P117

open CFSG.KLie.CT CFSG.KC.Loop

theorem andB_eq (a b : Bool) : andB a b = (a && b) := by cases a <;> rfl

theorem orB_eq (a b : Bool) : orB a b = (a || b) := by cases a <;> rfl

theorem notB_eq (a : Bool) : notB a = !a := by cases a <;> rfl

theorem andB_iff {a b : Bool} : andB a b = true ↔ a = true ∧ b = true := by
  cases a <;> cases b <;> simp [andB]

theorem notB_iff {a : Bool} : notB a = true ↔ a = false := by
  cases a <;> simp [notB]

theorem strictN_eq (y : Nat) (k : Nat → Nat) : strictN y k = k y := by cases y <;> rfl

theorem beq_eq (a b : Nat) : Nat.beq a b = (a == b) := rfl

theorem blt_eq (a b : Nat) : Nat.blt a b = decide (a < b) := by
  cases h : Nat.blt a b
  · rw [← Bool.not_eq_true, Nat.blt_eq] at h; simp [h]
  · rw [Nat.blt_eq] at h; simp [h]

theorem ble_eq (a b : Nat) : Nat.ble a b = decide (a ≤ b) := by
  cases h : Nat.ble a b
  · rw [← Bool.not_eq_true, Nat.ble_eq] at h; simp [h]
  · rw [Nat.ble_eq] at h; simp [h]

theorem neAllL_eq {α : Type} (p : α → Bool) : ∀ l : List α, neAllL p l = l.all p
  | [] => rfl
  | a :: l => by
    change andB (p a) (neAllL p l) = _
    rw [andB_eq, neAllL_eq p l, List.all_cons]

theorem czListEq_iff : ∀ {a b : List Nat}, czListEq a b = true ↔ a = b
  | [], [] => ⟨fun _ => rfl, fun _ => rfl⟩
  | [], _ :: _ => ⟨fun h => Bool.noConfusion h, fun h => nomatch h⟩
  | _ :: _, [] => ⟨fun h => Bool.noConfusion h, fun h => nomatch h⟩
  | x :: a, y :: b => by
    change andB (Nat.beq x y) (czListEq a b) = true ↔ _
    rw [andB_eq, Bool.and_eq_true, czListEq_iff, List.cons.injEq, beq_eq, beq_iff_eq]

theorem czAny_eq (p : Nat → Bool) : ∀ l : List Nat, czAny p l = l.any p
  | [] => rfl
  | x :: l => by
    change orB (p x) (czAny p l) = _
    rw [orB_eq, czAny_eq p l, List.any_cons]

theorem pMap_eq (f : Nat → Nat) : ∀ L : List Nat, pMap f L = L.map f
  | [] => rfl
  | x :: L => by
    change List.cons (f x) (pMap f L) = _
    rw [pMap_eq f L, List.map_cons]

theorem pFilt_eq (f : Nat → Bool) : ∀ L : List Nat, pFilt f L = L.filter f
  | [] => rfl
  | x :: L => by
    change Bool.rec (motive := fun _ => List Nat) (pFilt f L) (List.cons x (pFilt f L)) (f x) = _
    rw [pFilt_eq f L, List.filter_cons]
    cases f x <;> rfl

theorem pCount_eq (f : Nat → Bool) : ∀ L : List Nat, pCount f L = L.countP f
  | [] => rfl
  | x :: L => by
    change strictN (pCount f L)
      (fun a => Bool.rec (motive := fun _ => Nat) a (Nat.succ a) (f x)) = _
    rw [strictN_eq, pCount_eq f L, List.countP_cons]
    cases f x <;> rfl

private theorem sFilter_aux (p : Nat → Bool) : ∀ (n : Nat) (acc : List Nat),
    Nat.rec (motive := fun _ => List Nat → List Nat) (fun acc => acc)
      (fun i ih acc => ih (Bool.rec (motive := fun _ => List Nat) acc (List.cons i acc) (p i)))
      n acc = (List.range n).filter p ++ acc
  | 0, acc => by simp
  | n + 1, acc => by
    change Nat.rec (motive := fun _ => List Nat → List Nat) (fun acc => acc)
      (fun i ih acc => ih (Bool.rec (motive := fun _ => List Nat) acc (List.cons i acc) (p i))) n
      (Bool.rec (motive := fun _ => List Nat) acc (List.cons n acc) (p n)) = _
    rw [sFilter_aux p n, List.range_succ, List.filter_append, List.append_assoc]
    cases h : p n <;> simp [h]

theorem sFilter_eq (n : Nat) (p : Nat → Bool) : sFilter n p = (List.range n).filter p :=
  (sFilter_aux p n []).trans (List.append_nil _)

end CFSG.KC.GMS.P117

end
