module

public import Certificates.Data.Kernel.ThCent.List
public import CFSG.Certificates.Kernel.F3152.SortSound

public section

namespace CFSG.KC.ThCent

open CFSG.KC.Th CFSG.KC.Th.BigS

@[expose] noncomputable def distRow (x : Nat) (t : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun y _ ih' => andB (notB (Nat.beq x y)) ih') t

theorem distinctL_cons (x : Nat) (t : List Nat) :
    distinctL (x :: t) = andB (distRow x t) (distinctL t) := rfl

theorem distRow_cons (x y : Nat) (t : List Nat) :
    distRow x (y :: t) = andB (notB (Nat.beq x y)) (distRow x t) := rfl

theorem distRow_of_not_mem (x : Nat) : ∀ t : List Nat, x ∉ t → distRow x t = true
  | [], _ => rfl
  | y :: t, h => by
    have hb : Nat.beq x y = false := by
      cases hb : Nat.beq x y
      · rfl
      · exact absurd (List.mem_cons.2 (Or.inl (Nat.eq_of_beq_eq_true hb))) h
    rw [distRow_cons, hb, distRow_of_not_mem x t (fun hm => h (List.mem_cons_of_mem _ hm))]
    all_goals rfl

theorem distinctL_of_nodup : ∀ l : List Nat, l.Nodup → distinctL l = true
  | [], _ => rfl
  | x :: t, h => by
    obtain ⟨hx, ht⟩ := List.nodup_cons.1 h
    rw [distinctL_cons, distRow_of_not_mem x t hx, distinctL_of_nodup t ht]
    all_goals rfl

end CFSG.KC.ThCent

end
