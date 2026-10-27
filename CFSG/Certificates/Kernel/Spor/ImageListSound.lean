module

public import CFSG.Certificates.Kernel.Spor.DistinctSound

public section

namespace CFSG.KS.Co2Shape

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.Monster.B.Co2.Native

theorem lenL_eq {α : Type} : ∀ l : List α, lenL l = l.length
  | [] => rfl
  | _ :: l => congrArg Nat.succ (lenL_eq l)

theorem allL_eq {α : Type} (f : α → Bool) : ∀ l : List α, allL f l = l.all f
  | [] => rfl
  | x :: l => by
    change Bool.rec (motive := fun _ => Bool) false (allL f l) (f x) = _
    rw [List.all_cons, allL_eq f l]
    cases f x <;> rfl

theorem eqNL_iff : ∀ a b : List Nat, eqNL a b = true ↔ a = b
  | [], [] => iff_of_true rfl rfl
  | [], _ :: _ => iff_of_false Bool.false_ne_true (List.cons_ne_nil _ _).symm
  | _ :: _, [] => iff_of_false Bool.false_ne_true (List.cons_ne_nil _ _)
  | x :: xs, y :: ys => by
    change Bool.rec (motive := fun _ => Bool) false (eqNL xs ys) (Nat.beq x y) = true ↔ _
    rw [bAnd_iff, eqNL_iff xs ys, Nat.beq_eq, List.cons.injEq]

theorem invCand_eq_foldl (n : Nat) (t : Array Nat) :
    invCand n t = (List.range n).foldl (fun r i => r.set! t[i]! i) (Array.replicate n 0) := by
  unfold invCand
  simp only [Id.run, Std.Legacy.Range.forIn_eq_forIn_range', List.forIn_pure_yield_eq_foldl,
    Std.Legacy.Range.size]
  simp only [Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, bind_pure, List.range_eq_range']
  rfl

theorem permBody_of {n : Nat} {l : List Nat} (hl : l.length = n) (hnd : l.Nodup)
    (hb : ∀ x ∈ l, x < n) : (l.length == n && isInvA n l.toArray (invCand n l.toArray)) = true := by
  have ht : ∀ i (hi : i < n), l.toArray[i]! = l[i]'(by omega) := by
    intro i hi
    rw [List.getElem!_toArray, getElem!_pos l i (by omega)]
  have htn : ∀ i < n, l.toArray[i]! < n := fun i hi => by
    rw [ht i hi]
    exact hb _ (List.getElem_mem _)
  have key : ∀ k ≤ n, ((List.range k).foldl (fun r i => r.set! l.toArray[i]! i)
      (Array.replicate n 0)).size = n ∧ ∀ i < k, ((List.range k).foldl
        (fun r i => r.set! l.toArray[i]! i) (Array.replicate n 0))[l.toArray[i]!]! = i := by
    intro k
    induction k with
    | zero => intro _; simp
    | succ k ih =>
      intro hk
      obtain ⟨hs, hi⟩ := ih (by omega)
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
      refine ⟨by rw [Array.size_set!, hs], fun i hik => ?_⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 hik with hlt | rfl
      · have hne : l.toArray[i]! ≠ l.toArray[k]! := by
          rw [ht i (by omega), ht k (by omega)]
          intro e
          have := (List.Nodup.getElem_inj_iff hnd).1 e
          omega
        rw [Array.getElem!_set!_ne _ _ _ _ (Ne.symm hne)]
        exact hi i hlt
      · rw [Array.getElem!_set!_self _ _ _ (by rw [hs]; exact htn i (by omega))]
  unfold isInvA allLt
  rw [Bool.and_eq_true, beq_iff_eq, invCand_eq_foldl]
  refine ⟨hl, ?_⟩
  obtain ⟨_, hk⟩ := key n le_rfl
  rw [Nat.all_eq_finRange_all, List.all_eq_true]
  rintro ⟨i, hi⟩ _
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
  exact ⟨htn i hi, hk i hi⟩

theorem permBody_of_permL {n : Nat} {l : List Nat} (h : permL n l = true) :
    (l.length == n && isInvA n l.toArray (invCand n l.toArray)) = true := by
  obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 h
  obtain ⟨hnd, hb⟩ := distinctL_sound h2
  exact permBody_of (by rw [← lenL_eq]; exact Nat.eq_of_beq_eq_true h1) hnd
    (fun x hx => (hb x hx).1)

end CFSG.KS.Co2Shape

end
