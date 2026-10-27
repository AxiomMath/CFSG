module

public import Certificates.Data.Kernel.Spor.Co2Shape
public import CFSG.Sporadic.Co2Cert.CheckInputs
import CFSG.Certificates.Kernel.Spor.DistinctSound

public section

namespace CFSG.KS.Co2SShape

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Co2Shape CFSG.Sporadic.Co2Cert CFSG.Monster.B.Mathieu
  CFSG.Monster.B.Co2.Native

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

theorem lettersK_eq (j : Nat) : ∀ w : List Int, lettersK j w = lettersOK j w
  | [] => rfl
  | z :: w => by
    have e : lettersK j (z :: w) = Bool.rec (motive := fun _ => Bool) false
        (Bool.rec (motive := fun _ => Bool) false (lettersK j w)
          (Nat.ble (Nat.shiftRight (CFSG.KS.Mathieu.icode z) 1) j))
        (Nat.blt 0 (CFSG.KS.Mathieu.icode z)) :=
      strictB_eq (CFSG.KS.Mathieu.icode z) (fun c => Bool.rec (motive := fun _ => Bool) false
        (Bool.rec (motive := fun _ => Bool) false (lettersK j w) (Nat.ble (Nat.shiftRight c 1) j))
        (Nat.blt 0 c))
    have key : (Nat.blt 0 (CFSG.KS.Mathieu.icode z) &&
        Nat.ble (Nat.shiftRight (CFSG.KS.Mathieu.icode z) 1) j) =
        (z != 0 && decide (z.natAbs ≤ j)) := by
      have hs : Nat.shiftRight (CFSG.KS.Mathieu.icode z) 1 = CFSG.KS.Mathieu.icode z / 2 :=
        Nat.shiftRight_eq_div_pow _ _
      rw [hs]
      apply Bool.eq_iff_iff.mpr
      simp only [Bool.and_eq_true, Nat.blt_eq, Nat.ble_eq, bne_iff_ne, ne_eq, decide_eq_true_eq]
      cases z with
      | ofNat k =>
        change (0 < k + k ∧ (k + k) / 2 ≤ j) ↔ (¬Int.ofNat k = 0 ∧ k ≤ j)
        rw [Int.ofNat_eq_natCast, Int.natCast_eq_zero]
        omega
      | negSucc k =>
        change (0 < k + 1 + (k + 1) + 1 ∧ (k + 1 + (k + 1) + 1) / 2 ≤ j) ↔
          (¬Int.negSucc k = 0 ∧ k + 1 ≤ j)
        have h2 : ¬Int.negSucc k = 0 := Int.negSucc_ne_zero k
        simp only [h2, not_false_eq_true, true_and]
        omega
    rw [e, lettersOK, List.all_cons, ← lettersOK, ← lettersK_eq j w, ← key]
    cases Nat.blt 0 (CFSG.KS.Mathieu.icode z) <;>
      cases Nat.ble (Nat.shiftRight (CFSG.KS.Mathieu.icode z) 1) j <;> rfl

theorem wordsL_spec (k : Nat) : ∀ (D : List (List Int)) (j : Nat), wordsL k D j = true →
    ∀ t < D.length, lettersOK (j + t + k) (D.getD t []) = true
  | [], _, _, t, ht => absurd ht (Nat.not_lt_zero t)
  | w :: D, j, h, t, ht => by
    have h' : Bool.rec (motive := fun _ => Bool) false (wordsL k D (Nat.succ j))
        (lettersK (Nat.add j k) w) = true := h
    obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 h'
    cases t with
    | zero =>
      rw [lettersK_eq] at h1
      simpa using h1
    | succ t =>
      have := wordsL_spec k D (j + 1) h2 t (by simpa using ht)
      rw [List.getD_cons_succ]
      rwa [show j + (t + 1) + k = j + 1 + t + k by omega]

theorem invCand_eq_foldl (n : Nat) (t : Array Nat) :
    invCand n t = (List.range n).foldl (fun r i => r.set! t[i]! i) (Array.replicate n 0) := by
  unfold invCand
  simp only [Id.run, Std.Legacy.Range.forIn_eq_forIn_range', List.forIn_pure_yield_eq_foldl,
    Std.Legacy.Range.size]
  simp only [Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, bind_pure, List.range_eq_range']
  rfl

theorem isPermList_of {n : Nat} {l : List Nat} (hl : l.length = n) (hnd : l.Nodup)
    (hb : ∀ x ∈ l, x < n) : isPermList n l = true := by
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
  unfold isPermList isInvA allLt
  rw [Bool.and_eq_true, beq_iff_eq, invCand_eq_foldl]
  refine ⟨hl, ?_⟩
  obtain ⟨_, hk⟩ := key n le_rfl
  rw [Nat.all_eq_finRange_all, List.all_eq_true]
  rintro ⟨i, hi⟩ _
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
  exact ⟨htn i hi, hk i hi⟩

theorem isPermList_of_permL {n : Nat} {l : List Nat} (h : permL n l = true) :
    isPermList n l = true := by
  obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 h
  obtain ⟨hnd, hb⟩ := distinctL_sound h2
  exact isPermList_of (by rw [← lenL_eq]; exact Nat.eq_of_beq_eq_true h1) hnd
    (fun x hx => (hb x hx).1)

theorem chainK_sound {c : CFSG.Monster.B.Mathieu.ChainRecord} {n k r : Nat} {base : List Nat}
    (h : CFSG.KS.Co2Shape.chainK c n k r base = true) :
    CFSG.Sporadic.Co2Cert.chainShapeOK c n k r base = true := by
  unfold chainK at h
  simp only [bAnd_iff, Nat.beq_eq, lenL_eq, allL_eq, List.all_eq_true, eqNL_iff] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
  unfold chainShapeOK
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, and_assoc]
  refine ⟨h1, h2, h3, h4, fun x hx => isPermList_of_permL (h5 x hx),
    fun x hx => isPermList_of_permL (h6 x hx), h7, fun j hj => ?_⟩
  have := wordsL_spec k c.derivations 0 h8 j (by rw [h4]; exact List.mem_range.1 hj)
  rwa [Nat.zero_add] at this

end CFSG.KS.Co2SShape
