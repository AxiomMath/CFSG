module

public import Certificates.Data.Kernel.Misc.HNHeis
public import CFSG.Certificates.Kernel.SporSch.LyMatSound
public import CFSG.Sporadic.HNSchreier.SeedsCheckInputs
import CFSG.Certificates.Kernel.SporSch.LyMatLemmas
import CFSG.Certificates.Kernel.Spor.OrdSound
public import CFSG.Sporadic.Schreier.LyCheckSeven

public section

namespace CFSG.KS.Misc.HNHeis

open CFSG.KC.Ord CFSG.KS.SporSch.LyM CFSG.KC.Misc.HNHeis CFSG.Sporadic.He.Native
open CFSG.Sporadic.HNSchreier.Native

local notation "U" X:max => unpackL 133 13 1729 X

variable (hc : constsH = true)
include hc

theorem mulH_eq {X Y : Nat} (hX : vldH X = true) (hY : vldH Y = true) :
    mulM 5 133 (U X) (U Y) = U (mulH X Y) ∧ vldH (mulH X Y) = true :=
  mulR_eq hc hX hY

theorem oneH_eq : idM 133 = U ONEH ∧ vldH ONEH = true := idM_eq hc

theorem beqH_eq {X Y : Nat} (hX : vldH X = true) (hY : vldH Y = true) :
    (U X == U Y) = Nat.beq X Y := beq_eq hc hX hY

omit hc in
theorem strictN_val (y : Nat) (k : Nat → Nat) : CFSG.KC.Loop.strictN y k = k y := by
  cases y <;> rfl

omit hc in
theorem letL_val (y : Nat) (k : Nat → List Nat) : letL y k = k y := by
  cases y <;> rfl

@[expose] def RegRep (A : Array (Array (Array Nat))) (R : List Nat) : Prop :=
  A.size = R.length ∧ ∀ i, A.getD i (idM 133) = U (regH R i) ∧ vldH (regH R i) = true

theorem wordFrom_eq {A : Array (Array (Array Nat))} {R : List Nat} (hA : RegRep A R) :
    ∀ (w : List Nat) (P : Nat), vldH P = true →
      w.foldl (fun M l => mulM 5 133 M (A.getD (l - 1) (idM 133))) (U P) = U (wordFromH R P w) ∧
        vldH (wordFromH R P w) = true := by
  intro w
  induction w with
  | nil =>
    intro P hP
    have e : wordFromH R P [] = P := rfl
    rw [List.foldl_nil, e]
    exact ⟨rfl, hP⟩
  | cons l w ih =>
    intro P hP
    obtain ⟨e, v⟩ := hA.2 (l - 1)
    obtain ⟨m1, m2⟩ := mulH_eq hc hP v
    have hw : wordFromH R P (l :: w) = wordFromH R (mulH P (regH R (l - 1))) w := by
      change CFSG.KC.Loop.strictN (mulH P (regH R (Nat.sub l 1)))
        (fun P => wordFromH R P w) = _
      rw [strictN_val]
      rfl
    rw [List.foldl_cons, e, m1, hw]
    exact ih _ m2

theorem wordM_eq {A : Array (Array (Array Nat))} {R : List Nat} (hA : RegRep A R) (w : List Nat) :
    wordM (fun l => A.getD (l - 1) (idM 133)) w = U (wordH R w) ∧ vldH (wordH R w) = true := by
  have h := wordFrom_eq hc hA w ONEH (oneH_eq hc).2
  rw [← (oneH_eq hc).1] at h
  exact h

theorem push_rep {A : Array (Array (Array Nat))} {R : List Nat} (hA : RegRep A R) {x : Nat}
    (hx : vldH x = true) : RegRep (A.push (U x)) (R ++ [x]) := by
  refine ⟨by rw [Array.size_push, List.length_append, hA.1]; rfl, fun i => ?_⟩
  have hs := hA.1
  rcases Nat.lt_trichotomy i A.size with h | h | h
  · have e1 : (A.push (U x)).getD i (idM 133) = A.getD i (idM 133) := by
      rw [Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?, Array.getElem?_push_lt h,
        Array.getElem?_eq_getElem h]
    have e2 : regH (R ++ [x]) i = regH R i := by
      unfold regH
      rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
        List.getElem?_append_left (by omega)]
    rw [e1, e2]
    exact hA.2 i
  · subst h
    have e1 : (A.push (U x)).getD A.size (idM 133) = U x := by
      rw [Array.getD_eq_getD_getElem?, Array.getElem?_push_size, Option.getD_some]
    have e2 : regH (R ++ [x]) A.size = x := by
      unfold regH
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega), hs, Nat.sub_self]
      simp
    rw [e1, e2]
    exact ⟨rfl, hx⟩
  · have e1 : (A.push (U x)).getD i (idM 133) = idM 133 := by
      rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (by rw [Array.size_push]; omega),
        Option.getD_none]
    have e2 : regH (R ++ [x]) i = ONEH := by
      unfold regH
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp; omega), Option.getD_none]
    rw [e1, e2]
    exact oneH_eq hc

theorem pair_rep {a b : Array (Array Nat)} {X Y : Nat} (ha : a = U X) (hb : b = U Y)
    (hX : vldH X = true) (hY : vldH Y = true) : RegRep #[a, b] [X, Y] := by
  refine ⟨rfl, fun i => ?_⟩
  match i with
  | 0 => exact ⟨ha, hX⟩
  | 1 => exact ⟨hb, hY⟩
  | i + 2 =>
    have e1 : (#[a, b] : Array (Array (Array Nat))).getD (i + 2) (idM 133) = idM 133 := by
      rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (by simp), Option.getD_none]
    have e2 : regH [X, Y] (i + 2) = ONEH := by
      unfold regH
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp), Option.getD_none]
    rw [e1, e2]
    exact oneH_eq hc

theorem slp_rep : ∀ (prog : List (List Nat)) (A : Array (Array (Array Nat))) (R : List Nat),
    RegRep A R →
    RegRep (prog.foldl (fun A w => A.push (wordM (fun l => A.getD (l - 1) (idM 133)) w)) A)
      (slpFromH R prog) := by
  intro prog
  induction prog with
  | nil => intro A R h; exact h
  | cons w prog ih =>
    intro A R h
    obtain ⟨e, v⟩ := wordM_eq hc h w
    have hs : slpFromH R (w :: prog) = slpFromH (R ++ [wordH R w]) prog := by
      change letL (wordH R w) (fun x => slpFromH (R ++ [x]) prog) = _
      rw [letL_val]
    rw [List.foldl_cons, e, hs]
    exact ih _ _ (push_rep hc h v)

theorem notIdM_eq {X : Nat} (hX : vldH X = true) (h : Nat.beq X ONEH = false) :
    notIdM 133 (U X) = true := by
  obtain ⟨hid, v1⟩ := oneH_eq hc
  have cX := CFSG.KS.Ord.validM_canon hc hX
  have c1 := CFSG.KS.Ord.validM_canon hc v1
  unfold notIdM
  by_contra hb
  simp only [Bool.not_eq_true', Bool.not_eq_false] at hb
  rw [Nat.all_eq_finRange_all, List.all_eq_true] at hb
  have hall : ∀ i < 133, ∀ j < 133, ((U X)[i]!)[j]! % 5 = if i = j then 1 else 0 := by
    intro i hi j hj
    have h1 := hb ⟨i, hi⟩ (List.mem_finRange _)
    simp only at h1
    rw [Nat.all_eq_finRange_all, List.all_eq_true] at h1
    have h2 := h1 ⟨j, hj⟩ (List.mem_finRange _)
    simpa using h2
  have hXO : X = ONEH := by
    refine canon_ext cX c1 fun i hi j hj => ?_
    have a1 := hall i hi j hj
    have b1 := canon_ent cX hi hj
    rw [unpackL_get hi hj, Nat.mod_eq_of_lt (by simpa using b1)] at a1
    have a2 : ((U ONEH)[i]!)[j]! = if i = j then 1 else 0 := by
      rw [← hid]
      unfold idM
      rw [ofFn_get! _ hi, ofFn_get! _ hj]
    rw [unpackL_get hi hj] at a2
    simp only [Nat.reduceMul] at a1 a2 ⊢
    rw [a1, a2]
  rw [hXO, Nat.beq_refl] at h
  exact Bool.noConfusion h

end CFSG.KS.Misc.HNHeis

end
