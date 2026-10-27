module

public import CFSG.Certificates.Kernel.Spor.PK.MiscBase
public import CFSG.Certificates.Kernel.Spor.PK.Enc
public import CFSG.Certificates.Kernel.Spor.PK.BFS
public import Certificates.Data.Kernel.Misc.T46
import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Data.Fintype.EquivFin

public section

namespace CFSG.KS.PK

open CFSG.KC.Ord CFSG.KC.LQT.P CFSG.KC.Misc CFSG.KC.Misc.O73 CFSG.KC.Misc.T46

theorem at'_eq (w P i : Nat) : at' w P i = fd w P i := by
  unfold at' fd
  exact fld_eq P (w * i) w

private theorem sl1 (k : Nat) : Nat.shiftLeft 1 k = 2 ^ k := Nat.one_shiftLeft k

private theorem testBit_orPow (f : Nat → Nat) (n j : Nat) :
    (Nat.rec (motive := fun _ => Nat) 0
      (fun i acc => Nat.lor acc (Nat.shiftLeft 1 (f i))) n).testBit j = true ↔
      ∃ i < n, f i = j := by
  induction n with
  | zero => simp
  | succ n ih =>
    show (Nat.lor (Nat.rec (motive := fun _ => Nat) 0
      (fun i acc => Nat.lor acc (Nat.shiftLeft 1 (f i))) n) (Nat.shiftLeft 1 (f n))).testBit j
        = true ↔ _
    rw [Nat.lor_eq, Nat.testBit_or, Bool.or_eq_true, ih, sl1, Nat.testBit_two_pow,
      decide_eq_true_iff]
    constructor
    · rintro (⟨i, hi, h⟩ | h)
      · exact ⟨i, Nat.lt_succ_of_lt hi, h⟩
      · exact ⟨n, Nat.lt_succ_self n, h⟩
    · rintro ⟨i, hi, h⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
      · exact Or.inl ⟨i, hi, h⟩
      · exact Or.inr h

private theorem orPow_eq_iff (f : Nat → Nat) (n : Nat) :
    Nat.rec (motive := fun _ => Nat) 0 (fun i acc => Nat.lor acc (Nat.shiftLeft 1 (f i))) n
        = Nat.sub (Nat.shiftLeft 1 n) 1 ↔ ∀ j, (∃ i < n, f i = j) ↔ j < n := by
  have e1 : Nat.sub (Nat.shiftLeft 1 n) 1 = 2 ^ n - 1 := by rw [sl1]; rfl
  rw [e1]
  constructor
  · intro h j
    rw [← testBit_orPow, h, Nat.testBit_two_pow_sub_one, decide_eq_true_iff]
  · intro h
    apply Nat.eq_of_testBit_eq
    intro j
    rw [Bool.eq_iff_iff, testBit_orPow, Nat.testBit_two_pow_sub_one, decide_eq_true_iff]
    exact h j

private theorem isPermN_of_surj {n : Nat} {f : Nat → Nat} (h1 : ∀ i < n, f i < n)
    (h2 : ∀ j < n, ∃ i < n, f i = j) : IsPermN n f := by
  refine ⟨h1, ?_⟩
  let g : Fin n → Fin n := fun x => ⟨f x.val, h1 x.val x.isLt⟩
  have hsurj : Function.Surjective g := by
    intro y
    obtain ⟨i, hi, hfi⟩ := h2 y.val y.isLt
    exact ⟨⟨i, hi⟩, Fin.ext hfi⟩
  have hinj : Function.Injective g := Finite.injective_iff_surjective.2 hsurj
  intro x hx y hy hxy
  exact congrArg Fin.val (hinj (a₁ := ⟨x, hx⟩) (a₂ := ⟨y, hy⟩) (Fin.ext hxy))

theorem permK_iff {n w P : Nat} :
    permK n w P = true ↔ P < 2 ^ (w * n) ∧ IsPermN n (fd w P) := by
  unfold CFSG.KC.Misc.O73.permK
  simp only [letB_eq, andB_eq, Bool.and_eq_true, allN_lqt_iff, Nat.blt_eq, Nat.beq_eq, at'_eq]
  rw [orPow_eq_iff]
  simp only [sl1, Nat.mul_eq]
  constructor
  · rintro ⟨hP, h1, h2⟩
    exact ⟨hP, isPermN_of_surj h1 fun j hj => (h2 j).2 hj⟩
  · rintro ⟨hP, hperm⟩
    refine ⟨hP, hperm.1, fun j => ⟨?_, fun hj => hperm.surj hj⟩⟩
    rintro ⟨i, hi, rfl⟩
    exact hperm.1 i hi

private theorem rec_enc {w : Nat} {g : Nat → Nat} {n : Nat} (hg : ∀ i < n, g i < 2 ^ w) :
    Nat.rec (motive := fun _ => Nat) 0
      (fun x acc => Nat.lor acc (Nat.shiftLeft (g x) (Nat.mul w x))) n = enc w g n := by
  induction n with
  | zero => rfl
  | succ k ih =>
    have h1 := ih (fun i hi => hg i (Nat.lt_succ_of_lt hi))
    show Nat.lor (Nat.rec (motive := fun _ => Nat) 0
      (fun x acc => Nat.lor acc (Nat.shiftLeft (g x) (Nat.mul w x))) k)
        (Nat.shiftLeft (g k) (Nat.mul w k)) = _
    rw [h1, enc_succ]
    exact lor_shiftLeft_eq_add (enc_lt (fun i hi => hg i (Nat.lt_succ_of_lt hi)))

theorem compP_eq (n w t u : Nat) : compP n w t u = enc w (fun x => fd w t (fd w u x)) n := by
  unfold compP
  simp only [letN_eq]
  refine (rec_enc (g := fun x => at' w t (at' w u x))
    (fun i _ => by rw [at'_eq]; exact fd_lt _ _ _)).trans
    (enc_congr fun i _ => by rw [at'_eq, at'_eq])

theorem idP_eq {n w : Nat} (hw : n ≤ 2 ^ w) : idP n w = enc w (fun x => x) n := by
  unfold idP
  exact rec_enc (g := fun x => x) (fun i hi => Nat.lt_of_lt_of_le hi hw)

private theorem le693 : (693 : Nat) ≤ 2 ^ 10 := by decide

private theorem itr_lt (P k : Nat) : ∀ i < 693, itr (fd 10 P) k i < 2 ^ 10 := by
  intro i hi
  cases k with
  | zero => exact Nat.lt_of_lt_of_le hi le693
  | succ k => exact fd_lt _ _ _

theorem powP_eq (e P : Nat) : powP e P = enc 10 (itr (fd 10 P) e) 693 := by
  unfold powP
  simp only [letN_eq]
  induction e with
  | zero => exact idP_eq le693
  | succ k ih =>
    show compP 693 10 P (Nat.rec (motive := fun _ => Nat) (idP 693 10)
      (fun _ acc => compP 693 10 P acc) k) = _
    rw [ih, compP_eq]
    apply enc_congr
    intro x hx
    rw [fd_enc (fun i hi => itr_lt P k i hi) hx]
    rfl

@[expose] def wordGF (G : List Nat) (w : List Int) (x : Nat) : Nat :=
  w.foldr (fun z y => fd 10 (G.getD (z.natAbs - 1) 0) y) x

private theorem wordGF_lt (G : List Nat) (w : List Int) : ∀ i < 693, wordGF G w i < 2 ^ 10 := by
  intro i hi
  cases w with
  | nil => exact Nat.lt_of_lt_of_le hi le693
  | cons z w => exact fd_lt _ _ _

private theorem wordG_cons (G : List Nat) (z : Int) (w : List Int) :
    wordG G (z :: w) = compP 693 10 (wordM7.nthN G (Nat.sub (Int.natAbs z) 1)) (wordG G w) := rfl

theorem wordG_eq (G : List Nat) (w : List Int) : wordG G w = enc 10 (wordGF G w) 693 := by
  induction w with
  | nil => exact idP_eq le693
  | cons z w ih =>
    rw [wordG_cons, ih, compP_eq]
    apply enc_congr
    intro x hx
    rw [fd_enc (fun i hi => wordGF_lt G w i hi) hx, nthN_eq]
    rfl

private theorem wordXYF_lt (w : List Nat) (X Y : Nat) : ∀ i < 693,
    w.foldr (fun z y => fd 10 (if z = 1 then X else Y) y) i < 2 ^ 10 := by
  intro i hi
  cases w with
  | nil => exact Nat.lt_of_lt_of_le hi le693
  | cons z w => exact fd_lt _ _ _

private theorem wordXY_cons (X Y z : Nat) (w : List Nat) :
    wordXY X Y (z :: w) = compP 693 10 (if z = 1 then X else Y) (wordXY X Y w) := by
  show compP 693 10 (Bool.rec (motive := fun _ => Nat) Y X (Nat.beq z 1)) (wordXY X Y w) = _
  simp only [nIf_eq, Nat.beq_eq]

theorem wordXY_eq (X Y : Nat) (w : List Nat) :
    wordXY X Y w = enc 10 (fun x => w.foldr (fun z y => fd 10 (if z = 1 then X else Y) y) x) 693 := by
  induction w with
  | nil => exact idP_eq le693
  | cons z w ih =>
    rw [wordXY_cons, ih, compP_eq]
    apply enc_congr
    intro x hx
    rw [fd_enc (fun i hi => wordXYF_lt w X Y i hi) hx]
    rfl

@[expose] def wordPF (w : Nat) (Ps : List Nat) (wd : List Nat) (x : Nat) : Nat :=
  wd.foldr (fun c y => if c < Ps.length then fd w (Ps.getD c 0) y else y) x

private theorem wordPF_lt {n w : Nat} (Ps : List Nat)
    (hPs : ∀ c < Ps.length, ∀ x < n, fd w (Ps.getD c 0) x < n) (wd : List Nat) :
    ∀ x < n, wordPF w Ps wd x < n := by
  induction wd with
  | nil => intro x hx; exact hx
  | cons c wd ih =>
    intro x hx
    show (if c < Ps.length then fd w (Ps.getD c 0) (wordPF w Ps wd x) else wordPF w Ps wd x) < n
    by_cases hc : c < Ps.length
    · rw [if_pos hc]
      exact hPs c hc _ (ih x hx)
    · rw [if_neg hc]
      exact ih x hx

private theorem wordP_nil (n w : Nat) (Ps : List Nat) :
    CFSG.KC.Misc.O73.wordP n w Ps [] = idP n w := by
  unfold CFSG.KC.Misc.O73.wordP
  simp only [letN_eq]

private theorem wordP_cons (n w : Nat) (Ps : List Nat) (c : Nat) (wd : List Nat) :
    CFSG.KC.Misc.O73.wordP n w Ps (c :: wd) =
      compP n w (if c < Ps.length then Ps.getD c 0 else idP n w)
        (CFSG.KC.Misc.O73.wordP n w Ps wd) := by
  have h : CFSG.KC.Misc.O73.wordP n w Ps (c :: wd) =
      compP n w (Bool.rec (motive := fun _ => Nat) (idP n w) (wordM7.nthN Ps c)
        (Nat.blt c (lenN Ps))) (CFSG.KC.Misc.O73.wordP n w Ps wd) := by
    unfold CFSG.KC.Misc.O73.wordP
    simp only [letN_eq]
  rw [h]
  simp only [nIf_eq, Nat.blt_eq, lenN_misc_eq, nthN_eq]

theorem wordP_eq_of_maps {n w : Nat} (hw : n ≤ 2 ^ w) (Ps : List Nat)
    (hPs : ∀ c < Ps.length, ∀ x < n, fd w (Ps.getD c 0) x < n) (wd : List Nat) :
    CFSG.KC.Misc.O73.wordP n w Ps wd = enc w (wordPF w Ps wd) n := by
  induction wd with
  | nil => rw [wordP_nil]; exact idP_eq hw
  | cons c wd ih =>
    have hlt := wordPF_lt Ps hPs wd
    rw [wordP_cons, ih, compP_eq]
    apply enc_congr
    intro x hx
    rw [fd_enc (fun i hi => Nat.lt_of_lt_of_le (hlt i hi) hw) hx]
    show _ = (if c < Ps.length then fd w (Ps.getD c 0) (wordPF w Ps wd x) else wordPF w Ps wd x)
    by_cases hc : c < Ps.length
    · rw [if_pos hc, if_pos hc]
    · rw [if_neg hc, if_neg hc, idP_eq hw,
        fd_enc (fun i hi => Nat.lt_of_lt_of_le hi hw) (hlt x hx)]

end CFSG.KS.PK

end
