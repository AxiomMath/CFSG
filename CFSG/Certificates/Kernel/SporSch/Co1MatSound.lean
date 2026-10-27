module

public import CFSG.Certificates.Kernel.SporSch.Co1MatLemmas

public section

namespace CFSG.KS.SporSch.M24

open CFSG.Sporadic.Co1Schreier.Native CFSG.KS.Raw

theorem mulEqK_sound {X Y Z : Nat} (h : mulEqK X Y Z = true) :
    mul (unpack 24 24 X) (unpack 24 24 Y) = unpack 24 24 Z := by
  rw [← Nat.eq_of_beq_eq_true h, MatL.unpack_mulK]

theorem invOKK_sound {X Y : Nat} (h : invOKK X Y = true) :
    mul (unpack 24 24 X) (unpack 24 24 Y) = one () ∧ inv (unpack 24 24 X) = unpack 24 24 Y :=
  MatL.invOK_of h

namespace MatS

theorem bAnd_split {a b : Bool} (h : Bool.rec (motive := fun _ => Bool) false b a = true) :
    a = true ∧ b = true := by
  cases a <;> simp_all

theorem shiftRight_one_div (c : Nat) : Nat.shiftRight c 1 = c / 2 :=
  (Nat.shiftRight_eq_div_pow c 1).trans (by norm_num)

theorem posK_spec {w : List Nat} (h : posK w = true) : ∀ j ∈ w, j = 1 ∨ j = 2 := by
  induction w with
  | nil => simp
  | cons j w ih =>
    have e : posK (j :: w) =
        bAnd(bIf(Nat.beq j (nat_lit 1), true, Nat.beq j (nat_lit 2)), posK w) := rfl
    have eo : ∀ c d : Bool, Bool.rec (motive := fun _ => Bool) d true c = (c || d) := by
      intro c d
      cases c <;> rfl
    rw [e, MatL.bAnd_eq, eo] at h
    simp only [Bool.and_eq_true, Bool.or_eq_true, Nat.beq_eq] at h
    intro j' hj'
    rcases List.mem_cons.1 hj' with rfl | hj'
    · exact h.1
    · exact ih h.2 j' hj'

theorem wordPK_eq (A B : Nat) (w : List Nat) :
    wordPK A B w = w.foldl (fun acc j => mulK acc (nIf(Nat.beq j (nat_lit 1), A, B))) idM := by
  unfold wordPK
  generalize idM = a
  induction w generalizing a with
  | nil => rfl
  | cons j w ih => exact (MatL.strictN_eq _ _).trans (ih _)

end MatS

theorem wordEqK_sound {A B R : Nat} {w : List Nat} (h : wordEqK A B w R = true) (is : List Rows) :
    word [unpack 24 24 A, unpack 24 24 B] is (w.map Int.ofNat) = unpack 24 24 R := by
  obtain ⟨hp, hR⟩ := MatS.bAnd_split h
  obtain rfl := Nat.eq_of_beq_eq_true hR
  have hpos := MatS.posK_spec hp
  unfold word
  rw [List.foldl_map, ← MatL.unpack_idM, MatS.wordPK_eq]
  clear h hp hR
  generalize idM = a
  induction w generalizing a with
  | nil => rfl
  | cons j w ih =>
    rw [List.foldl_cons, List.foldl_cons]
    have hj : letter [unpack 24 24 A, unpack 24 24 B] is (Int.ofNat j) =
        unpack 24 24 (nIf(Nat.beq j (nat_lit 1), A, B)) := by
      rcases hpos j (by simp) with rfl | rfl <;> simp [letter, MatL.nIf_eq]
    rw [hj, ← MatL.unpack_mulK]
    exact ih (fun j' hj' => hpos j' (List.mem_cons_of_mem j hj')) _

namespace MatS

theorem lettersK_spec {k : Nat} {w : List Nat} (h : lettersK k w = true) :
    ∀ c ∈ w, 2 ≤ c ∧ c / 2 - 1 < k := by
  induction w with
  | nil => simp
  | cons c w ih =>
    have e : lettersK k (c :: w) = bAnd(Nat.ble (nat_lit 2) c,
        bAnd(Nat.blt (Nat.sub (Nat.shiftRight c (nat_lit 1)) (nat_lit 1)) k, lettersK k w)) := rfl
    rw [e] at h
    simp only [MatL.bAnd_eq, Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq, shiftRight_one_div,
      Nat.sub_eq] at h
    intro c' hc'
    rcases List.mem_cons.1 hc' with rfl | hc'
    · exact ⟨h.1, h.2.1⟩
    · exact ih h.2.2 c' hc'

theorem letterK_parity (M MI : Nat → Nat) (c : Nat) :
    letterK M MI c = if c % 2 = 0 then M (c / 2 - 1) else MI (c / 2 - 1) := by
  have h1 : Nat.land c 1 = c % 2 := Nat.and_one_is_mod c
  unfold letterK
  rw [MatL.nIf_eq, h1, shiftRight_one_div]
  simp only [Nat.beq_eq, Nat.sub_eq]

theorem letterS_eq {M MI : Nat → Nat} {k c : Nat} (h2 : 2 ≤ c) (hk : c / 2 - 1 < k) :
    letter (MatL.rowsL M k) (MatL.rowsL MI k) (decLetter c) = unpack 24 24 (letterK M MI c) := by
  rw [letterK_parity]
  unfold letter decLetter
  by_cases hc : c % 2 = 0
  · have hpos : (0 : Int) < ((c / 2 : Nat) : Int) := by omega
    simp only [hc, ↓reduceIte, hpos, Int.toNat_natCast]
    simp [MatL.rowsL, List.getD_eq_getElem?_getD, hk]
  · have hneg : ¬ (0 : Int) < -((c / 2 : Nat) : Int) := by omega
    simp only [hc, ↓reduceIte, hneg, neg_neg, Int.toNat_natCast]
    simp [MatL.rowsL, List.getD_eq_getElem?_getD, hk]

theorem wordSK_eq (M MI : Nat → Nat) (w : List Nat) :
    wordSK M MI w = w.foldl (fun acc c => mulK acc (letterK M MI c)) idM := by
  unfold wordSK
  generalize idM = a
  induction w generalizing a with
  | nil => rfl
  | cons c w ih => exact (MatL.strictN_eq _ _).trans (ih _)

theorem wordS_unpack {M MI : Nat → Nat} {k : Nat} (w : List Nat) (a : Nat)
    (hl : ∀ c ∈ w, 2 ≤ c ∧ c / 2 - 1 < k) :
    w.foldl (fun A c => mul A (letter (MatL.rowsL M k) (MatL.rowsL MI k) (decLetter c)))
        (unpack 24 24 a) =
      unpack 24 24 (w.foldl (fun acc c => mulK acc (letterK M MI c)) a) := by
  induction w generalizing a with
  | nil => rfl
  | cons c w ih =>
    rw [List.foldl_cons, List.foldl_cons, letterS_eq (hl c (by simp)).1 (hl c (by simp)).2,
      ← MatL.unpack_mulK]
    exact ih _ (fun c' hc' => hl c' (List.mem_cons_of_mem c hc'))

theorem word_eq_wordSK {M MI : Nat → Nat} {k : Nat} {w : List Nat} (h : lettersK k w = true) :
    word (MatL.rowsL M k) (MatL.rowsL MI k) (decWord w) = unpack 24 24 (wordSK M MI w) := by
  unfold word decWord
  rw [List.foldl_map, ← MatL.unpack_idM, wordSK_eq]
  exact wordS_unpack w idM (lettersK_spec h)

theorem lenLL_eq (ws : List (List Nat)) : lenLL ws = ws.length := by
  induction ws with
  | nil => rfl
  | cons w ws ih => exact congrArg Nat.succ ih

end MatS

theorem dagK_sound {M MI : Nat → Nat} {nb N : Nat} {ws : List (List Nat)} {base : List Rows}
    (hb : base = (List.range nb).map fun i => unpack 24 24 (M i))
    (h : dagK M MI nb N ws = true) :
    dag base (ws.map decWord) = ((List.range N).map fun i => unpack 24 24 (M i),
      (List.range N).map fun i => unpack 24 24 (MI i), true) := by
  obtain ⟨hN, h⟩ := MatS.bAnd_split h
  obtain ⟨hall, hrec⟩ := MatS.bAnd_split h
  have hN' : nb + ws.length = N := by
    rw [← MatS.lenLL_eq]
    exact Nat.eq_of_beq_eq_true hN
  exact MatL.dag_sound (M := M) (MI := MI) lettersK (wordSK M MI) decWord hb
    (fun _ _ hw => MatS.word_eq_wordSK hw) hN' (MatL.allN_iff.1 hall) hrec

end CFSG.KS.SporSch.M24

end
