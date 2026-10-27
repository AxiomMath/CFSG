module

public import Certificates.Data.Kernel.WordRelK

public section

namespace CFSG.KC.WordRelK

open CFSG.Monster.B CFSG.Monster.B.TwoA.Sp8 CFSG.Monster.B.TwoA.Sp8.WordRel

theorem allBelow_true {n : Nat} {f : Nat → Bool} (h : allBelow n f = true) :
    ∀ k < n, f k = true := by
  induction n with
  | zero => intro k hk; omega
  | succ n ih =>
    have h' : (allBelow n f && f n) = true := h
    rw [Bool.and_eq_true] at h'
    intro k hk
    rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk | rfl
    · exact ih h'.1 k hk
    · exact h'.2

theorem allL_true {p : XLetter → Bool} {w : List XLetter} (h : allL p w = true) :
    ∀ ℓ ∈ w, p ℓ = true := by
  induction w with
  | nil => intro ℓ hℓ; simp at hℓ
  | cons a w ih =>
    have h' : (p a && allL p w) = true := h
    rw [Bool.and_eq_true] at h'
    intro ℓ hℓ
    rcases List.mem_cons.1 hℓ with rfl | hℓ
    · exact h'.1
    · exact ih h'.2 ℓ hℓ

private theorem par12_all : allBelow 64 (fun h => allBelow 64 fun l =>
    Nat.beq (par12 (64 * h + l)) (if Model.parN 12 (64 * h + l) then 1 else 0)) = true := by
  decide +kernel

theorem par12_eq : ∀ v < 4096, par12 v = if Model.parN 12 v then 1 else 0 := by
  intro v hv
  have h := allBelow_true (allBelow_true par12_all (v / 64) (by omega)) (v % 64) (by omega)
  rw [Nat.div_add_mod] at h
  exact Nat.eq_of_beq_eq_true h

theorem beq_div_mod (n : Nat) : Nat.beq (n / 16777216 % 2) 1 = n.testBit 24 := by
  rw [Nat.testBit_eq_decide_div_mod_eq, show (2 : Nat) ^ 24 = 16777216 from rfl]
  rcases Nat.mod_two_eq_zero_or_one (n / 16777216) with h | h <;> rw [h] <;> rfl

private theorem bit24 (b : Bool) (i : Nat) :
    ((if b then 1 else 0) * 16777216).testBit i = (b && decide (i = 24)) := by
  cases b
  · simp
  · rw [show (if true then 1 else 0) * 16777216 = 2 ^ 24 from rfl, Nat.testBit_two_pow]
    simp [eq_comm]

theorem unpackP_mulP (x y : Nat) : unpackP (mulP x y) = (unpackP x).mul (unpackP y) := by
  have hv : (y % 4096) &&& (x / 4096 % 4096) < 4096 :=
    Nat.and_lt_two_pow (n := 12) _ (Nat.mod_lt _ (by decide))
  unfold mulP
  rw [par12_eq _ hv]
  generalize hb : Model.parN 12 ((y % 4096) &&& (x / 4096 % 4096)) = b
  have hpair : Model.pairN (y % 4096) (x / 4096 % 4096) = b := hb
  simp only [unpackP, Model.Pauli.mul, Model.Pauli.s, Model.Pauli.a, Model.Pauli.d, hpair,
    beq_div_mod]
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · simp only [Nat.testBit_xor, bit24]
    simp
  · apply Nat.eq_of_testBit_eq
    intro i
    rw [show (4096 : Nat) = 2 ^ 12 from rfl]
    simp only [Nat.testBit_mod_two_pow, Nat.testBit_xor, bit24]
    by_cases hi : i < 12
    · simp [hi, show i ≠ 24 by omega]
    · simp [hi]
  · apply Nat.eq_of_testBit_eq
    intro i
    rw [show (4096 : Nat) = 2 ^ 12 from rfl]
    simp only [Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow, Nat.testBit_xor, bit24]
    by_cases hi : i < 12
    · simp [hi, show i + 12 ≠ 24 by omega]
    · simp [hi]

theorem mulP_lt {x y : Nat} (hx : x < 2 ^ 25) (hy : y < 2 ^ 25) : mulP x y < 2 ^ 25 := by
  unfold mulP
  refine Nat.xor_lt_two_pow (Nat.xor_lt_two_pow hx hy) ?_
  have h := Nat.mod_two_eq_zero_or_one (foldX 1 (foldX 2 (foldX 4 (foldX 8
    ((y % 4096) &&& (x / 4096 % 4096))))))
  unfold par12
  rcases h with h | h <;> rw [h] <;> decide

theorem unpackP_canon (x : Nat) : (unpackP x).2.1 < 4096 ∧ (unpackP x).2.2 < 4096 :=
  ⟨Nat.mod_lt _ (by decide), Nat.mod_lt _ (by decide)⟩

theorem unpackP_xor_rStar (x : Nat) : unpackP (x ^^^ rStarP) = (unpackP x).mul rStarN := by
  have h : mulP x rStarP = x ^^^ rStarP := by
    unfold mulP
    rw [show rStarP % 4096 = 0 from rfl, Nat.zero_and, show par12 0 * 16777216 = 0 from rfl,
      Nat.xor_zero]
  rw [← h, unpackP_mulP]
  rfl

theorem pcEqN_of_pcEqP {x y : Nat} (h : pcEqP x y = true) :
    pcEqN (unpackP x) (unpackP y) = true := by
  unfold pcEqP at h
  unfold pcEqN
  rw [Bool.or_eq_true, Nat.beq_eq, Nat.beq_eq] at h
  rcases h with h | h
  · rw [h]
    simp
  · rw [h, unpackP_xor_rStar]
    simp

theorem letterEq_sound {ℓ t : XLetter} (h : letterEq ℓ t = true) : ℓ = t := by
  cases ℓ <;> cases t <;> simp_all [letterEq, pauliEq, Prod.ext_iff]

private theorem idx_spec (ℓ : XLetter) : ∀ L : List XLetter,
    List.rec (motive := fun _ => Nat) 0 (fun t _ ih => bif letterEq ℓ t then 0 else ih + 1) L <
      L.length →
    L.getD (List.rec (motive := fun _ => Nat) 0
      (fun t _ ih => bif letterEq ℓ t then 0 else ih + 1) L) (.lift 0) = ℓ
  | [], h => absurd h (by simp)
  | t :: L, h => by
    change (bif letterEq ℓ t then 0 else _ + 1) < L.length + 1 at h
    change (t :: L).getD (bif letterEq ℓ t then 0 else _ + 1) (.lift 0) = ℓ
    cases he : letterEq ℓ t
    · rw [he] at h
      simp only [cond_false, List.getD_cons_succ] at h ⊢
      exact idx_spec ℓ L (by omega)
    · simp only [cond_true, List.getD_cons_zero]
      exact (letterEq_sound he).symm

theorem tLetters_length : tLetters.length = 9 := rfl

theorem tLetters_getD_tIdx {ℓ : XLetter} (h : tIdx ℓ < 9) : tLetters.getD (tIdx ℓ) (.lift 0) = ℓ :=
  idx_spec ℓ tLetters h

theorem rowIdx_lt {ℓ : XLetter} (h : okT ℓ = true) : rowIdx ℓ < 52 := by
  cases ℓ with
  | lift k =>
    have : k < 43 := by simpa [okT] using h
    change k < 52
    omega
  | pc y =>
    have : tIdx (.pc y) < 9 := by simpa [okT] using h
    change 43 + tIdx (.pc y) < 52
    omega
  | sign a =>
    have : tIdx (.sign a) < 9 := by simpa [okT] using h
    change 43 + tIdx (.sign a) < 52
    omega

theorem letterAt_rowIdx {ℓ : XLetter} (h : okT ℓ = true) : letterAt (rowIdx ℓ) = ℓ := by
  cases ℓ with
  | lift k =>
    have hk : k < 43 := by simpa [okT] using h
    simp [letterAt, rowIdx, hk]
  | pc y =>
    have hi : tIdx (.pc y) < 9 := by simpa [okT] using h
    have hb : Nat.blt (43 + tIdx (.pc y)) 43 = false :=
      Bool.eq_false_iff.2 (by rw [Ne, Nat.blt_eq]; omega)
    simp only [letterAt, rowIdx, hb, cond_false, Nat.add_sub_cancel_left]
    exact tLetters_getD_tIdx hi
  | sign a =>
    have hi : tIdx (.sign a) < 9 := by simpa [okT] using h
    have hb : Nat.blt (43 + tIdx (.sign a)) 43 = false :=
      Bool.eq_false_iff.2 (by rw [Ne, Nat.blt_eq]; omega)
    simp only [letterAt, rowIdx, hb, cond_false, Nat.add_sub_cancel_left]
    exact tLetters_getD_tIdx hi

private theorem tLetters_ok : ∀ j < 9, (tLetters.getD j (.lift 0)).ok = true := by decide +kernel

theorem okT_ok {ℓ : XLetter} (h : okT ℓ = true) : ℓ.ok = true := by
  cases ℓ with
  | lift k =>
    have hk : k < 43 := by simpa [okT] using h
    simpa [XLetter.ok] using hk
  | pc y =>
    have hi : tIdx (.pc y) < 9 := by simpa [okT] using h
    rw [← tLetters_getD_tIdx hi]
    exact tLetters_ok _ hi
  | sign a =>
    have hi : tIdx (.sign a) < 9 := by simpa [okT] using h
    rw [← tLetters_getD_tIdx hi]
    exact tLetters_ok _ hi

@[expose] def Canon (y : Model.Pauli) : Prop := y.2.1 < 4096 ∧ y.2.2 < 4096

private theorem packN_lt (f : Nat → Bool) : ∀ n, Model.packN f n < 2 ^ n
  | 0 => by
    rw [Model.packN]
    decide
  | n + 1 => by
    rw [Model.packN]
    refine Nat.or_lt_two_pow (lt_trans (packN_lt f n) (Nat.pow_lt_pow_right (by decide)
      (Nat.lt_succ_self n))) ?_
    split
    · exact Nat.pow_lt_pow_right (by decide) (Nat.lt_succ_self n)
    · exact Nat.two_pow_pos _

private theorem dualN_lt (v : Nat) : Model.dualN v < 4096 := packN_lt _ 12

private theorem coeffN_lt (v : Nat) : Model.coeffN v < 4096 := packN_lt _ 12

private theorem thetaRec_lt (a : Nat) : ∀ n, Model.thetaRec n a < 4096
  | 0 => by
    rw [Model.thetaRec]
    decide
  | n + 1 => by
    rw [Model.thetaRec]
    split
    · exact Nat.xor_lt_two_pow (n := 12) (Nat.xor_lt_two_pow (thetaRec_lt a n) (packN_lt _ 12))
        (dualN_lt _)
    · exact thetaRec_lt a n

private theorem thetaN_lt (a : Nat) : Model.thetaN a < 4096 := thetaRec_lt a 12

private theorem ite63_lt (P : Prop) [Decidable P] : (if P then 63 else 0 : Nat) < 2 ^ 12 := by
  split <;> decide

theorem conjPauliN_canon (q : Model.Pauli) {y : Model.Pauli} (hy : Canon y) :
    Canon (Model.conjPauliN q y) := hy

theorem conjPermN_canon (p : Array Nat) (y : Model.Pauli) : Canon (Model.conjPermN p y) :=
  ⟨coeffN_lt _, Nat.xor_lt_two_pow (n := 12) (thetaN_lt _) (dualN_lt _)⟩

theorem conjYN_canon {a : Nat} (ha : a < 4096) {y : Model.Pauli} (hy : Canon y) :
    Canon (Model.conjYN a y) := by
  obtain ⟨hya, hyd⟩ := hy
  simp only [Canon, Model.conjYN, Model.Pauli.mul, Model.conjTN, Model.conjDN, Model.Pauli.a,
    Model.Pauli.d, Model.Pauli.s, Model.acodeN]
  rw [show (4096 : Nat) = 2 ^ 12 from rfl] at ha hya hyd ⊢
  refine ⟨Nat.xor_lt_two_pow (Nat.xor_lt_two_pow (by decide)
    (Nat.xor_lt_two_pow hya (ite63_lt _))) (Nat.xor_lt_two_pow ?_ (ite63_lt _)), ?_⟩
  · split
    · exact ha
    · decide
  · refine Nat.xor_lt_two_pow (Nat.xor_lt_two_pow (by decide) (dualN_lt _)) (Nat.xor_lt_two_pow ?_ hyd)
    split
    · exact thetaN_lt _
    · decide

private theorem signCodes_lt : ∀ j < 11, ∀ a ∈ signCodesOf j, a < 4096 := by decide +kernel

private theorem foldl_conjYN_canon : ∀ (as : List Nat), (∀ a ∈ as, a < 4096) →
    ∀ {y : Model.Pauli}, Canon y → Canon (as.foldl (fun x a => Model.conjYN a x) y)
  | [], _, _, hy => hy
  | a :: as, h, _, hy => by
    rw [List.foldl_cons]
    exact foldl_conjYN_canon as (fun b hb => h b (List.mem_cons_of_mem _ hb))
      (conjYN_canon (h a (List.mem_cons_self ..)) hy)

theorem conjN_canon {ℓ : XLetter} (hℓ : okT ℓ = true) {y : Model.Pauli} (hy : Canon y) :
    Canon (ℓ.conjN y) := by
  cases ℓ with
  | lift k =>
    have hk : k < 43 := by simpa [okT] using hℓ
    change Canon (h1ConjN k y)
    unfold h1ConjN
    split
    · exact conjPauliN_canon _ hy
    · split
      · exact conjPauliN_canon _ (conjPermN_canon _ _)
      · first
          | exact foldl_conjYN_canon _ (signCodes_lt (k - 32) (by omega)) hy
          | (rw [if_pos hk]; exact foldl_conjYN_canon _ (signCodes_lt (k - 32) (by omega)) hy)
  | pc q => exact conjPauliN_canon q hy
  | sign a =>
    have hi : tIdx (.sign a) < 9 := by simpa [okT] using hℓ
    have h := tLetters_getD_tIdx hi
    have ha : a = 3 := by
      generalize tIdx (.sign a) = i at hi h
      interval_cases i <;> simp_all [tLetters]
    subst ha
    exact conjYN_canon (by decide) hy

end CFSG.KC.WordRelK
