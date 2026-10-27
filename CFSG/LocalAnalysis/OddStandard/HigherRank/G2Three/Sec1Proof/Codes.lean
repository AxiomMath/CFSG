module

public import CFSG.RankThree.PartTwo.Census.Carrier.G2ThreeCodes
public import Mathlib.Tactic.Basify

public section

namespace CFSG.OddStandard.HigherRank.G2Three.Sec1Proof

open CFSG.RankThree.PartTwo.Census.Carrier.G2Three

abbrev Wm : Type := Matrix (Fin 14 ⊕ Fin 14) (Fin 14 ⊕ Fin 14) (ZMod 3)

@[expose] def wdiag (A B : Matrix (Fin 14) (Fin 14) (ZMod 3)) : Wm := Matrix.fromBlocks A 0 0 B

@[expose] def wanti (A B : Matrix (Fin 14) (Fin 14) (ZMod 3)) : Wm := Matrix.fromBlocks 0 A B 0

theorem wdiag_mul (A B C D : Matrix (Fin 14) (Fin 14) (ZMod 3)) :
    wdiag A B * wdiag C D = wdiag (A * C) (B * D) := by
  simp [wdiag, Matrix.fromBlocks_multiply]

theorem wdiag_mul_wanti (A B C D : Matrix (Fin 14) (Fin 14) (ZMod 3)) :
    wdiag A B * wanti C D = wanti (A * C) (B * D) := by
  simp [wdiag, wanti, Matrix.fromBlocks_multiply]

theorem wanti_mul_wdiag (A B C D : Matrix (Fin 14) (Fin 14) (ZMod 3)) :
    wanti A B * wdiag C D = wanti (A * D) (B * C) := by
  simp [wdiag, wanti, Matrix.fromBlocks_multiply]

theorem wanti_mul_wanti (A B C D : Matrix (Fin 14) (Fin 14) (ZMod 3)) :
    wanti A B * wanti C D = wdiag (A * D) (B * C) := by
  simp [wdiag, wanti, Matrix.fromBlocks_multiply]

theorem wdiag_one : wdiag 1 1 = (1 : Wm) := Matrix.fromBlocks_one

@[expose] def pcFlag (c : List ℕ) : Bool := c.headD 0 == 1

@[expose] def pcA (c : List ℕ) : List ℕ := (c.drop 1).take 196

@[expose] def pcB (c : List ℕ) : List ℕ := (c.drop 197).take 196

@[expose] def mkPc (f : Bool) (a b : List ℕ) : List ℕ := (if f then 1 else 0) :: (a ++ b)

@[expose] def decPc (c : List ℕ) : Wm :=
  if pcFlag c then wanti (dec14 (pcA c)) (dec14 (pcB c)) else wdiag (dec14 (pcA c)) (dec14 (pcB c))

@[expose] def mulPc (x y : List ℕ) : List ℕ :=
  match pcFlag x, pcFlag y with
  | false, false => mkPc false (mul14 (pcA x) (pcA y)) (mul14 (pcB x) (pcB y))
  | false, true => mkPc true (mul14 (pcA x) (pcA y)) (mul14 (pcB x) (pcB y))
  | true, false => mkPc true (mul14 (pcA x) (pcB y)) (mul14 (pcB x) (pcA y))
  | true, true => mkPc false (mul14 (pcA x) (pcB y)) (mul14 (pcB x) (pcA y))

@[expose] def onePc : List ℕ := mkPc false one14 one14

@[expose] def canonPc (c : List ℕ) : Bool :=
  c.length == 393 && (c.headD 0 == 0 || c.headD 0 == 1) && canon14 (pcA c) && canon14 (pcB c) &&
    (pcA c).any fun t => t != 0

theorem length_mul14 (m n : List ℕ) : (mul14 m n).length = 196 := by
  simp [mul14]

theorem pcFlag_mkPc (f : Bool) (a b : List ℕ) : pcFlag (mkPc f a b) = f := by
  cases f <;> simp [pcFlag, mkPc]

theorem pcA_mkPc (f : Bool) {a : List ℕ} (b : List ℕ) (ha : a.length = 196) :
    pcA (mkPc f a b) = a := by
  simp [pcA, mkPc, List.take_left' ha]

theorem pcB_mkPc (f : Bool) {a b : List ℕ} (ha : a.length = 196) (hb : b.length = 196) :
    pcB (mkPc f a b) = b := by
  simp [pcB, mkPc, List.drop_left' ha, List.take_of_length_le hb.le]

theorem length_one14 : one14.length = 196 := by simp [one14]

theorem decPc_mkPc_false {a b : List ℕ} (ha : a.length = 196) (hb : b.length = 196) :
    decPc (mkPc false a b) = wdiag (dec14 a) (dec14 b) := by
  unfold decPc
  rw [pcFlag_mkPc, pcA_mkPc _ _ ha, pcB_mkPc _ ha hb]
  simp

theorem decPc_mkPc_true {a b : List ℕ} (ha : a.length = 196) (hb : b.length = 196) :
    decPc (mkPc true a b) = wanti (dec14 a) (dec14 b) := by
  unfold decPc
  rw [pcFlag_mkPc, pcA_mkPc _ _ ha, pcB_mkPc _ ha hb]
  simp

theorem decPc_mulPc (x y : List ℕ) : decPc (mulPc x y) = decPc x * decPc y := by
  have h1 := length_mul14 (pcA x) (pcA y)
  have h2 := length_mul14 (pcB x) (pcB y)
  have h3 := length_mul14 (pcA x) (pcB y)
  have h4 := length_mul14 (pcB x) (pcA y)
  have dx : decPc x = if pcFlag x = true then wanti (dec14 (pcA x)) (dec14 (pcB x))
      else wdiag (dec14 (pcA x)) (dec14 (pcB x)) := rfl
  have dy : decPc y = if pcFlag y = true then wanti (dec14 (pcA y)) (dec14 (pcB y))
      else wdiag (dec14 (pcA y)) (dec14 (pcB y)) := rfl
  cases hx : pcFlag x <;> cases hy : pcFlag y <;> simp only [hx, hy] at dx dy <;>
    simp only [mulPc, hx, hy, Bool.false_eq_true, if_false, if_true] at dx dy ⊢
  · rw [decPc_mkPc_false h1 h2, dx, dy, wdiag_mul, dec14_mul14, dec14_mul14]
  · rw [decPc_mkPc_true h1 h2, dx, dy, wdiag_mul_wanti, dec14_mul14, dec14_mul14]
  · rw [decPc_mkPc_true h3 h4, dx, dy, wanti_mul_wdiag, dec14_mul14, dec14_mul14]
  · rw [decPc_mkPc_false h3 h4, dx, dy, wanti_mul_wanti, dec14_mul14, dec14_mul14]

theorem decPc_onePc : decPc onePc = 1 := by
  unfold onePc
  rw [decPc_mkPc_false length_one14 length_one14, dec14_one14, wdiag_one]

theorem canonPc_onePc : canonPc onePc = true := by
  have hl : onePc.length = 393 := by simp [onePc, mkPc, length_one14]
  have ha : pcA onePc = one14 := pcA_mkPc _ _ length_one14
  have hb : pcB onePc = one14 := pcB_mkPc _ length_one14 length_one14
  have hany : one14.any (fun t => t != 0) = true := by decide +kernel
  simp only [canonPc, hl, ha, hb, canon14_one14, hany]
  simp [onePc, mkPc]

theorem length_of_canonPc {c : List ℕ} (h : canonPc c = true) : c.length = 393 := by
  simp only [canonPc, Bool.and_eq_true, beq_iff_eq] at h
  exact h.1.1.1.1

theorem eq_mkPc_of_length {c : List ℕ} (h : c.length = 393) :
    c = c.headD 0 :: (pcA c ++ pcB c) := by
  rcases c with _ | ⟨x, t⟩
  · simp at h
  · have ht : t.length = 392 := by simpa using h
    simp only [pcA, pcB, List.drop_succ_cons, List.drop_zero, List.headD_cons]
    have hd : (t.drop 196).length = 196 := by simp [ht]
    rw [List.take_of_length_le hd.le, List.take_append_drop]

theorem canonPc_spec {c : List ℕ} (h : canonPc c = true) :
    c.length = 393 ∧ (c.headD 0 = 0 ∨ c.headD 0 = 1) ∧ canon14 (pcA c) = true ∧
      canon14 (pcB c) = true ∧ (pcA c).any (fun t => t != 0) = true := by
  simp only [canonPc, Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true] at h
  exact ⟨h.1.1.1.1, h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩

theorem pcA_ne_zero {c : List ℕ} (h : canonPc c = true) : dec14 (pcA c) ≠ 0 := by
  obtain ⟨-, -, hA, -, hany⟩ := canonPc_spec h
  intro h0
  have hz : dec14 (List.replicate 196 0) = 0 := by
    ext i j
    simp only [dec14, Matrix.of_apply, Matrix.zero_apply, List.getD_eq_getElem?_getD,
      List.getElem?_getD_replicate_default_eq, Nat.cast_zero]
  have hcz : canon14 (List.replicate 196 0) = true := by decide +kernel
  have := dec14_injective hA hcz (h0.trans hz.symm)
  rw [this] at hany
  exact absurd hany (by decide +kernel)

theorem decPc_injective {x y : List ℕ} (hx : canonPc x = true) (hy : canonPc y = true)
    (h : decPc x = decPc y) : x = y := by
  obtain ⟨lx, fx, ax, bx, -⟩ := canonPc_spec hx
  obtain ⟨ly, fy, ay, bY, -⟩ := canonPc_spec hy
  have nx := pcA_ne_zero hx
  have ny := pcA_ne_zero hy
  have key : pcFlag x = pcFlag y ∧ dec14 (pcA x) = dec14 (pcA y) ∧
      dec14 (pcB x) = dec14 (pcB y) := by
    unfold decPc at h
    cases hfx : pcFlag x <;> cases hfy : pcFlag y <;> simp only [hfx, hfy] at h ⊢ <;>
      simp only [Bool.false_eq_true, if_false, if_true, wdiag, wanti,
        Matrix.fromBlocks_inj] at h
    · exact ⟨trivial, h.1, h.2.2.2⟩
    · exact absurd h.1 nx
    · exact absurd h.1.symm ny
    · exact ⟨trivial, h.2.1, h.2.2.1⟩
  obtain ⟨hf, hA, hB⟩ := key
  have eA := dec14_injective ax ay hA
  have eB := dec14_injective bx bY hB
  have eh : x.headD 0 = y.headD 0 := by
    unfold pcFlag at hf
    rcases fx with h1 | h1 <;> rcases fy with h2 | h2 <;> rw [h1, h2] at hf
    · exact h1.trans h2.symm
    · exact absurd hf (by decide)
    · exact absurd hf (by decide)
    · exact h1.trans h2.symm
  rw [eq_mkPc_of_length lx, eq_mkPc_of_length ly, eh, eA, eB]

end CFSG.OddStandard.HigherRank.G2Three.Sec1Proof
