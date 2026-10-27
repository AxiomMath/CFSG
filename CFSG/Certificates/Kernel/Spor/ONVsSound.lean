module

public import Certificates.Data.Kernel.Spor.ONVsK

public section

namespace CFSG.KS.ONVs

open CFSG.KC.Loop

theorem bAnd_vs {a b : Bool} (h : bAnd(a, b) = true) : a = true ∧ b = true := by
  cases a
  · exact absurd h Bool.false_ne_true
  · exact ⟨rfl, h⟩

theorem recAnd_vs (f : Nat → Bool) : ∀ n,
    Nat.rec (motive := fun _ => Bool) true
      (fun i ih => Bool.rec (motive := fun _ => Bool) false ih (f i)) n = true →
    ∀ i < n, f i = true
  | 0, _, i, hi => absurd hi (Nat.not_lt_zero i)
  | n + 1, h, i, hi => by
    obtain ⟨h1, h2⟩ := bAnd_vs h
    rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hlt | rfl
    · exact recAnd_vs f n h2 i hlt
    · exact h1

theorem allBelow_vs {m : Nat} {f : Nat → Bool} (h : allBelow m 1 f = true) (hm : m ≤ 64)
    (i : Nat) (him : i < m) : f i = true := by
  have h1 := recAnd_vs (fun h => Nat.rec (motive := fun _ => Bool) true (fun l ih2 =>
      bAnd((fun i => bIf(Nat.blt i m, f i, true)) (Nat.add (Nat.shiftLeft h 6) l), ih2)) 64) 1 h
    0 Nat.one_pos
  have h2 := recAnd_vs (fun l => (fun i => bIf(Nat.blt i m, f i, true))
    (Nat.add (Nat.shiftLeft 0 6) l)) 64 h1 i (by omega)
  have e : Nat.add (Nat.shiftLeft 0 6) i = i := by
    change 0 <<< 6 + i = i
    rw [Nat.zero_shiftLeft, Nat.zero_add]
  have hb : Nat.blt i m = true := Nat.blt_eq.mpr him
  dsimp only at h2
  rw [e, hb] at h2
  exact h2

@[expose] def decL : Nat → Nat → List Nat
  | 0, _ => []
  | n + 1, r => Nat.land r 15 :: decL n (Nat.shiftRight r 4)

@[expose] def wordL (w : Nat) : List Nat := decL (Nat.land w 255) (Nat.shiftRight w 8)

theorem trW_eq (L : Nat → Nat → Nat) : ∀ n r x,
    trW L n r x = (decL n r).foldl (fun x l => L l x) x
  | 0, _, _ => rfl
  | n + 1, r, x => trW_eq L n (Nat.shiftRight r 4) (L (Nat.land r 15) x)

theorem wAt_eq (L : Nat → Nat → Nat) (w x : Nat) :
    wAt L w x = (wordL w).foldl (fun x l => L l x) x :=
  trW_eq L _ _ x

theorem letOK_lt : ∀ n r, letOK n r = true → ∀ l ∈ decL n r, l < 6
  | 0, _, _, l, hl => absurd hl List.not_mem_nil
  | n + 1, r, h, l, hl => by
    obtain ⟨h1, h2⟩ := bAnd_vs h
    rcases List.mem_cons.1 hl with rfl | hl
    · exact Nat.blt_eq.mp h1
    · exact letOK_lt n (Nat.shiftRight r 4) h2 l hl

theorem wOK_lt {w : Nat} (h : wOK w = true) : ∀ l ∈ wordL w, l < 6 :=
  letOK_lt _ _ h

theorem lt_of_succ_lt {g : Nat → Nat} {m : Nat} (h : ∀ k < m, g k < g (k + 1)) :
    ∀ i j, i < j → j ≤ m → g i < g j := by
  intro i j hij hj
  induction j with
  | zero => exact absurd hij (Nat.not_lt_zero i)
  | succ j ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.1 hij with hlt | rfl
    · exact Nat.lt_trans (ih hlt (by omega)) (h j (by omega))
    · exact h i (by omega)

theorem vs_sound {L : Nat → Nat → Nat} {N F E : Nat → Nat} (h : vsCheck L N F E = true) :
    (∀ l < 6, L l 0 = 0) ∧ (∀ k < 39, ∀ l ∈ wordL (E k), l < 6) ∧ N 0 = 1 ∧ N 20 = 24 ∧
    F 2 = 1 ∧ F 6 = 3 ∧ F 20 = 11 ∧ F 56 = 28 ∧
    wAt L (E 0) 2 = N 2 ∧ wAt L (E 1) 6 = N 6 ∧ wAt L (E 2) 56 = N 56 ∧
    (∀ k < 36, wAt L (E (3 + k)) 20 = 20) ∧
    ∀ i < 36, ∀ j < 36, i < j → key L (E (3 + i)) < key L (E (3 + j)) := by
  obtain ⟨c1, h⟩ := bAnd_vs h
  obtain ⟨c2, h⟩ := bAnd_vs h
  obtain ⟨c3, h⟩ := bAnd_vs h
  obtain ⟨c4, h⟩ := bAnd_vs h
  obtain ⟨c5, h⟩ := bAnd_vs h
  obtain ⟨c6, h⟩ := bAnd_vs h
  obtain ⟨c7, h⟩ := bAnd_vs h
  obtain ⟨c8, h⟩ := bAnd_vs h
  obtain ⟨c9, h⟩ := bAnd_vs h
  obtain ⟨c10, h⟩ := bAnd_vs h
  obtain ⟨c11, h⟩ := bAnd_vs h
  obtain ⟨c12, c13⟩ := bAnd_vs h
  refine ⟨fun l hl => Nat.eq_of_beq_eq_true (allBelow_vs c1 (by decide) l hl),
    fun k hk => wOK_lt (allBelow_vs c2 (by decide) k hk), Nat.eq_of_beq_eq_true c3,
    Nat.eq_of_beq_eq_true c4, Nat.eq_of_beq_eq_true c5, Nat.eq_of_beq_eq_true c6,
    Nat.eq_of_beq_eq_true c7, Nat.eq_of_beq_eq_true c8, Nat.eq_of_beq_eq_true c9,
    Nat.eq_of_beq_eq_true c10, Nat.eq_of_beq_eq_true c11,
    fun k hk => Nat.eq_of_beq_eq_true (allBelow_vs c12 (by decide) k hk), ?_⟩
  intro i hi j hj hij
  refine lt_of_succ_lt (g := fun k => key L (E (3 + k))) (m := 35) (fun k hk => ?_) i j hij
    (by omega)
  have hk' := Nat.blt_eq.mp (allBelow_vs c13 (by decide) k hk)
  have e1 : Nat.add 3 k = 3 + k := rfl
  have e2 : Nat.add 4 k = 3 + (k + 1) := by
    change 4 + k = 3 + (k + 1)
    omega
  rw [e1, e2] at hk'
  exact hk'

end CFSG.KS.ONVs

end
