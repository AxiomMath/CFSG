module

public import CFSG.Certificates.Kernel.Misc.Sp6SndBase

public section

namespace CFSG.KC.Misc.Sp6.Snd

open CFSG.KC.Ord CFSG.KC.LQT.P CFSG.KC.Misc CFSG.KC.Misc.O62 CFSG.KC.Misc.Sp6
open CFSG.LocalAnalysis.ComponentInitial.ChevSp6EpsOne

private theorem div_add_small (W M len : ℕ) (h : W % M + len < M) :
    (W + len) / M = W / M := by
  have hd : W / M * M + W % M = W := by rw [Nat.mul_comm]; exact Nat.div_add_mod W M
  have e : (W / M + 1) * M = W / M * M + M := Nat.succ_mul (W / M) M
  apply Nat.div_eq_of_lt_le <;> omega

private theorem qlPack_gen (F : List ℕ → ℕ → ℕ → ℕ)
    (hnil : ∀ i acc, F [] i acc = acc + i)
    (hcons : ∀ x t i acc, F (x :: t) i acc = F t (i + 1) (acc ||| (x <<< (8 + 36 * i)))) :
    ∀ (l : List ℕ) (i acc : ℕ), (∀ x ∈ l, x < 2 ^ 36) → acc < 2 ^ (8 + 36 * i) →
      ∃ W : ℕ, F l i acc = W + (i + l.length) ∧ W % 2 ^ (8 + 36 * i) = acc ∧
        ∀ k < l.length, (W / 2 ^ (8 + 36 * (i + k))) % 2 ^ 36 = l.getD k 0 := by
  intro l
  induction l with
  | nil =>
    intro i acc _ hacc
    refine ⟨acc, ?_, Nat.mod_eq_of_lt hacc, fun k hk => by simp at hk⟩
    rw [hnil, List.length_nil, Nat.add_zero]
  | cons x t ih =>
    intro i acc hx hacc
    have hxt : x < 2 ^ 36 := hx x (List.mem_cons_self ..)
    have hT : ∀ y ∈ t, y < 2 ^ 36 := fun y hy => hx y (List.mem_cons_of_mem x hy)
    have hs : 2 ^ (8 + 36 * (i + 1)) = 2 ^ (8 + 36 * i) * 2 ^ 36 := by
      rw [← Nat.pow_add]; congr 1
    have hor : acc ||| (x <<< (8 + 36 * i)) = acc + 2 ^ (8 + 36 * i) * x := by
      rw [Nat.shiftLeft_eq, Nat.mul_comm x, Nat.or_comm, Nat.add_comm acc,
        ← Nat.two_pow_add_eq_or_of_lt hacc x]
    have hacc' : acc ||| (x <<< (8 + 36 * i)) < 2 ^ (8 + 36 * (i + 1)) := by
      rw [hor, hs]
      have h1 : acc + 2 ^ (8 + 36 * i) * x < 2 ^ (8 + 36 * i) + 2 ^ (8 + 36 * i) * x :=
        Nat.add_lt_add_right hacc _
      have h2 : 2 ^ (8 + 36 * i) + 2 ^ (8 + 36 * i) * x = 2 ^ (8 + 36 * i) * (x + 1) := by
        rw [Nat.mul_add, Nat.mul_one, Nat.add_comm]
      have h3 : 2 ^ (8 + 36 * i) * (x + 1) ≤ 2 ^ (8 + 36 * i) * 2 ^ 36 :=
        Nat.mul_le_mul_left _ (Nat.succ_le_of_lt hxt)
      rw [h2] at h1
      exact lt_of_lt_of_le h1 h3
    obtain ⟨W, hW, hWlow, hWf⟩ := ih (i + 1) (acc ||| (x <<< (8 + 36 * i))) hT hacc'
    have hdvd : 2 ^ (8 + 36 * i) ∣ 2 ^ (8 + 36 * (i + 1)) := Nat.pow_dvd_pow 2 (by omega)
    refine ⟨W, ?_, ?_, ?_⟩
    · rw [hcons, hW, List.length_cons]; omega
    · rw [← Nat.mod_mod_of_dvd W hdvd, hWlow, hor, Nat.add_mul_mod_self_left,
        Nat.mod_eq_of_lt hacc]
    · intro k hk
      cases k with
      | zero =>
        rw [List.getD_cons_zero, Nat.add_zero, ← Nat.mod_mul_right_div_self, ← hs, hWlow, hor,
          Nat.add_mul_div_left _ _ (Nat.two_pow_pos _), Nat.div_eq_of_lt hacc, Nat.zero_add]
      | succ k' =>
        have hk' : k' < t.length := by simp only [List.length_cons] at hk; omega
        have e : i + (k' + 1) = i + 1 + k' := by omega
        rw [List.getD_cons_succ, e]
        exact hWf k' hk'

private theorem qlOfL_pack (Pl : List ℕ) (h : ∀ x ∈ Pl, x < 2 ^ 36) :
    ∃ W : ℕ, qlOfL Pl = W + Pl.length ∧ W % 256 = 0 ∧
      ∀ k < Pl.length, (W / 2 ^ (8 + 36 * k)) % 2 ^ 36 = Pl.getD k 0 := by
  obtain ⟨W, hW, hlow, hf⟩ := qlPack_gen
    (fun l i acc => List.rec (motive := fun _ => ℕ → ℕ → ℕ) (fun i acc => Nat.add acc i)
      (fun x _ ih i acc => ih (Nat.succ i) (Nat.lor acc (Nat.shiftLeft x
        (Nat.add (nat_lit 8) (Nat.mul (nat_lit 36) i))))) l i acc)
    (fun _ _ => rfl) (fun _ _ _ _ => rfl) Pl 0 0 h (Nat.two_pow_pos _)
  have hq : qlOfL Pl = W + (0 + Pl.length) := hW
  refine ⟨W, by rw [hq, Nat.zero_add], ?_, ?_⟩
  · have h8 : (2 : ℕ) ^ (8 + 36 * 0) = 256 := rfl
    rw [h8] at hlow
    exact hlow
  · intro k hk
    have hfk := hf k hk
    rw [Nat.zero_add] at hfk
    exact hfk

theorem qlAt_qlOfL {Pl : List ℕ} (h : ∀ x ∈ Pl, x < 2 ^ 36) (hl : Pl.length < 256) {i : ℕ}
    (hi : i < Pl.length) : qlAt (qlOfL Pl) i = Pl[i] := by
  obtain ⟨W, hq, h256, hf⟩ := qlOfL_pack Pl h
  have hget : Pl.getD i 0 = Pl[i] := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
    rfl
  rw [← hget, ← hf i hi]
  unfold qlAt
  change (qlOfL Pl >>> (8 + 36 * i)) &&& (2 ^ 36 - 1) = (W / 2 ^ (8 + 36 * i)) % 2 ^ 36
  rw [Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow, hq]
  congr 1
  have hM : 256 ∣ 2 ^ (8 + 36 * i) :=
    Nat.dvd_trans (⟨1, rfl⟩ : 256 ∣ 2 ^ 8) (Nat.pow_dvd_pow 2 (by omega))
  have hr : W % 2 ^ (8 + 36 * i) % 256 = 0 := by
    rw [Nat.mod_mod_of_dvd W hM]
    exact h256
  have hMlt : W % 2 ^ (8 + 36 * i) < 2 ^ (8 + 36 * i) := Nat.mod_lt _ (Nat.two_pow_pos _)
  have hM0 : 2 ^ (8 + 36 * i) % 256 = 0 := Nat.mod_eq_zero_of_dvd hM
  have hsm : W % 2 ^ (8 + 36 * i) + Pl.length < 2 ^ (8 + 36 * i) := by
    generalize W % 2 ^ (8 + 36 * i) = r at hr hMlt ⊢
    generalize 2 ^ (8 + 36 * i) = M at hM0 hMlt hr ⊢
    omega
  exact div_add_small W _ _ hsm

theorem qlMem_iff {Q y : ℕ} : qlMem Q y = true ↔ ∃ i < qlCnt Q, qlAt Q i = y := by
  unfold qlMem
  simp only [letB_eq, anyN_eq_true, Nat.beq_eq]

private theorem qlIdx_fold (c : ℕ) (P : ℕ → Bool) (n : ℕ) (h : ∃ i < n, P i = true) :
    (Nat.rec (motive := fun _ => ℕ) c
        (fun i acc => Bool.rec (motive := fun _ => ℕ) acc i (P i)) n) < n ∧
      P (Nat.rec (motive := fun _ => ℕ) c
        (fun i acc => Bool.rec (motive := fun _ => ℕ) acc i (P i)) n) = true := by
  induction n with
  | zero =>
    obtain ⟨i, hi, -⟩ := h
    omega
  | succ n ih =>
    dsimp only
    cases hP : P n
    · obtain ⟨i, hi, hPi⟩ := h
      have hin : i < n := by
        rcases Nat.lt_succ_iff_lt_or_eq.mp hi with h1 | h1
        · exact h1
        · subst h1
          rw [hP] at hPi
          exact absurd hPi (by decide)
      obtain ⟨h1, h2⟩ := ih ⟨i, hin, hPi⟩
      exact ⟨Nat.lt_succ_of_lt h1, h2⟩
    · dsimp only
      exact ⟨Nat.lt_succ_self n, hP⟩

theorem qlIdx_spec {Q y : ℕ} (h : ∃ i < qlCnt Q, qlAt Q i = y) :
    qlIdx Q y < qlCnt Q ∧ qlAt Q (qlIdx Q y) = y := by
  obtain ⟨j, hj, hjy⟩ := h
  have key := qlIdx_fold (qlCnt Q) (fun i => Nat.beq (qlAt Q i) y) (qlCnt Q)
    ⟨j, hj, by simp [hjy]⟩
  unfold qlIdx
  simp only [letN_eq]
  exact ⟨key.1, by simpa using key.2⟩

private theorem commFold_testBit (P : ℕ → Bool) (n b : ℕ) :
    (Nat.rec (motive := fun _ => ℕ) (nat_lit 0)
        (fun j acc => Bool.rec (motive := fun _ => ℕ) acc (acc ||| (1 <<< j)) (P j)) n).testBit b
      = true ↔ b < n ∧ P b = true := by
  induction n with
  | zero => simp
  | succ n ih =>
    dsimp only
    cases hP : P n
    · dsimp only
      rw [ih]
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨by omega, h2⟩
      · rintro ⟨h1, h2⟩
        refine ⟨?_, h2⟩
        have hbn : b ≠ n := by
          rintro rfl
          rw [hP] at h2
          exact absurd h2 (by decide)
        omega
    · dsimp only
      rw [Nat.testBit_or, Bool.or_eq_true, ih, Nat.one_shiftLeft, Nat.testBit_two_pow]
      constructor
      · rintro ((⟨h1, h2⟩) | h)
        · exact ⟨by omega, h2⟩
        · have e := of_decide_eq_true h
          subst e
          exact ⟨Nat.lt_succ_self n, hP⟩
      · rintro ⟨h1, h2⟩
        rcases Nat.lt_or_ge b n with h3 | h3
        · exact Or.inl ⟨h3, h2⟩
        · exact Or.inr (decide_eq_true (by omega))

theorem commMask_testBit (PQ x j : ℕ) : (commMask PQ x).testBit j = true ↔
    j < qlCnt PQ ∧ compK x (qlAt PQ j) = compK (qlAt PQ j) x := by
  unfold commMask
  simp only [letN_eq]
  refine (commFold_testBit (fun i => Nat.beq (compK x (qlAt PQ i)) (compK (qlAt PQ i) x))
    (qlCnt PQ) j).trans ?_
  simp only [Nat.beq_eq]

private theorem adjFold_testBit (base : ℕ) (P : ℕ → Bool) (f : ℕ → ℕ) (n b : ℕ) :
    (Nat.rec (motive := fun _ => ℕ) base
        (fun i acc => Bool.rec (motive := fun _ => ℕ) acc (acc ||| (1 <<< f i)) (P i)) n).testBit b
      = true ↔ base.testBit b = true ∨ ∃ i < n, P i = true ∧ f i = b := by
  induction n with
  | zero => simp
  | succ n ih =>
    dsimp only
    cases hP : P n
    · dsimp only
      rw [ih]
      constructor
      · rintro (h | ⟨i, hi, h⟩)
        · exact Or.inl h
        · exact Or.inr ⟨i, by omega, h⟩
      · rintro (h | ⟨i, hi, h1, h2⟩)
        · exact Or.inl h
        · rcases Nat.lt_succ_iff_lt_or_eq.mp hi with h3 | h3
          · exact Or.inr ⟨i, h3, h1, h2⟩
          · subst h3
            rw [hP] at h1
            exact absurd h1 (by decide)
    · dsimp only
      rw [Nat.testBit_or, Bool.or_eq_true, ih, Nat.one_shiftLeft, Nat.testBit_two_pow]
      constructor
      · rintro ((h | ⟨i, hi, h⟩) | h)
        · exact Or.inl h
        · exact Or.inr ⟨i, by omega, h⟩
        · exact Or.inr ⟨n, Nat.lt_succ_self n, hP, of_decide_eq_true h⟩
      · rintro (h | ⟨i, hi, h1, h2⟩)
        · exact Or.inl (Or.inl h)
        · rcases Nat.lt_succ_iff_lt_or_eq.mp hi with h3 | h3
          · exact Or.inl (Or.inr ⟨i, h3, h1, h2⟩)
          · subst h3
            exact Or.inr (decide_eq_true h2)

theorem adjK_testBit (PQ x A j : ℕ) : (adjK PQ x A).testBit j = true ↔
    A.testBit j = true ∨ ∃ i < 128, A.testBit i = true ∧ qlIdx PQ (compK x (qlAt PQ i)) = j := by
  unfold adjK
  refine (adjFold_testBit A (fun i => hasB A i) (fun i => qlIdx PQ (compK x (qlAt PQ i)))
    128 j).trans ?_
  simp only [hasB_eq]

end CFSG.KC.Misc.Sp6.Snd

end
