module

public import Certificates.Data.Kernel.Spor.Fi24Pair
public import CFSG.Certificates.Kernel.BenesSound

public section

namespace CFSG.KC.Fi24Pair

open CFSG.KC.Benes CFSG.KC.MonsterConv.Perm CFSG.KLC.Fi22

private theorem testBit_succ_of_even {a : Nat} (h : a % 2 = 0) (k : Nat) :
    (a + 1).testBit k = (decide (k = 0) || a.testBit k) := by
  cases k with
  | zero =>
    have : (a + 1) % 2 = 1 := by omega
    simp [Nat.testBit_zero, this]
  | succ k =>
    rw [Nat.testBit_add_one, Nat.testBit_add_one]
    have : (a + 1) / 2 = a / 2 := by omega
    rw [this]
    simp

private theorem testBit_add_pow_clear {p b : Nat} (h : p.testBit b = false) (c : Nat) :
    (p + 2 ^ b).testBit c = (decide (c = b) || p.testBit c) := by
  obtain ⟨a, s, hs, rfl⟩ : ∃ a s, s < 2 ^ b ∧ p = 2 ^ b * a + s :=
    ⟨p / 2 ^ b, p % 2 ^ b, Nat.mod_lt _ (Nat.two_pow_pos b), (Nat.div_add_mod p (2 ^ b)).symm⟩
  have ha : a % 2 = 0 := by
    rw [Nat.testBit_two_pow_mul_add a hs b, if_neg (Nat.lt_irrefl b), Nat.sub_self,
      Nat.testBit_zero] at h
    simpa using h
  have e2 : 2 ^ b * a + s + 2 ^ b = 2 ^ b * (a + 1) + s := by
    rw [Nat.mul_succ]
    omega
  rw [e2, Nat.testBit_two_pow_mul_add _ hs, Nat.testBit_two_pow_mul_add _ hs]
  by_cases hc : c < b
  · rw [if_pos hc, if_pos hc, decide_eq_false (by omega), Bool.false_or]
  · rw [if_neg hc, if_neg hc, testBit_succ_of_even ha (c - b)]
    have : decide (c - b = 0) = decide (c = b) := by
      by_cases hcb : c = b
      · subst hcb
        simp
      · rw [decide_eq_false hcb, decide_eq_false (by omega)]
    rw [this]

private theorem testBit_sub_pow_set {q b : Nat} (h : q.testBit b = true) :
    2 ^ b ≤ q ∧ (q - 2 ^ b).testBit b = false ∧
      ∀ c, c ≠ b → (q - 2 ^ b).testBit c = q.testBit c := by
  have hle : 2 ^ b ≤ q := Nat.ge_two_pow_of_testBit h
  have e : q = 2 ^ b + (q - 2 ^ b) := by omega
  have h0 : (q - 2 ^ b).testBit b = false := by
    have := Nat.testBit_two_pow_add_eq (q - 2 ^ b) b
    rw [← e, h] at this
    cases hh : (q - 2 ^ b).testBit b
    · rfl
    · rw [hh] at this
      exact absurd this (by decide)
  refine ⟨hle, h0, fun c hc => ?_⟩
  have := testBit_add_pow_clear h0 c
  rw [Nat.sub_add_cancel hle] at this
  rw [this, decide_eq_false hc, Bool.false_or]

private theorem trS_eq (t : Nat) : trS t = 2 ^ (t + 12) - 2 ^ t := by
  simp only [trS, nsub, nshl, nadd, Nat.one_shiftLeft]

private theorem W24_eq : W24 = 2 ^ 24 := rfl

private theorem testBit_trM {t : Nat} (ht : t < 12) (q : Nat) :
    (trM t).testBit q = (decide (q < 2 ^ 24) && q.testBit t && !q.testBit (t + 12)) := by
  unfold trM
  rw [W24_eq]
  simp only [nland, nxor, nadd, Nat.testBit_and, Nat.testBit_xor, ones_eq,
    Nat.testBit_two_pow_sub_one]
  rw [idPlane_testBit (by omega), idPlane_testBit (by omega)]
  cases decide (q < 2 ^ 24) <;> cases q.testBit t <;> cases q.testBit (t + 12) <;> rfl

private theorem mem_trM {t : Nat} (ht : t < 12) (q : Nat) :
    (trM t).testBit q = true ↔ q < 2 ^ 24 ∧ q.testBit t = true ∧ q.testBit (t + 12) = false := by
  rw [testBit_trM ht]
  simp [and_assoc]

private theorem testBit_add_trS {t q : Nat} (h1 : q.testBit t = true)
    (h2 : q.testBit (t + 12) = false) (c : Nat) :
    (q + (2 ^ (t + 12) - 2 ^ t)).testBit c =
      (if c = t then false else if c = t + 12 then true else q.testBit c) := by
  obtain ⟨hle, h0, hc⟩ := testBit_sub_pow_set h1
  have e : q + (2 ^ (t + 12) - 2 ^ t) = (q - 2 ^ t) + 2 ^ (t + 12) := by
    have : 2 ^ t ≤ 2 ^ (t + 12) := Nat.pow_le_pow_right (by decide) (by omega)
    omega
  have hx : (q - 2 ^ t).testBit (t + 12) = false := by
    rw [hc _ (by omega), h2]
  rw [e, testBit_add_pow_clear hx]
  by_cases h3 : c = t
  · subst h3
    rw [h0, if_pos rfl, decide_eq_false (by omega), Bool.false_or]
  · by_cases h4 : c = t + 12
    · subst h4
      rw [if_neg h3, if_pos rfl, decide_eq_true rfl, Bool.true_or]
    · rw [if_neg h3, if_neg h4, decide_eq_false h4, Bool.false_or, hc c h3]

private def trSrc (t c : Nat) : Nat := if c = t then t + 12 else if c = t + 12 then t else c

private theorem trSrc_low {t c : Nat} (h : c = t) : trSrc t c = t + 12 := by
  unfold trSrc
  rw [if_pos h]

private theorem trSrc_high {t c : Nat} (h : c = t + 12) : trSrc t c = t := by
  unfold trSrc
  rw [if_neg (by omega), if_pos h]

private theorem trSrc_ne {t c : Nat} (h1 : c ≠ t) (h2 : c ≠ t + 12) : trSrc t c = c := by
  unfold trSrc
  rw [if_neg h1, if_neg h2]

private theorem testBit_swp_tr {t : Nat} (ht : t < 12) {q : Nat} (hq : q < 2 ^ 24) (c : Nat) :
    (swp (trS t) (trM t) q).testBit c = q.testBit (trSrc t c) := by
  have hD := trS_eq t
  have hpow : 2 ^ t ≤ 2 ^ (t + 12) := Nat.pow_le_pow_right (by decide) (by omega)
  have hpos : 0 < 2 ^ t := Nat.two_pow_pos t
  unfold swp
  by_cases hA : (trM t).testBit q = true
  · rw [if_pos hA]
    obtain ⟨-, h1, h2⟩ := (mem_trM ht q).1 hA
    rw [hD, testBit_add_trS h1 h2 c]
    by_cases h3 : c = t
    · rw [if_pos h3, trSrc_low h3]
      exact h2.symm
    · by_cases h4 : c = t + 12
      · rw [if_neg h3, if_pos h4, trSrc_high h4]
        exact h1.symm
      · rw [if_neg h3, if_neg h4, trSrc_ne h3 h4]
  · rw [if_neg hA]
    by_cases hB : trS t ≤ q ∧ (trM t).testBit (q - trS t) = true
    · rw [if_pos hB]
      obtain ⟨hd, hm⟩ := hB
      obtain ⟨q', rfl⟩ : ∃ q', q = q' + trS t := ⟨q - trS t, by omega⟩
      rw [Nat.add_sub_cancel] at hm ⊢
      obtain ⟨-, h1, h2⟩ := (mem_trM ht q').1 hm
      rw [hD, testBit_add_trS h1 h2 (trSrc t c)]
      by_cases h3 : c = t
      · rw [trSrc_low h3, if_neg (by omega), if_pos rfl, h3]
        exact h1
      · by_cases h4 : c = t + 12
        · rw [trSrc_high h4, if_pos rfl, h4]
          exact h2
        · rw [trSrc_ne h3 h4, if_neg h3, if_neg h4]
    · rw [if_neg hB]
      have hsame : q.testBit t = q.testBit (t + 12) := by
        cases h1 : q.testBit t <;> cases h2 : q.testBit (t + 12)
        · rfl
        · exfalso
          obtain ⟨hle, h0, hc⟩ := testBit_sub_pow_set h2
          have hxt : (q - 2 ^ (t + 12)).testBit t = false := by
            rw [hc t (by omega), h1]
          have e : q - trS t = (q - 2 ^ (t + 12)) + 2 ^ t := by
            rw [hD]
            omega
          apply hB
          refine ⟨by omega, ?_⟩
          rw [e, mem_trM ht]
          refine ⟨by omega, ?_, ?_⟩
          · rw [testBit_add_pow_clear hxt, decide_eq_true rfl, Bool.true_or]
          · rw [testBit_add_pow_clear hxt, decide_eq_false (by omega), Bool.false_or, h0]
        · exact absurd ((mem_trM ht q).2 ⟨hq, h1, h2⟩) hA
        · rfl
      by_cases h3 : c = t
      · rw [trSrc_low h3, h3]
        exact hsame
      · by_cases h4 : c = t + 12
        · rw [trSrc_high h4, h4]
          exact hsame.symm
        · rw [trSrc_ne h3 h4]

private theorem swp_tr_lt {t : Nat} (ht : t < 12) {q : Nat} (hq : q < 2 ^ 24) :
    swp (trS t) (trM t) q < 2 ^ 24 := by
  apply Nat.lt_pow_two_of_testBit
  intro c hc
  rw [testBit_swp_tr ht hq c, trSrc_ne (by omega) (by omega)]
  exact Nat.testBit_lt_two_pow (lt_two_pow_mono hq hc)

private theorem disj_tr {t : Nat} (ht : t < 12) : Disj (trS t) (trM t) := by
  intro q hq
  obtain ⟨-, h1, h2⟩ := (mem_trM ht q).1 hq
  rw [testBit_trM ht, trS_eq, testBit_add_trS h1 h2 t, if_pos rfl]
  simp

private theorem testBit_tr_comp (X q : Nat) :
    (tr X).testBit q = X.testBit (compF (fun t => swp (trS t) (trM t)) 0 12 q) := by
  unfold tr
  rw [iterN_eq]
  exact testBit_iterF (f := fun t Y => dsw (trS t) (trM t) Y) (τ := fun t => swp (trS t) (trM t))
    (c := 12) (fun i hi y q => testBit_dsw (disj_tr hi) y q) 0 12 (by omega) X q

private def trIdx (n c : Nat) : Nat :=
  if c < n then c + 12 else if 12 ≤ c ∧ c < n + 12 then c - 12 else c

private theorem trIdx_succ {n : Nat} (hn : n < 12) (c : Nat) :
    trIdx (n + 1) c = trSrc n (trIdx n c) := by
  unfold trIdx trSrc
  repeat' split
  all_goals omega

private theorem testBit_compF_tr : ∀ n, n ≤ 12 → ∀ q, q < 2 ^ 24 → ∀ c,
    (compF (fun t => swp (trS t) (trM t)) 0 n q).testBit c = q.testBit (trIdx n c)
  | 0, _, q, _, c => by
    rw [trIdx, if_neg (by omega), if_neg (by omega)]
    rfl
  | n + 1, hn, q, hq, c => by
    rw [compF_snoc, Nat.zero_add,
      testBit_compF_tr n (by omega) _ (swp_tr_lt (t := n) (by omega) hq) c,
      testBit_swp_tr (t := n) (by omega) hq, trIdx_succ (by omega)]

private theorem testBit_mul4096 (a b : Nat) (hb : b < 4096) (e : Nat) :
    (4096 * a + b).testBit e = if e < 12 then b.testBit e else a.testBit (e - 12) := by
  have := Nat.testBit_two_pow_mul_add a (b := b) (i := 12) (by simpa using hb) e
  simpa using this

private theorem compF_tr_swap {i j : Nat} (hi : i < 4096) (hj : j < 4096) :
    compF (fun t => swp (trS t) (trM t)) 0 12 (4096 * i + j) = 4096 * j + i := by
  have hq : 4096 * i + j < 2 ^ 24 := by omega
  apply Nat.eq_of_testBit_eq
  intro c
  rw [testBit_compF_tr 12 (Nat.le_refl 12) _ hq c]
  by_cases h1 : c < 12
  · rw [trIdx, if_pos h1, testBit_mul4096 i j hj, testBit_mul4096 j i hi, if_neg (by omega),
      if_pos h1, show c + 12 - 12 = c by omega]
  · by_cases h2 : c < 24
    · rw [trIdx, if_neg h1, if_pos ⟨by omega, by omega⟩, testBit_mul4096 i j hj,
        testBit_mul4096 j i hi, if_pos (by omega), if_neg h1]
    · rw [trIdx, if_neg h1, if_neg (by omega), testBit_mul4096 i j hj, testBit_mul4096 j i hi,
        if_neg h1, if_neg h1]
      have h3 : 4096 ≤ 2 ^ (c - 12) := by
        have := Nat.pow_le_pow_right (n := 2) (by decide) (show 12 ≤ c - 12 by omega)
        simpa using this
      rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hi h3),
        Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hj h3)]

private theorem testBit_tr (X : Nat) {i j : Nat} (hi : i < 4096) (hj : j < 4096) :
    (tr X).testBit (4096 * i + j) = X.testBit (4096 * j + i) := by
  rw [testBit_tr_comp, compF_tr_swap hi hj]

private theorem R24_eq : R24 = maskN (4096 * 4096) / M4096 := rfl

private theorem stageDist_eq : ∀ s < 23, stageDist s = stageShift 12 s := by decide

private theorem nwMask_eq (NW s : Nat) : nwMask NW s = benesMask 12 NW s := by
  unfold nwMask benesMask
  have h1 : Nat.shiftLeft s 12 = Nat.mul s (2 ^ 12) := Nat.shiftLeft_eq s 12
  have h2 : M4096 = ones (2 ^ 12) := rfl
  rw [h1, h2]

private theorem nwPerm_eq (NW p : Nat) : nwPerm NW p = benesPerm 12 NW p := by
  unfold nwPerm benesPerm
  refine compF_congr 0 23 (fun s _ hs => ?_) p
  show swp (stageDist s) (nwMask NW s) = swp (stageShift 12 s) (benesMask 12 NW s)
  rw [stageDist_eq s hs, nwMask_eq]

theorem testBit_preP {NW : Nat} (h : CFSG.KLC.Fi22.nwValid NW = true) (X : Nat) {i j : Nat}
    (hi : i < 4096) (hj : j < 4096) :
    (preP NW X).testBit (4096 * i + j) =
      X.testBit (4096 * benesPerm 12 NW i + benesPerm 12 NW j) := by
  have hA : ∀ Y, ∀ u < 4096, ∀ p < 4096,
      (applyNW NW R24 Y).testBit (4096 * u + p) = Y.testBit (4096 * u + nwPerm NW p) :=
    fun Y => (testBit_applyNW h (B := 4096) (R := R24) R24_eq Y).1
  unfold preP
  rw [testBit_tr _ hi hj, hA _ j hj i hi, testBit_tr _ hj (nwPerm_lt h hi),
    hA _ (nwPerm NW i) (nwPerm_lt h hi) j hj, nwPerm_eq, nwPerm_eq]

end CFSG.KC.Fi24Pair

end
