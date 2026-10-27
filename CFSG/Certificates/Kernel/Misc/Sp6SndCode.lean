module

public import CFSG.Certificates.Kernel.Misc.Sp6SndLin
public import CFSG.LocalAnalysis.ComponentInitial.ChevSp6EpsOneOqDataKill

public section

namespace CFSG.KC.Misc.Sp6.Snd

open CFSG.KC.Ord CFSG.KC.LQT.P CFSG.KC.Misc CFSG.KC.Misc.O62 CFSG.KC.Misc.Sp6
open CFSG.LocalAnalysis.ComponentInitial.ChevSp6EpsOne

private theorem imgK_eq' (A j : ℕ) : imgK A j = A / 2 ^ (6 * (5 - j)) % 64 := by
  have h := Nat.and_two_pow_sub_one_eq_mod (A >>> (6 * (5 - j))) 6
  rw [Nat.shiftRight_eq_div_pow] at h
  have e : imgK A j = (A >>> (6 * (5 - j))) &&& 2 ^ 6 - 1 := rfl
  rw [e, Nat.shiftRight_eq_div_pow]
  exact h

private theorem dec_eq (A : ℕ) :
    dec A = [imgK A 0, imgK A 1, imgK A 2, imgK A 3, imgK A 4, imgK A 5] := by
  simp [dec, List.range_succ]

private theorem codeL6 (a b c d e f : ℕ) :
    codeL [a, b, c, d, e, f] = ((((a * 64 + b) * 64 + c) * 64 + d) * 64 + e) * 64 + f := by
  show Nat.add (Nat.mul 64 (Nat.add (Nat.mul 64 (Nat.add (Nat.mul 64 (Nat.add (Nat.mul 64
    (Nat.add (Nat.mul 64 (Nat.add (Nat.mul 64 0) a)) b)) c)) d)) e)) f = _
  simp only [Nat.add_eq, Nat.mul_eq]
  omega

private theorem imgK_vals (A : ℕ) :
    imgK A 0 = A / 2 ^ 30 % 64 ∧ imgK A 1 = A / 2 ^ 24 % 64 ∧ imgK A 2 = A / 2 ^ 18 % 64 ∧
    imgK A 3 = A / 2 ^ 12 % 64 ∧ imgK A 4 = A / 2 ^ 6 % 64 ∧ imgK A 5 = A % 64 := by
  refine ⟨imgK_eq' A 0, imgK_eq' A 1, imgK_eq' A 2, imgK_eq' A 3, imgK_eq' A 4, ?_⟩
  simpa using imgK_eq' A 5

private theorem tup_cases {l : List ℕ} (h : IsTup l) :
    ∃ a b c d e f, l = [a, b, c, d, e, f] ∧ a < 64 ∧ b < 64 ∧ c < 64 ∧ d < 64 ∧ e < 64 ∧
      f < 64 := by
  obtain ⟨h1, h2⟩ := h
  match l, h1, h2 with
  | [a, b, c, d, e, f], _, h2 =>
    simp only [List.mem_cons, forall_eq_or_imp, List.not_mem_nil, or_false, forall_eq] at h2
    exact ⟨a, b, c, d, e, f, rfl, h2⟩

theorem dec_codeL {l : List ℕ} (h : IsTup l) : dec (codeL l) = l := by
  obtain ⟨a, b, c, d, e, f, rfl, ha, hb, hc, hd, he, hf⟩ := tup_cases h
  obtain ⟨i0, i1, i2, i3, i4, i5⟩ := imgK_vals (codeL [a, b, c, d, e, f])
  rw [dec_eq, i0, i1, i2, i3, i4, i5, codeL6]
  simp only [List.cons.injEq]
  refine ⟨by omega, by omega, by omega, by omega, by omega, by omega, trivial⟩

theorem codeL_dec {A : ℕ} (h : A < 2 ^ 36) : codeL (dec A) = A := by
  obtain ⟨i0, i1, i2, i3, i4, i5⟩ := imgK_vals A
  rw [dec_eq, i0, i1, i2, i3, i4, i5, codeL6]
  omega

theorem codeL_inj {l l' : List ℕ} (h : IsTup l) (h' : IsTup l') (e : codeL l = codeL l') :
    l = l' := by
  rw [← dec_codeL h, ← dec_codeL h', e]

theorem idK_eq : idK = codeL idT := by
  show idK = codeL [1, 2, 4, 8, 16, 32]
  rw [codeL6]
  show (1108378656 : ℕ) = _
  omega

theorem dec_idK : dec idK = idT := by
  rw [idK_eq]
  exact dec_codeL idT_tup

private theorem lorM (P Q n : ℕ) (hP : P % 2 ^ n = 0) (hQ : Q < 2 ^ n) : P ||| Q = P + Q := by
  have h : P = (P / 2 ^ n) <<< n := by
    rw [Nat.shiftLeft_eq]; exact (Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero hP)).symm
  calc P ||| Q = ((P / 2 ^ n) <<< n) ||| Q := by rw [← h]
    _ = (P / 2 ^ n) <<< n + Q := (Nat.shiftLeft_add_eq_or_of_lt hQ _).symm
    _ = P + Q := by rw [← h]

theorem compK_eq (A B : ℕ) : compK A B = codeL (compT (dec A) (dec B)) := by
  have key : ∀ j, actT (tLo A) (tHi A) (imgK B j) = evalV (dec A) (imgK B j) :=
    fun j => actT_eq A (imgK_lt B j)
  have hl : ∀ x ∈ dec A, x < 64 := (dec_tup A).2
  have hc : compT (dec A) (dec B) = [evalV (dec A) (imgK B 0), evalV (dec A) (imgK B 1),
      evalV (dec A) (imgK B 2), evalV (dec A) (imgK B 3), evalV (dec A) (imgK B 4),
      evalV (dec A) (imgK B 5)] := by
    rw [compT, dec_eq B]; rfl
  rw [hc, codeL6]
  simp only [compK, letN_eq, key]
  have b0 := evalV_lt' hl (imgK B 0)
  have b1 := evalV_lt' hl (imgK B 1)
  have b2 := evalV_lt' hl (imgK B 2)
  have b3 := evalV_lt' hl (imgK B 3)
  have b4 := evalV_lt' hl (imgK B 4)
  have b5 := evalV_lt' hl (imgK B 5)
  generalize evalV (dec A) (imgK B 0) = x0 at *
  generalize evalV (dec A) (imgK B 1) = x1 at *
  generalize evalV (dec A) (imgK B 2) = x2 at *
  generalize evalV (dec A) (imgK B 3) = x3 at *
  generalize evalV (dec A) (imgK B 4) = x4 at *
  generalize evalV (dec A) (imgK B 5) = x5 at *
  show ((x0 <<< 30 ||| x1 <<< 24) ||| (x2 <<< 18 ||| x3 <<< 12)) ||| (x4 <<< 6 ||| x5) = _
  have e1 := lorM (x4 <<< 6) x5 6 (by simp only [Nat.shiftLeft_eq]; omega)
    (by omega)
  have e2 := lorM (x2 <<< 18) (x3 <<< 12) 18 (by simp only [Nat.shiftLeft_eq]; omega)
    (by simp only [Nat.shiftLeft_eq]; omega)
  have e3 := lorM (x0 <<< 30) (x1 <<< 24) 30 (by simp only [Nat.shiftLeft_eq]; omega)
    (by simp only [Nat.shiftLeft_eq]; omega)
  have e4 := lorM (x0 <<< 30 + x1 <<< 24) (x2 <<< 18 + x3 <<< 12) 24
    (by simp only [Nat.shiftLeft_eq]; omega) (by simp only [Nat.shiftLeft_eq]; omega)
  have e5 := lorM (x0 <<< 30 + x1 <<< 24 + (x2 <<< 18 + x3 <<< 12)) (x4 <<< 6 + x5) 12
    (by simp only [Nat.shiftLeft_eq]; omega) (by simp only [Nat.shiftLeft_eq]; omega)
  rw [e1, e2, e3, e4, e5]
  simp only [Nat.shiftLeft_eq]
  omega

theorem invK_eq {A : ℕ} (hA : A < 2 ^ 36) : invK A = isInvT (dec A) := by
  have hc : compK A A = codeL (compT (dec A) (dec A)) := compK_eq A A
  have h1 : compK A A = idK ↔ compT (dec A) (dec A) = idT := by
    rw [hc, idK_eq]
    exact ⟨codeL_inj (compT_tup (dec_tup A).2 (dec_tup A)) idT_tup, fun h => by rw [h]⟩
  have h2 : A = idK ↔ dec A = idT := by
    constructor
    · intro h; rw [h]; exact dec_idK
    · intro h; rw [← codeL_dec hA, h, idK_eq]
  apply Bool.eq_iff_iff.2
  simp only [invK, isInvT, andB_eq_true, notB_eq_true, Bool.and_eq_true, beq_iff_eq, bne_iff_ne,
    ne_eq, Nat.beq_eq, Bool.not_eq_true]
  have h3 : A.beq idK = false ↔ ¬ A = idK := by
    rw [← Bool.not_eq_true]; simp [Nat.beq_eq]
  rw [h1, h3, h2]

end CFSG.KC.Misc.Sp6.Snd

end
