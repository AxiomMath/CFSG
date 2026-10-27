module

public import Certificates.Data.Kernel.GammaUFpfThreeK

public section

namespace CFSG.KC.GUK

open CFSG.GF2Type.Smith1979.GammaU CFSG.GF2Type.Smith1979.GammaU.SigmaP

theorem combo_eq : combo = comboK := by
  funext L m
  induction L generalizing m with
  | nil => rfl
  | cons a L ih =>
    change (if m % 2 = 1 then a else 0) ^^^ combo L (m / 2) =
      Nat.xor (bif Nat.beq (Nat.land m 1) 1 then a else 0) (comboK L (Nat.shiftRight m 1))
    have h1 : Nat.land m 1 = m % 2 := Nat.and_one_is_mod m
    have h2 : Nat.shiftRight m 1 = m / 2 := (Nat.shiftRight_eq_div_pow m 1).trans (by norm_num)
    rw [ih, h1, h2]
    by_cases hm : m % 2 = 1
    · rw [if_pos hm, hm]
      rfl
    · have hb : Nat.beq (m % 2) 1 = false := Bool.eq_false_iff.2 fun h => hm (Nat.eq_of_beq_eq_true h)
      rw [if_neg hm, hb]
      rfl

theorem f0b_eq : f0b = f0K := by
  funext m n
  simp only [f0b, f0K, par6, List.range_succ, List.range_zero, List.nil_append, List.foldl_append,
    List.foldl_cons, List.foldl_nil, Nat.testBit_xor, Nat.testBit_and, Nat.testBit_shiftRight]

theorem bitM_eq (M y : Nat) : bitM M y = M.testBit y := by
  have h1 : Nat.land (Nat.shiftRight M y) 1 = M / 2 ^ y % 2 := by
    rw [← Nat.shiftRight_eq_div_pow]
    exact Nat.and_one_is_mod _
  rw [bitM, h1, Nat.testBit_eq_decide_div_mod_eq]
  apply Bool.eq_iff_iff.2
  simp [Nat.beq_eq]

theorem testBit_maskL : ∀ (L : List Nat) (y : Nat), (maskL L).testBit y = L.contains y
  | [], y => by
    change (0 : Nat).testBit y = false
    simp
  | a :: L, y => by
    have h : maskL (a :: L) = 2 ^ a ||| maskL L := by
      change Nat.lor (Nat.shiftLeft 1 a) (maskL L) = _
      rw [← Nat.one_shiftLeft]
      rfl
    rw [h, Nat.testBit_or, Nat.testBit_two_pow, testBit_maskL L y, List.contains_cons]
    by_cases hy : y = a
    · subst hy
      simp
    · have hy' : a ≠ y := Ne.symm hy
      simp [hy, hy']

theorem bitM_maskL (L : List Nat) (y : Nat) : bitM (maskL L) y = L.contains y := by
  rw [bitM_eq, testBit_maskL]

theorem kHead_eq : kHead = headK := by
  funext b B6 S CS SB SP
  simp only [kHead, headK, combo_eq, f0b_eq]

theorem kTripleOK_eq {B6 S : List ℕ} {SM : ℕ} (hS : ∀ y, S.contains y = bitM SM y)
    (CS : List (ℕ × ℕ)) (b u : List ℕ) : kTripleOK B6 S CS b u = tripleK B6 SM CS b u := by
  simp only [kTripleOK, tripleK, combo_eq, hS]

theorem kTriples_eq {B6 S : List ℕ} {SM : ℕ} (hS : ∀ y, S.contains y = bitM SM y)
    (CS : List (ℕ × ℕ)) (b : List ℕ) : kTriples B6 S CS b = triplesK B6 S S SM CS b := by
  simp only [kTriples, triplesK, kTripleOK_eq hS]

theorem triplesK_append (B6 S U V : List ℕ) (SM : ℕ) (CS : List (ℕ × ℕ)) (b : List ℕ) :
    triplesK B6 S (U ++ V) SM CS b = (triplesK B6 S U SM CS b && triplesK B6 S V SM CS b) := by
  simp only [triplesK, List.all_append]

end CFSG.KC.GUK

end
