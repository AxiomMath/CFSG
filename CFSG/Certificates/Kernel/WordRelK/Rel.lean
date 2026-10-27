
module

public import CFSG.Certificates.Kernel.WordRelK.Sound
public import CFSG.Monster.B.TwoA.Sp8.P0WordsBase

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.KC.WordRelK

open CFSG.Monster.B CFSG.Monster.B.TwoA.Sp8 CFSG.Monster.B.TwoA.Sp8.WordRel
  CFSG.ComponentClassification.RankTwoSporadic.B.TwoDFix

theorem tWord_zero : tWord 0 = [] := by decide

theorem lWord_zero : lWord 0 = [] := by decide

variable
  {T : Nat}

theorem wordX_eq_of_relT (hT : ∀ r < 52, tabOK T r = true) {w w' : List XLetter}
    (h : relT T w w' = true) : wordX w = wordX w' :=
  wordX_eq_of_relCheck (relCheck_of_relT hT h)

private theorem tD_mul_self (τ : Nat) : wordX (tWord τ) * wordX (tWord τ) = 1 := by
  have h := tD_xor τ τ
  rw [Nat.xor_self] at h
  change tD τ * tD τ = 1
  rw [← h]
  change wordX (tWord 0) = 1
  rw [tWord_zero]
  rfl

theorem lComm_wordX (hT : ∀ r < 52, tabOK T r = true) (hrow : ∀ i < 16, lCommRowT T i = true)
    (hsym : lCommSymOK = true) {i j : Nat} (hi : i < 16) (hj : j < 16) :
    wordX (lWord (2 ^ i) ++ lWord (2 ^ j)) =
      wordX (lWord (2 ^ j) ++ lWord (2 ^ i) ++ tWord ((lCommN.getD i []).getD j 0)) := by
  have hs := allBelow_true hsym
  have hpos : ∀ {i j : Nat}, i < 16 → j < 16 → i < j →
      wordX (lWord (2 ^ i) ++ lWord (2 ^ j)) =
        wordX (lWord (2 ^ j) ++ lWord (2 ^ i) ++ tWord ((lCommN.getD i []).getD j 0)) := by
    intro i j hi hj hij
    have h := allBelow_true (hrow i hi) j hj
    have hb : Nat.blt i j = true := by rw [Nat.blt_eq]; exact hij
    simp only [hb, cond_true] at h
    exact wordX_eq_of_relT hT h
  have hrow_i := hs i hi
  rw [Bool.and_eq_true] at hrow_i
  rcases Nat.lt_trichotomy i j with h | rfl | h
  · exact hpos hi hj h
  · rw [Nat.eq_of_beq_eq_true hrow_i.1, tWord_zero, List.append_nil]
  · have e := hpos hj hi h
    rw [Nat.eq_of_beq_eq_true (allBelow_true hrow_i.2 j hj)]
    simp only [wordX_append] at e ⊢
    rw [e, mul_assoc, tD_mul_self, mul_one]

theorem lSq_wordX (hT : ∀ r < 52, tabOK T r = true) (hrow : ∀ i < 16, lSqT T i = true)
    {i : Nat} (hi : i < 16) : wordX (lWord (2 ^ i) ++ lWord (2 ^ i)) = 1 :=
  wordX_eq_of_relT hT (hrow i hi)

theorem uConjL_wordX (hT : ∀ r < 52, tabOK T r = true) (hrow : ∀ k < 10, uConjLRowT T k = true)
    {k j : Nat} (hk : k < 10) (hj : j < 16) :
    wordX (uWord k ++ lWord (2 ^ j)) =
      wordX (lWord ((uConjLN.getD k []).getD j (0, 0)).1 ++
        tWord ((uConjLN.getD k []).getD j (0, 0)).2 ++ uWord k) :=
  wordX_eq_of_relT hT (allBelow_true (hrow k hk) j hj)

theorem uConjT_wordX (hT : ∀ r < 52, tabOK T r = true) (hrow : ∀ k < 10, uConjTRowT T k = true)
    {k j : Nat} (hk : k < 10) (hj : j < 9) :
    wordX (uWord k ++ tWord (2 ^ j)) = wordX (tWord ((uConjTN.getD k []).getD j 0) ++ uWord k) :=
  wordX_eq_of_relT hT (allBelow_true (hrow k hk) j hj)

theorem uSq_wordX (hT : ∀ r < 52, tabOK T r = true) (hrow : ∀ k < 10, uSqT T k = true)
    {k : Nat} (hk : k < 10) :
    wordX (uWord k ++ uWord k) = wordX (lWord (uSqN.getD k (0, 0)).1 ++ tWord (uSqN.getD k (0, 0)).2) :=
  wordX_eq_of_relT hT (hrow k hk)

theorem uComm_wordX (hT : ∀ r < 52, tabOK T r = true) (hrow : ∀ j < 10, uCommRowT T j = true)
    (hdiag : uCommDiagOK = true) {j k : Nat} (hj : j < 10) (hk : k < 10) :
    wordX (uWord j ++ uWord k) =
      wordX (lWord ((uCommN.getD j []).getD k (0, 0)).1 ++
        tWord ((uCommN.getD j []).getD k (0, 0)).2 ++ uWord k ++ uWord j) := by
  by_cases hjk : j = k
  · subst hjk
    rw [beq_iff_eq.1 (allBelow_true hdiag j hj), lWord_zero, tWord_zero, List.nil_append,
      List.nil_append]
  · have h := allBelow_true (hrow j hj) k hk
    have hb : Nat.beq j k = false := Bool.eq_false_iff.2 (by rw [Ne, Nat.beq_eq]; exact hjk)
    simp only [hb, cond_false] at h
    exact wordX_eq_of_relT hT h

theorem coDec_wordX (hT : ∀ r < 52, tabOK T r = true) (hrow : ∀ i < 9, coDecT T i = true)
    {i : Nat} (hi : i < 9) :
    wordX ((coGens.getD i []).map .lift) =
      wordX (lWord (coDecN.getD i (0, 0)).1 ++ tWord (coDecN.getD i (0, 0)).2) :=
  wordX_eq_of_relT hT (hrow i hi)

theorem paDec_wordX (hT : ∀ r < 52, tabOK T r = true) (hrow : ∀ i < 15, paDecT T i = true)
    {i : Nat} (hi : i < 15) :
    wordX ((pauliWords.getD i []).map .lift) =
      wordX (lWord (paDecN.getD i (0, 0)).1 ++ tWord (paDecN.getD i (0, 0)).2) :=
  wordX_eq_of_relT hT (hrow i hi)

end CFSG.KC.WordRelK
