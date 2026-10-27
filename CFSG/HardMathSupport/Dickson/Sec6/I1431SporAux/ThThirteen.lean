module

public import CFSG.HardMathSupport.Dickson.Sec6.I1431SporAux.FixOrder13
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThSlp
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThCentSound
public import CFSG.Sporadic.Th.Max3.AllConjFinal
public import Certificates.Certificate17402

public section

namespace CFSG.HardMathSupport.Dickson.Sec6.I1431

open CFSG.Open CFSG.Blueprint CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.SectionRank.Native
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThSlp
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThCent
  CFSG.HardMathSupport.Dickson.Sec6.I1431.ThThirteenNative

section Th


@[expose] noncomputable def y13J : J := wordG (pairLetters xJ yJ) y13Word

@[expose] noncomputable def g13J : J := wordG (pairLetters xJ yJ) g13Word

theorem th13_facts : orderOf y13J = 13 ∧ y13J * g13J = g13J * y13J ^ 2 := by
  have h := Certificates.certificate17402
  unfold th13OK at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  have hY : rowsMatrix (y13Rows ()) = matJ y13J := by
    unfold y13Rows y13J
    exact rowsMatrix_wordRows rowsMatrix_xRows rowsMatrix_yRows x_sq_kernel y_cube_kernel
      y13Word
  have hG : rowsMatrix (g13Rows ()) = matJ g13J := by
    unfold g13Rows g13J
    exact rowsMatrix_wordRows rowsMatrix_xRows rowsMatrix_yRows x_sq_kernel y_cube_kernel
      g13Word
  have hid : rowsMatrix idRows = matJ (1 : J) := by rw [rowsMatrix_idRows, matJ_one]
  have hpow : y13J ^ 13 = 1 := by
    refine eq_of_rowsMatrix_eq (g := y13J ^ 13) (h := 1) ?_ hid h1
    rw [rowsMatrix_powRowsN, hY, matJ_pow]
  have hne : y13J ≠ 1 := ne_of_rowsDiffer hY hid h2
  have : Fact (Nat.Prime 13) := ⟨by norm_num⟩
  refine ⟨orderOf_eq_prime hpow hne, ?_⟩
  refine eq_of_rowsMatrix_eq (g := y13J * g13J) (h := g13J * y13J ^ 2) ?_ ?_ h3
  · rw [rowsMatrix_mulRows, hY, hG, matJ_mul]
  · rw [rowsMatrix_mulRows, rowsMatrix_powRowsN, hG, hY, matJ_mul, matJ_pow]

theorem th_thirteen_card_J : 13 * Nat.card {h : J // orderOf h = 13} ≤ Nat.card J := by
  obtain ⟨ho, hrel⟩ := th13_facts
  have : Finite J := Nat.finite_of_card_ne_zero (by rw [CFSG.Sporadic.Th.Max3.natCard_J]; norm_num)
  have hH : ¬ 13 ^ 2 ∣ Nat.card J := by
    rw [CFSG.Sporadic.Th.Max3.natCard_J]
    norm_num
  refine thirteen_mul_card_orderOf_le hH ho (g := (g13J)⁻¹) ?_
  calc (g13J)⁻¹ * y13J * ((g13J)⁻¹)⁻¹ = (g13J)⁻¹ * (y13J * g13J) := by group
    _ = (g13J)⁻¹ * (g13J * y13J ^ 2) := by rw [hrel]
    _ = y13J ^ 2 := by group

theorem th_thirteen_card :
    13 * Nat.card {h : NativeSporadic.Th // orderOf h = 13} ≤ Nat.card NativeSporadic.Th := by
  have h := th_thirteen_card_J
  have e1 := @card_orderOf_thirteen_congr NativeSporadic.Th J _ _ CFSG.Sporadic.Th.thEquivJ
  have e2 := Nat.card_congr (CFSG.Sporadic.Th.thEquivJ).toEquiv
  calc 13 * Nat.card {h : NativeSporadic.Th // orderOf h = 13} =
        13 * Nat.card {h : J // orderOf h = 13} := by rw [e1]
    _ ≤ Nat.card J := h
    _ = Nat.card NativeSporadic.Th := e2.symm

end Th

end CFSG.HardMathSupport.Dickson.Sec6.I1431
