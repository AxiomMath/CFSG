module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.MaximalityAmbient.KNormalizer
public import Certificates.Certificate12633

public section

set_option linter.unusedSectionVars false

namespace CFSG.AGLEmbeddingD2.Wilson.MaximalityAmbient.KCheck

open CFSG.Sporadic.J4 CFSG.Sporadic.J4.Native CFSG.Sporadic.J4.QT CFSG.Sporadic.J4.QT2A
  CFSG.Quasithin.J4M2 CFSG.Quasithin.J4Loc CFSG.AGLEmbeddingD2.Wilson.Coordinator

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem chkComm_parts {n : ℕ} (hn : n < 24576) :
    wfR kTab[n]! = true ∧ wfR (rightC kTab[n]!) = true ∧ wfR (leftC kTab[n]!) = true ∧
      (eqRows (rightC kTab[n]!) (leftC kTab[n]!) = true → (decodeF n).2.1 = 0) := by
  have h := Certificates.certificate12633
  unfold chkComm at h
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range] at h
  obtain ⟨-, h⟩ := h
  have h1 := h n hn
  simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true', decide_eq_true_eq] at h1
  obtain ⟨⟨⟨h2, h3⟩, h4⟩, h5⟩ := h1
  refine ⟨h2, h3, h4, fun he => ?_⟩
  rcases h5 with h5 | h5
  · rw [he] at h5
    exact absurd h5 (by simp)
  · exact h5

section Mats

variable
  (hM : MatFacts)
include hM

theorem Kgrp_centralizer_cE :
    ∀ k ∈ Kgrp, k * cE = cE * k → ∃ e : Bool, ∃ i < 3, k = (if e then z0 else 1) * cE ^ i := by
  intro k hk hcomm
  obtain ⟨n, hn, rfl⟩ := Kgrp_le_Sform hM k hk
  obtain ⟨hw, hw1, hw2, himp⟩ := chkComm_parts hn
  have hg : Mx (kElt (decodeF n)) = rowsMatrix kTab[n]! := by
    rw [Mx_kElt hM, kTab_getElem hn]
  have h1 : rowsMatrix (rightC kTab[n]!) = rowsMatrix (leftC kTab[n]!) := by
    unfold rightC leftC
    rw [cTab, rowsMatrix_mulT_frTable, rowsMatrix_mulT_frTable, ← hg, ← Mx_cE hM, ← map_mul,
      ← map_mul, hcomm]
  have hc : (decodeF n).2.1 = 0 := himp (eqRows_iff.2 (eq_of_rowsMatrix_eq' hw1 hw2 h1))
  refine ⟨(decodeF n).1, (decodeF n).2.2, ?_, ?_⟩
  · simp only [decodeF]
    omega
  · unfold kElt qNF
    rw [hc, eta_zero, mul_one]

end Mats

end CFSG.AGLEmbeddingD2.Wilson.MaximalityAmbient.KCheck
