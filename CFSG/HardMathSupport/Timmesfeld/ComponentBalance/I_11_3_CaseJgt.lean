module

public import CFSG.HardMathSupport.Timmesfeld.ComponentBalance.I_11_3_CaseJgtAC
public import CFSG.HardMathSupport.Timmesfeld.ComponentBalance.I_11_3_CaseJgtCount

public section

namespace CFSG.HardMathSupport.Timmesfeld.ComponentBalance

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB

theorem caseJgt113_of_tables (Tb : Tables113) : CaseJgt113 := by
  intro Q _ _ B L x T R hK
  have Tr := R.tri
  obtain ⟨g, hg, t, ht, hM⟩ : ∃ g ∈ B, ∃ t ∈ T, ∀ b ∈ B, GLBConj (g * t) L ≠ GLBConj b L := by
    by_contra hcon
    push Not at hcon
    exact hK (t113_T_le_normalizer_K hcon)
  have hAT := t113_A_centralizes_T R hK
  refine t113_jgt_count Tb Tr R.isL2 R.hmax (g1 := x) (g2 := x ^ 2) (g3 := g * t)
    Tr.conj1_ne Tr.conj2_ne ?_ Tr.conj21_ne.symm ?_ ?_ ?_
  · intro h
    exact hM 1 B.one_mem (by rw [h, gLBConj_one])
  · exact fun h => hM x Tr.mem h.symm
  · exact fun h => hM (x ^ 2) (B.pow_mem Tr.mem 2) h.symm
  · intro a ha
    refine ⟨Tr.comm_B ha.2 Tr.mem, Tr.comm_B ha.2 (B.pow_mem Tr.mem 2), ?_⟩
    calc a * (g * t) = (a * g) * t := by group
      _ = (g * a) * t := by rw [Tr.comm_B ha.2 hg]
      _ = g * (a * t) := by group
      _ = g * (t * a) := by rw [hAT a ha t ht]
      _ = (g * t) * a := by group

end CFSG.HardMathSupport.Timmesfeld.ComponentBalance
