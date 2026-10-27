module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongOFRCExcRed
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongOFRCDescG2
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongOFRCDescF4
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongOFRCDescE
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongOFRCLin
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongOFRCUni
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongOFRCSp
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongOFRCOrthOdd
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongOFRCOrthPlus
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongOFRCOrthMinus
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongOFRCSuzTits

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KD291OL

open CFSG.Assembly.LowTwoRank (StatedLieTag StatedLieAdmissible)
open CFSG.Blueprint CFSG.Blueprint.Chevalley

section


theorem untwDescent_G2 : UntwDescent .G2 Tag.G2 := by
  intro ℓ f p hℓ hp hp5 hne hadm K _ _ hK α hαp hα
  obtain ⟨-, hf, -, h3⟩ := hadm
  exact descent_fixed_adjoint_G2 hℓ hf hp hp5 hne K hK h3 α hαp hα

theorem untwDescent_F4 : UntwDescent .F4 Tag.F4 := by
  intro ℓ f p hℓ hp hp5 hne hadm K _ _ hK α hαp hα
  obtain ⟨-, hf, -⟩ := hadm
  exact descent_fixed_adjoint_F4 hℓ hf hp hp5 hne K hK α hαp hα

theorem untwDescent_E {t : StatedLieTag} {τ : Tag} (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    (hadm : ∀ {ℓ f : ℕ}, StatedLieAdmissible t 0 ℓ f → 1 ≤ f) : UntwDescent t τ := by
  intro ℓ f p hℓ hp hp5 hne hadm' K _ _ hK α hαp hα
  exact descent_fixed_adjoint_E hτ hℓ (hadm hadm') hp hp5 hne K hK α hαp hα

theorem outerFixedRankCrossAt_G2_of_step (h : UntwCrossRankStep Tag.G2) :
    OuterFixedRankCrossAt .G2 :=
  outerFixedRankCrossAt_of_untwStep (fun K _ ℓ f hm => hm.2) (by decide) untwDescent_G2 h

theorem outerFixedRankCrossAt_F4_of_step
    (h : UntwCrossRankStep Tag.F4) : OuterFixedRankCrossAt .F4 :=
  outerFixedRankCrossAt_of_untwStep (fun K _ ℓ f hm => hm.2) (by decide) untwDescent_F4 h

theorem outerFixedRankCrossAt_E6_of_step (h : UntwCrossRankStep Tag.E6) :
    OuterFixedRankCrossAt .E6 :=
  outerFixedRankCrossAt_of_untwStep (fun K _ ℓ f hm => hm.2) (by decide)
    (untwDescent_E (Or.inl rfl) fun h => h.2.1) h

theorem outerFixedRankCrossAt_E7_of_step (h : UntwCrossRankStep Tag.E7) :
    OuterFixedRankCrossAt .E7 :=
  outerFixedRankCrossAt_of_untwStep (fun K _ ℓ f hm => hm.2) (by decide)
    (untwDescent_E (Or.inr (Or.inl rfl)) fun h => h.2.1) h

theorem outerFixedRankCrossAt_E8_of_step (h : UntwCrossRankStep Tag.E8) :
    OuterFixedRankCrossAt .E8 :=
  outerFixedRankCrossAt_of_untwStep (fun K _ ℓ f hm => hm.2) (by decide)
    (untwDescent_E (Or.inr (Or.inr rfl)) fun h => h.2.1) h

theorem outerFixedRankCross_holds_of
    (hExc : ∀ t, IsExceptionalTag t → ExcCrossRankStepAt t) : ∀ t, OuterFixedRankCrossAt t := by
  intro t
  cases t
  · exact outerFixedRankCrossAt_PSL
  · exact outerFixedRankCrossAt_PSU
  · exact outerFixedRankCrossAt_PSp
  · exact outerFixedRankCrossAt_POmegaOdd
  · exact outerFixedRankCrossAt_POmegaPlus
  · exact outerFixedRankCrossAt_POmegaMinus
  · exact outerFixedRankCrossAt_G2_of_step (hExc .G2 (by simp [IsExceptionalTag]))
  · exact outerFixedRankCrossAt_F4_of_step (hExc .F4 (by simp [IsExceptionalTag]))
  · exact outerFixedRankCrossAt_E6_of_step (hExc .E6 (by simp [IsExceptionalTag]))
  · exact outerFixedRankCrossAt_E7_of_step (hExc .E7 (by simp [IsExceptionalTag]))
  · exact outerFixedRankCrossAt_E8_of_step (hExc .E8 (by simp [IsExceptionalTag]))
  · exact hExc .twistedE6 (by simp [IsExceptionalTag])
  · exact hExc .trialityD4 (by simp [IsExceptionalTag])
  · exact outerFixedRankCrossAt_twistedB2
  · exact hExc .twistedG2 (by simp [IsExceptionalTag])
  · exact hExc .twistedF4 (by simp [IsExceptionalTag])
  · exact outerFixedRankCrossAt_Tits

end

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KD291OL
