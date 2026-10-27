module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.ComponentInitial.LinearUnitaryField
public import CFSG.RankThree.PartOne.N143.SectionCover
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.AGLEmbedding.KFactProofs.AlphaFive

open CFSG.RankThree.PartTwo.Sec4.Census CFSG.RankThree.PartOne.N143 CFSG.RankThree.PerfectCover
open CFSG.ComponentClassification.TBLit (GriessMultipliersAllModels)
open CFSG.LocalAnalysis.ComponentInitial (UnitaryFieldData)

theorem isQuasisimple_of_open_five {K : Type} [Group K] (hq : Open.IsQuasisimple K) :
    CFSG.IsQuasisimple K :=
  ⟨⟨hq.1⟩, hq.2, CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian K hq⟩

theorem not_dvd_of_dvd_twelve {p n : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hn : n ∣ 12) :
    ¬ p ∣ n := by
  intro h
  have h12 : p ∣ 12 := h.trans hn
  have : p ≤ 12 := Nat.le_of_dvd (by norm_num) h12
  interval_cases p <;> first | omega | exact absurd hp (by norm_num)

end CFSG.AGLEmbedding.KFactProofs.AlphaFive
