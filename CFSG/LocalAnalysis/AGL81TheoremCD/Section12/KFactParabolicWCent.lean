module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ParabCommGeneric

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section12

open CFSG.Open CFSG.AGLEmbedding

@[expose] def KFactParabolicWCentSolvable : Prop :=
  ∀ (A : Type) [Group A] [Finite A] (Y P B : Subgroup A), Open.IsQuasisimple ↥Y →
    pCoreOf 2 Y = ⊥ → IsClassicalTwoOrG2 (↥Y ⧸ Subgroup.center ↥Y) → IsParabolicTwo Y P →
    B ≤ Subgroup.normalizer (Y : Set A) → B ≤ Subgroup.normalizer (P : Set A) →
    (∀ b ∈ B, CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.ParabComm.WCent P b) →
    ∀ R : Subgroup A, R ≤ B → ⁅R, R⁆ = R → ∀ r ∈ R, ∀ y ∈ Y, r * y = y * r

end CFSG.LocalAnalysis.AGL81TheoremCD.Section12
