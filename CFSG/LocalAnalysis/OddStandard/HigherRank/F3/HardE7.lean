module

public import CFSG.RankThree.PartOne.Mult.Exceptional
public import CFSG.LocalAnalysis.OddStandard.HigherRank.F3.HardBridge

public section

namespace CFSG.OddStandard.HigherRank.F3

open CFSG CFSG.ComponentClassification.HarrisLit

theorem models_lieModel_E7_of_blueprint (hB : CFSG.TauCetiBridge.Even.ChevalleyBridgesAll)
    {Q : Type} [Group Q] {p f : ℕ} (hp : p.Prime)
    (h : CFSG.Blueprint.LieModel Q .E7 0 p f) : CFSG.Models.LieModel Q .E7 0 p f := by
  have ht : (CFSG.Assembly.LowTwoRank.StatedLieTag.E7) ∈
      CFSG.Blueprint.chevalleyExceptionalTags := by
    decide
  have hc := h.chevalleyExceptionalModel ht
  obtain ⟨d, hd, ⟨e⟩⟩ := CFSG.RankThree.PartOne.Mult.exists_index_of_chevalley hB hp ht hc
  exact ⟨h.admissible, Or.inr ⟨rfl, d, hd, ⟨e⟩⟩⟩

theorem models_lieModel_E7_of_blueprint' {Q : Type} [Group Q] {p f : ℕ} (hp : p.Prime)
    (h : CFSG.Blueprint.LieModel Q .E7 0 p f) : CFSG.Models.LieModel Q .E7 0 p f :=
  models_lieModel_E7_of_blueprint CFSG.TauCetiBridge.Even.chevalleyBridgesAll hp h

theorem hardBranchInput_of_balanced (h : HardBranchBalanced)
    (hGr : CFSG.Open.GriessAllModelsStatement) : HardBranchInputBalanced :=
  hardBranchInput_of_balanced_of_E7 h hGr
    (fun _ _ h => models_lieModel_E7_of_blueprint' Nat.prime_three h)

end CFSG.OddStandard.HigherRank.F3
