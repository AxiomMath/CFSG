module

public import CFSG.LocalAnalysis.AGLEmbedding.ToralCensusHubCenter

public section

namespace CFSG.HardMathSupport.Curtis.NaturalModuleCensus

open CFSG.Open CFSG.AGLEmbedding CFSG.Assembly.LowTwoRank

theorem card_center_eq_one_of_pomegaMinus_four (hGA : CFSG.Open.GriessAllModelsStatement)
    {A : Type} [Group A] [Finite A] [Group.IsPerfect A] {n : ℕ}
    (hm : StatedClassicalModel (A ⧸ Subgroup.center A) .POmegaMinus n 2 2) :
    Nat.card (Subgroup.center A) = 1 := by
  have hm' : CFSG.Models.LieModel _ _ _ _ _ := ⟨hm.1, Or.inl hm⟩
  have h := ToralCensus.card_center_dvd_multiplierOrders hGA (MulEquiv.refl _) hm'
  simp only [CFSG.Blueprint.Multiplier.genericOrders,
    CFSG.Blueprint.Multiplier.exceptionalOrders] at h
  obtain ⟨⟨-, -, hn⟩, -⟩ := hm
  have hg := ToralCensus.genericOrders_fst_eq_one_of_two (t := .POmegaMinus) (n := n) (f := 2)
    (by norm_num) (Or.inr (Or.inr (Or.inl ⟨rfl, by omega⟩)))
  simp only [CFSG.Blueprint.Multiplier.genericOrders] at hg
  rw [hg] at h
  simpa using h

end CFSG.HardMathSupport.Curtis.NaturalModuleCensus
