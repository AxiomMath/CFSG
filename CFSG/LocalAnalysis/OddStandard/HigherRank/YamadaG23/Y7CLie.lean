module

public import CFSG.Open.StatedZModTwo
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P54Odd

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open CFSG.Open CFSG.Blueprint

theorem y7c_lieModel_gl3 :
    LieModel (Matrix.GeneralLinearGroup (Fin 3) (ZMod 2)) .PSL 3 2 1 := by
  refine Or.inl ⟨by decide, ?_⟩
  refine StatedAPI.statedClassicalModel_psl_of_mulEquiv_statedSL_zmod_two (n := 3) (by norm_num) ?_
  have h : StatedSL 3 (ZMod 2) = ⊤ := StatedAPI.statedSL_eq_top_of_card_two (by simp) 3
  exact Subgroup.topEquiv.symm.trans (MulEquiv.subgroupCongr h.symm)

theorem y7c_hopf_gl3_dvd_two
    (hG : ComponentClassification.HarrisLit.T1.P54.GriessNativeTable) :
    Nat.card (griessHopfMultiplier (Matrix.GeneralLinearGroup (Fin 3) (ZMod 2))) ∣ 2 := by
  obtain ⟨-, ⟨e⟩⟩ := hG _ .PSL 3 2 1 y7c_lieModel_gl3
  rw [Nat.card_congr e.toEquiv,
    ComponentClassification.HarrisLit.T1.P54.card_generic_prod_exceptional]
  decide

end CFSG.OddStandard.HigherRank.YamadaG23
