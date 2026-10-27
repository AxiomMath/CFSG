module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenEightPairJShape
import CFSG.GH74.Generic.GKFCover
import CFSG.LieType.Multipliers.U42
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanBlockCycSU
public import CFSG.RankThree.PerfectCover.HopfFormula

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TenEight

open CFSG.Assembly.LowTwoRank

section Cover

theorem card_hopfMultiplier_of_model_psu_four_two {Y : Type} [Group Y]
    (h : StatedClassicalModel Y .PSU 4 2 1) :
    Nat.card (CFSG.RankThree.PerfectCover.hopfMultiplier Y) = 2 := by
  have hY : CFSG.Blueprint.LieModel Y .PSU 4 2 1 := .inl ⟨by decide, h⟩
  obtain ⟨-, ⟨e⟩⟩ := CFSG.LieType.Multipliers.U42.multiplier_PSU_four_two Y hY
  rw [← Nat.card_congr (CFSG.RankThree.PerfectCover.hopfMultiplierEquivGriess Y).toEquiv,
    Nat.card_congr e.toEquiv, Nat.card_congr (Multiplicative.toAdd : _ ≃ ZMod 2), Nat.card_zmod]

theorem u42Facts_of_model_psu_four_two {Y : Type} [Group Y]
    (h : StatedClassicalModel Y .PSU 4 2 1) : U42Facts Y := by
  refine ⟨CFSG.AGLEmbedding.BlockCyc.hasE9_of_model_psu h (by norm_num), ?_⟩
  intro Z _ _ hZ hodd ⟨e⟩
  have hperf : Group.IsPerfect Z := Group.isPerfect_def.2 hZ.1
  have hdvd := CFSG.GH74.Generic.card_ker_dvd_hopfMultiplier hperf
    (CFSG.GH74.Generic.centralQuotientMap e) (CFSG.GH74.Generic.centralQuotientMap_surjective e)
    (CFSG.GH74.Generic.centralQuotientMap_ker e).le
  rw [CFSG.GH74.Generic.centralQuotientMap_ker e,
    card_hopfMultiplier_of_model_psu_four_two h] at hdvd
  have hle : Nat.card (Subgroup.center Z) ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
  obtain ⟨k, hk⟩ := hodd
  exact Subgroup.eq_bot_of_card_eq _ (by omega)

end Cover

end CFSG.LocalAnalysis.RankThreeTheoremC.TenEight
