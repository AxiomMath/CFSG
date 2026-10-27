module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_7FinMain
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_7FinMaxL3
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_7FinMaxSp4

public section

namespace CFSG.QuasithinUnique.Fin257

open CFSG.Open

theorem maxRank257 : RankTwoMaxRank257 := by
  intro G _ _ K P K₁ K₂ V V' n hq hM _ hpair hV hV' _ A hAK hAP hAe
  obtain ⟨hn2, hmodel⟩ := hM
  rcases hmodel with hL | hS
  · obtain ⟨F, _, _, hcard, ⟨e⟩⟩ := hL.2
    have : CharP F 2 := LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
      Nat.prime_two (by omega) hcard
    have hdata := L3.modelData_L3 (F := F) hn2 hcard
    obtain ⟨π, R₁', R₂', hswap, hred⟩ :=
      reduce257 hq hdata (e.trans (statedSLEquiv F)) hpair hV hV'
    have hMR : MaxRankModel _ (LocalAnalysis.ComponentInitial.LinearFlag.projUnitriangular 3 F)
        R₁' R₂' := by
      rcases hswap with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact L3.maxRankModel_L3 hn2 hcard
      · exact (L3.maxRankModel_L3 hn2 hcard).symm L3.card_V1_eq_card_V2
    exact maxRank_of_red hq hred hMR A hAK hAP hAe
  · obtain ⟨F, _, _, hcard, ⟨e⟩⟩ := hS.2
    have : CharP F 2 := LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
      Nat.prime_two (by omega) hcard
    have hdata := Sp4.modelData_Sp (K := F) hn2 hcard
    obtain ⟨π, R₁', R₂', hswap, hred⟩ :=
      reduce257 hq hdata (e.trans (QuasithinUnique.Setup.X7b.antiProjEquiv F).symm) hpair hV hV'
    obtain ⟨-, h1, h2, -⟩ := QuasithinUnique.Setup.X7b.card_radicals (K := F)
    have hMR : MaxRankModel _ (ComponentClassification.UnbalancedCatalog.SpChain.antiUnipotent F)
        R₁' R₂' := by
      rcases hswap with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact Sp4.maxRankModel_Sp hn2 hcard
      · exact (Sp4.maxRankModel_Sp hn2 hcard).symm (h1.trans h2.symm)
    exact maxRank_of_red hq hred hMR A hAK hAP hAe

end CFSG.QuasithinUnique.Fin257
