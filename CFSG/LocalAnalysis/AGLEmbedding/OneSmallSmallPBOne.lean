module

public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallSPThree
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallSmallPKFacts

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

section Config

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
  {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}
  {K : Subgroup (H ⧸ primeComplementCore (G := H) p)}

theorem D1OneSmallData.false_of_sp_l34 (hβ : KFactBeta) (hK10 : KFactSmallInvolve)
    (hSch : KFactCatalogSchreier) (hα : KFactAlphaW) (hK3 : KFactAlphaThreeWeak)
    (hJ3 : KFactJ3Involve) (hO : KFactSmallThreeOrders)
    (hd : D1OneSmallData p P M H R Rbar K) {z : G} (hz : D1SmallCZElt p H R K z)
    (hp3 : p = 3) (hL : IsLinThreeFour K) (hSP : D1CzSP p z) : False := by
  subst hp3
  obtain ⟨P', Pbar, KC, -, -, -, hRC⟩ := hd.exists_reducedCentralizer hz hSP
  have hzC : z ∈ Subgroup.centralizer ({z} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr rfl
  obtain ⟨hzZ, hzp⟩ := hRC.center ⟨z, hzC⟩ rfl
  obtain ⟨A, f, hf⟩ := hd.exists_surjective_of_reducedCentralizer hz hRC hSch
  obtain ⟨T₁, -, hs₁, hn₁, hc₁, hT₁nc, hΓ₁, -⟩ := hd.exists_sylow
  by_cases hzK : d1CzElt 3 z ∈ KC
  · have hJ := hRC.red.j3_of_alphaThree_of_mem hRC.four_le_pRank hRC.catalog hzZ hzp hRC.comp
      hRC.normal hzK hα hK3
    exact not_l34_of_a6 hO (hJ3 KC hJ K hs₁ hn₁ hc₁ T₁ hT₁nc hΓ₁ hd.small A f hf) hL
  · obtain ⟨hs, hn, hc, hAut, T, hTnc, hΓ⟩ := hRC.red.exists_sylow_of_not_mem hRC.four_le_pRank
      hRC.catalog hzZ hzp hRC.comp hRC.normal hzK hβ
    exact not_spl_of_l34 hO hL (hK10 KC hs hn hc 3 hd.cfg.red.prime hd.cfg.red.ne_two T hTnc hΓ
      hAut K hs₁ hn₁ hc₁ T₁ hT₁nc hΓ₁ hd.small A f hf)

end Config

end CFSG.AGLEmbedding
