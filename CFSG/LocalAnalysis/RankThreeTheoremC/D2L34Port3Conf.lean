module

public import CFSG.LocalAnalysis.RankThreeTheoremC.D2L34Port3Defs
public import CFSG.LocalAnalysis.RankThreeTheoremC.D2PairRes3Leaf
import CFSG.LocalAnalysis.RankThreeTheoremC.D2PairRes3Abel

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbeddingD2 CFSG.QuasithinUnique
open CFSG.RankThreeCoreUniqueness.Helpers

variable {G : Type} [Group G] [Finite G]

theorem d2L34BetaConf3_of_l34 (hO : KFactL34Outer) (hI : KFactL34Inner)
    (hNO : KFactL34NotOrthogonal) (hSch : KFactCatalogSchreier) (hK4 : KFactSylowThreeAbelian)
    (h84 : Asc81bEightFour) (h93 : Asc81bNineThree) (hX : D1NoXBlock3 G)
    (hS3 : D2PairStrongThree3Comp G) (hS : Setting G) (hD1 : TheoremD1 G) {M : Subgroup G}
    (hM : rankThreeIsMaxTwoLocal M) (ha : D2FullCoreAt G M) (hb : D2ThreeClauseAt G M)
    (hp : 3 ∈ rankThreeSigmaA G) {P : Sylow 3 G} (hMP : IsCoreMaxLocal 3 P M)
    {A H R : Subgroup G} (hesc : D2Escape 3 P M A H R) (hmax : D2EscapeMax 3 P M R)
    {d : TauCeti.ValidLieTypeIndex} (hd : IsL34Index d)
    {Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3)}
    {K : Subgroup (H ⧸ primeComplementCore (G := H) 3)}
    (hRbar : (Rbar : Subgroup _) = (R.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore 3)))
    (hK : D2AlmostSimple 3 (H ⧸ primeComplementCore (G := H) 3) Rbar
      ((A.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore 3)))
      (((H ⊓ M).subgroupOf H).map (QuotientGroup.mk' (primeComplementCore 3))) K)
    (he : Nonempty (K ≃* (TauCeti.CFSGIndex.lie d).Group)) :
    D2L34BetaConf3 d P M A H R Rbar K := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hglob : AGLGlobal G := aglGlobal_of_setting hS
  have hNX : NoXBlockFor G := noXBlockFor_of_setting hX hS
  have hab := hesc.elemNine_of_abelian hRbar hK
    (hK4.1 d hd _ K Rbar hK.normal hK.centralizer_eq_bot he)
  by_cases hAK : (A.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore 3)) ≤ K
  swap
  · exact (hK.false_of_glbCore_one_eq_top
      (hO d hd _ K hK.normal hK.centralizer_eq_bot he _ hK.elem hK.card_A hAK)).elim
  have hirr := irreducibleOn_of_l34 hI hd hesc hRbar hK he hAK
  by_cases hC : Subgroup.centralizer
      (((A.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore 3)) : Subgroup _) :
        Set (H ⧸ primeComplementCore (G := H) 3)) ≤
      (A.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore 3))
  · exfalso
    have hU := primeComplementCore_eq_bot_of_l34 hI hd hK he hAK hC
    have hpr : AGLPair 3 M H R := hesc.toPair hglob
      (hesc.twoCore_inf_eq_of_primeCore_inf_eq (hesc.primeCore_inf_eq_iff.mpr hU))
    have hns : ¬ Group.IsSolvable M := fun hsolv => hpr.false_of_isSolvable h84 hNX hsolv
    have hsolv := isSolvable_normalizer_of_card_eq_nine_of_le hK.card_A hC
    rw [← hK.eq_normalizer_of_l34 hI hd he hAK] at hsolv
    exact hS3 hS hD1 M hM ha hb P A H R hp hMP hesc hmax hpr ((hb hp P hMP).2 hns)
      (d2PerfectThreePrime_of_isSolvable hsolv) hirr hab
  by_cases htwo : pCoreOf 2 (H ⊓ M) = pCoreOf 2 H
  · exfalso
    have hpr : AGLPair 3 M H R := hesc.toPair hglob htwo
    have hns : ¬ Group.IsSolvable M := fun hsolv => hpr.false_of_isSolvable h84 hNX hsolv
    exact hS3 hS hD1 M hM ha hb P A H R hp hMP hesc hmax hpr ((hb hp P hMP).2 hns)
      (d2PerfectThreePrime_of_perfect_eq_bot
        (hK.perfect_eq_bot_of_isSolvable_inf hSch (isSolvable_inf_of_l34 hI hd hK he hAK)))
      hirr hab
  by_cases hXc : ∃ C : Subgroup G, C ≤ pCoreOf 2 (H ⊓ M) ∧ C ≠ ⊥ ∧
      (C.subgroupOf (pCoreOf 2 (H ⊓ M))).Characteristic ∧ H ≤ Subgroup.normalizer (C : Set G)
  · obtain ⟨C, hCU, hC1, hchar, hHC⟩ := hXc
    have hNC : Subgroup.normalizer (C : Set G) = H :=
      hesc.maxTwoLocal_H.2 _
        ⟨C, hC1, (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 (H ⊓ M)).to_le hCU,
          rfl⟩ hHC
    have h1 := CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic
      (H := pCoreOf 2 (H ⊓ M)) (C.subgroupOf (pCoreOf 2 (H ⊓ M)))
    rw [Subgroup.map_subgroupOf_eq_of_le hCU] at h1
    have hNH : Subgroup.normalizer (pCoreOf 2 (H ⊓ M) : Set G) ≤ H := h1.trans hNC.le
    have hmaxX := hK.eq_or_eq_top_of_l34 hI hd he hAK
    have hNT : Subgroup.normalizer (pCoreOf 2 (H ⊓ M) : Set G) = H ⊓ M :=
      (inf_eq_right.mpr hNH).symm.trans (hesc.inf_normalizer_twoCore_inf hmaxX htwo)
    exact ⟨hd, hesc, hmax, hRbar, hK, he, hAK, hC, htwo, hNT, ⟨C, hCU, hC1, hchar, hHC⟩⟩
  · exact (false_of_l34_pu3 hI hNO h93 hNX hesc hglob hd hK he hAK htwo
      fun C hCU hC1 hchar hHC => hXc ⟨C, hCU, hC1, hchar, hHC⟩).elim

theorem d2L34AllResidue3_of_onlyL34At (hO : KFactL34Outer) (hI : KFactL34Inner)
    (hNO : KFactL34NotOrthogonal) (hSch : KFactCatalogSchreier) (hK4 : KFactSylowThreeAbelian)
    (h84 : Asc81bEightFour) (h93 : Asc81bNineThree) (hX : D1NoXBlock3 G)
    (hS3 : D2PairStrongThree3Comp G) (hS : Setting G) (hD1 : TheoremD1 G) {M : Subgroup G}
    (hM : rankThreeIsMaxTwoLocal M) (ha : D2FullCoreAt G M) (hb : D2ThreeClauseAt G M)
    (hp : 3 ∈ rankThreeSigmaA G) {P : Sylow 3 G} (hMP : IsCoreMaxLocal 3 P M)
    (hOnly : D2OnlyL34At P M) : D2L34AllResidue3 P M := by
  intro A' H' R' hesc hmax
  obtain ⟨Rbar', K', hRbar', hK'⟩ := hesc.almostSimple (aglGlobal_of_setting hS)
  obtain ⟨d', hd', he'⟩ := hOnly A' H' R' hesc hmax Rbar' K' hRbar' hK'
  exact ⟨d', Rbar', K', d2L34BetaConf3_of_l34 hO hI hNO hSch hK4 h84 h93 hX hS3 hS hD1 hM ha hb hp
    hMP hesc hmax hd' hRbar' hK' he'⟩

end CFSG.LocalAnalysis.RankThreeTheoremC
