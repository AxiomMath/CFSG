module

public import CFSG.LocalAnalysis.RankFourTheoremC.FischerPending.Centralizer
import CFSG.LocalAnalysis.RankThreeCoreUniqueness.RelativePairGeometry
import CFSG.LocalAnalysis.RankThreeCoreUniqueness.ConstrainedGlobalization

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.LocalAnalysis.RankThreeTheoremC Subgroup

variable {G : Type} [Group G] [Finite G]

theorem ObstructionSetting.gl83InvariantTwoTransitivity_of_containment
    (hS : ObstructionSetting G) (hR : TransitivityReduction G) (h13 : GL83InvariantTwoSylow G)
    (hcont : GL83InvariantTwoContainment G) : GL83InvariantTwoTransitivity G := by
  intro p hp P M D hext hPD hDab T T' hT hT'
  have hprime := sigmaA_prime p hp
  have hfact : Fact p.Prime := ⟨hprime⟩
  have hN := hR p hp P M D hext hPD
  have hM := hext.obstruction.1
  have hPM := hS.sylow_le hp hM
  obtain ⟨A, hAP, hA, hAc⟩ := hS.exists_elemAbelian_card_eq hp P
  obtain ⟨-, z, hzD, hz1, hzc, hzp, -⟩ := isolatedPlane_structure hprime P.isPGroup'
    (hext.isIsolatedPlane_of_isMulCommutative hprime hDab) hAP
    ((CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian p A).2 hA) hAc
  have hPN₀ := le_normalizer_zpowers_of_le_centralizer hzc
  have hN₀M := hN z hzD hz1 hzc hzp
  have hPX : (P : Subgroup G) ≤ normalizer ((CFSG.ABGTheoremB.pPrimeCoreIn p M ⊔
      CFSG.ABGTheoremB.pPrimeCoreIn p (normalizer ((zpowers z : Subgroup G) : Set G)) :
        Subgroup G) : Set G) :=
    le_normalizer_pPrimeCoreIn_sup hPM hPN₀
  have hX := h13 p hp P M D hext hPD hDab z hzD hz1 hzc hzp
  have hTX := (hX T (global_invariant_two_maximal_is_maximal_within D M T hT
    (hcont p hp P M D hext hPD hDab T hT))).le
  have hT'X := (hX T' (global_invariant_two_maximal_is_maximal_within D M T' hT'
    (hcont p hp P M D hext hPD hDab T' hT'))).le
  exact rank_two_maximal_two_subgroups_common_signalizer_transitivity p hprime D T' T _
    (P.isPGroup'.to_le hext.obstruction.2.1) hT' hT (coprime_card_pPrimeCoreIn_sup hN₀M)
    (hext.obstruction.2.1.trans hPX) hT'X hTX

theorem ObstructionSetting.transitivityCase_of_steps (hS : ObstructionSetting G)
    (hD1 : TheoremD1 G) (hR : TransitivityReduction G) (h13 : GL83InvariantTwoSylow G)
    (h15 : GL83InvariantTwoTransitivity G) : TransitivityCase G := by
  intro p hp P M D hext hPD
  have hprime := sigmaA_prime p hp
  have hfact : Fact p.Prime := ⟨hprime⟩
  have hN := hR p hp P M D hext hPD
  have hDab := hS.isMulCommutative_of_normalizer_le hp hext hN
  have hM := hext.obstruction.1
  have hPM := hS.sylow_le hp hM
  have hDM : D ≤ M := hext.obstruction.2.1.trans hPM
  obtain ⟨A, hAP, hA, hAc⟩ := hS.exists_elemAbelian_card_eq hp P
  obtain ⟨-, z, hzD, hz1, hzc, hzp, -⟩ := isolatedPlane_structure hprime P.isPGroup'
    (hext.isIsolatedPlane_of_isMulCommutative hprime hDab) hAP
    ((CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian p A).2 hA) hAc
  have hPN₀ := le_normalizer_zpowers_of_le_centralizer hzc
  have hN₀M := hN z hzD hz1 hzc hzp
  have hCD : centralizer (D : Set G) ≤ M := by
    refine le_trans ?_ ((centralizer_le_normalizer _).trans hN₀M)
    rw [zpowers_eq_closure, centralizer_closure]
    exact centralizer_le (Set.singleton_subset_iff.mpr hzD)
  obtain ⟨T, hO2T, hT⟩ := exists_invariantTwoMaximalWithin_containing D M (pCoreOf 2 M)
    (pCoreOf_le 2 M) (pCoreOf_isPGroup 2 M) (hDM.trans (localGroup_le_normalizer_pCoreOf 2 M))
  have hTne : T ≠ ⊥ := fun h => twoLocal_pCoreOf_ne_bot M hM.1.1 (le_bot_iff.mp (h ▸ hO2T))
  have hXM : CFSG.ABGTheoremB.pPrimeCoreIn p M ⊔ CFSG.ABGTheoremB.pPrimeCoreIn p
      (normalizer ((zpowers z : Subgroup G) : Set G)) ≤ M :=
    sup_le (CFSG.ABGTheoremB.pPrimeCoreIn_le p M)
      ((CFSG.ABGTheoremB.pPrimeCoreIn_le p _).trans hN₀M)
  have hPX : (P : Subgroup G) ≤ normalizer ((CFSG.ABGTheoremB.pPrimeCoreIn p M ⊔
      CFSG.ABGTheoremB.pPrimeCoreIn p (normalizer ((zpowers z : Subgroup G) : Set G)) :
        Subgroup G) : Set G) :=
    le_normalizer_pPrimeCoreIn_sup hPM hPN₀
  have hNT := hS.normalizer_le_of_isSylowOf_two hD1 hp hM hXM hPX
    (coprime_card_pPrimeCoreIn_sup hN₀M) (h13 p hp P M D hext hPD hDab z hzD hz1 hzc hzp T hT)
    hTne
  have hTglob := invariantTwoMaximalWithin_global_of_normalizer_le D M T hDM hT hNT
  exact ⟨hCD, T, hTglob, hNT, fun T' hT' => h15 p hp P M D hext hPD hDab T T' hTglob hT'⟩

theorem ObstructionSetting.transitivityCase_of_containment (hS : ObstructionSetting G)
    (hD1 : TheoremD1 G) (hR : TransitivityReduction G) (h13 : GL83InvariantTwoSylow G)
    (hcont : GL83InvariantTwoContainment G) : TransitivityCase G :=
  hS.transitivityCase_of_steps hD1 hR h13
    (hS.gl83InvariantTwoTransitivity_of_containment hR h13 hcont)

end CFSG.LocalAnalysis.RankFourTheoremC
