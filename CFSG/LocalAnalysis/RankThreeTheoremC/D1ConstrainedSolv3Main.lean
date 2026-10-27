module

public import CFSG.LocalAnalysis.RankThreeTheoremC.D1ConstrainedClose3Main
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1ConstrainedSolv3Defs
import CFSG.LocalAnalysis.RankThreeTheoremC.D1ConstrainedSolv3Core
import CFSG.LocalAnalysis.RankThreeTheoremC.D1ConstrainedSolv3Normalizes
import CFSG.LocalAnalysis.RankThreeTheoremC.D1ConstrainedSolv3Rank
import CFSG.LocalAnalysis.RankThreeTheoremC.D1ConstrainedSolv3Shapes
import CFSG.LocalAnalysis.RankThreeTheoremC.D1ConstrainedSolv3Sylow

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.PreuniquenessRankFour.Helpers CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.AGLEmbedding (D1Extremal D1Escape D1PhaseThree Asc81bEightFive Asc81bNineThree
  D1NoXBlock IsWeakSBlock KFactOutElemRank barM catalogSimpleSections_of_isKProper)

variable {G : Type} [Group G] [Finite G]

theorem false_of_solvable_weakBlock_three (hK5 : KFactBlockSylowThreeAut)
    (h85 : Asc81bEightFive) (h93 : Asc81bNineThree) (hD2 : D1NoXBlock) (hS : Setting G)
    (hp : 3 ∈ rankThreeSigmaA G) {P : Sylow 3 G} {M H : Subgroup G} (hM : IsCoreMaxLocal 3 P M)
    (hext : D1Extremal 3 P M H (P : Subgroup G)) {z : G} (hz : D1CentralizerInput3 3 P M z)
    (hph : D1PhaseThree 3 P M H (P : Subgroup G)) (hzP : z ∈ (P : Subgroup G))
    (hCH : Subgroup.centralizer ({z} : Set G) ≤ H) {L : Subgroup G}
    (hL : IsWeakSBlock M (pCoreOf 2 H) L)
    (hsolv : Group.IsSolvable ↥(Subgroup.normalizer ((pCoreOf 2 H : Subgroup G) : Set G) ⊓ L)) :
    False := by
  have hN : Subgroup.normalizer ((pCoreOf 2 H : Subgroup G) : Set G) = H :=
    hext.toD1Escape.normalizer_twoCore_H
  have hyps : BlockL28Hyps M (pCoreOf 2 H) L :=
    ⟨hph.isKGroup.1, hph.asc81bHyp, hL, hph.nineThree h93 hL,
      (hph.nineThree_not_one h85 hD2 hL).1, hph.not_isSylowTwoOf_inf h85 hD2 hL⟩
  have hQS : pCoreOf 2 M ≤ pCoreOf 2 H := hph.twoCore_M_le hph.twoCore_inf
  exact false_of_sylow_three_action hS.rank hp hM.1.1 hL hN hext.sylow_le hext.le_H hz.pRank_eq
    hz.orderOf_eq hzP hz.uniq hCH hQS
    (fun hs hi => not_dvd_card_mulAut_of_blockHyps hK5 hyps hQS hs hi) hsolv

@[expose] def D1ConstrainedWeakBlockGeFive (G : Type) [Group G] [Finite G] : Prop :=
  Setting G → ∀ p ∈ rankThreeSigmaA G, p ≠ 3 → ∀ (P : Sylow p G) (M : Subgroup G),
    IsCoreMaxLocal p P M → ∀ H : Subgroup G, D1Extremal p P M H (P : Subgroup G) →
      ∀ (_ : Fact p.Prime) (z : G), D1CentralizerInput3 p P M z →
      CFSG.layer (Subgroup.centralizer ({z} : Set G) ⧸
        primeComplementCore (G := Subgroup.centralizer ({z} : Set G)) p) = ⊥ →
      ∀ (Pbar : Sylow p (ReducedCentralizer p z)) (zbar : ReducedCentralizer p z)
        (E C : Subgroup (ReducedCentralizer p z)) (_ : E.Normal)
        (e : E ⧸ Subgroup.center E ≃* Multiplicative (Fin 2 → ZMod p)),
        D1ConstrainedReducedData3 p P M z Pbar zbar →
        ReducedStructure3 p Pbar (reducedMeet p M z) zbar E C e →
      HasPrimeConstraint (G := H) p → D1PhaseThree p P M H (P : Subgroup G) →
      z ∈ (P : Subgroup G) → Subgroup.centralizer ({z} : Set G) ≤ H →
      (∀ K : Subgroup G, GLBIsMaxTwoLocal K → (P : Subgroup G) ≤ K → ¬ K ≤ M → K = H) →
      Subgroup.normalizer ((P : Subgroup G) : Set G) ≤ H →
      ∀ T : Subgroup G, T ≤ GLBPrimeCore p H → IsPGroup 2 T →
        ¬ 2 ∣ (T.subgroupOf (GLBPrimeCore p H)).index →
        (P : Subgroup G) ≤ Subgroup.normalizer (T : Set G) → pCoreOf 2 H ≤ T →
        (∀ U : Subgroup G, U ≤ T → U ≠ ⊥ → (U.subgroupOf T).Characteristic →
          Subgroup.normalizer (U : Set G) ≤ H) →
        ∀ L : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L →
          (P : Subgroup G) ≤ Subgroup.normalizer (L : Set G) →
          (P : Subgroup G) ⊓ ((Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M))).comap
            (QuotientGroup.mk' (CFSG.pCore 2 ↥M))).map M.subtype = ⊥ →
          ¬ p ∣ (((P : Subgroup G) ⊓ L).subgroupOf L).index → z ∈ L → False

theorem D1ConstrainedWeakBlockGeFive.toSolv3 (hK5 : KFactBlockSylowThreeAut)
    (hOut : KFactOutElemRank) (h85 : Asc81bEightFive) (h93 : Asc81bNineThree)
    (hD2 : D1NoXBlock) (h : D1ConstrainedWeakBlockGeFive G) : D1ConstrainedWeakBlockSolv3 G := by
  intro hS p hp P M hM H hext hfact z hz hlayer Pbar zbar E C hEn e hdata hstr hcon hph hzP hCH
    huniq hNH T hTN hT2 hTidx hPT hST hchar _ L hL hsolv
  by_cases hp3 : p = 3
  · subst hp3
    exact false_of_solvable_weakBlock_three hK5 h85 h93 hD2 hS hp hM hext hz hph hzP hCH hL
      (hsolv rfl)
  · have hp5 : 5 ≤ p := by
      have h2 := hfact.out.two_le
      have h4 : p ≠ 4 := by
        rintro rfl
        exact absurd hfact.out (by norm_num)
      have := hext.ne_two
      omega
    have hPL := le_normalizer_of_isPGroup_ge_five hS.rank hfact.out hp5 hM.1.1
      hL.toIsTwoPrimeComponent P.isPGroup' hext.sylow_le
    have hN : Subgroup.normalizer ((pCoreOf 2 H : Subgroup G) : Set G) = H :=
      hext.toD1Escape.normalizer_twoCore_H
    have hfaith := inf_preimage_centralizer_eq_bot_of_weakBlock hext.ne_two P.isPGroup' hL hN
      hext.sylow_le hPL hz.orderOf_eq hzP hz.uniq hCH (hph.twoCore_M_le hph.twoCore_inf)
    have hsyl := not_dvd_index_inf_of_sylow_top P hPL
    have hMtop : M ≠ ⊤ := fun hMt => hph.not_le (hMt ▸ le_top)
    have hcat : IsCatalogGroup (↥(barM M L) ⧸ Subgroup.center ↥(barM M L)) :=
      ((catalogSimpleSections_of_isKProper hph.glob.kProper M hMtop).quotient
        _).isCatalogGroup_center_quotient hL.component
    have hpb := dvd_card_barM_of_faithful hOut hfact.out hp5 hz.pRank_eq hext.sylow_le hPL
      hL.component hcat hfaith
    have hzL : z ∈ L := mem_of_dvd_card_of_sylow P.isPGroup' hPL hzP hz.orderOf_eq hz.uniq hsyl
      (hpb.trans (card_barM_dvd hL.le))
    exact h hS p hp hp3 P M hM H hext hfact z hz hlayer Pbar zbar E C hEn e hdata hstr hcon hph hzP
      hCH huniq hNH T hTN hT2 hTidx hPT hST hchar L hL hPL hfaith hsyl hzL

theorem d1ConstrainedWeakBlockResidue3_of_five (hK4 : KFactBlockPerfectCoreThree)
    (hK5 : KFactBlockSylowThreeAut) (hOut : KFactOutElemRank) (h85 : Asc81bEightFive)
    (h93 : Asc81bNineThree) (hD2 : D1NoXBlock) (h : D1ConstrainedWeakBlockGeFive G) :
    D1ConstrainedWeakBlockResidue3 G :=
  d1ConstrainedWeakBlockResidue3_of_solv hK4 h85 h93 hD2 (h.toSolv3 hK5 hOut h85 h93 hD2)

end CFSG.LocalAnalysis.RankThreeTheoremC
