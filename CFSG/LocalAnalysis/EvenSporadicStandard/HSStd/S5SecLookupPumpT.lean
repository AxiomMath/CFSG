module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.S5SecLookup
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.OuterPumpTChain
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.OuterPumpTSetup
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.OuterPumpSeitzLift
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.OuterPumpChainStd
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.OuterPumpGlobal
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.OuterPumpL4Seitz

public section

namespace CFSG.EvenSporadicStandard.HSStd

open Subgroup Relation CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.EvenSporadicStandard
  CFSG.EvenSporadicStandard.Induction CFSG.EvenSporadicStandard.Solomon78 CFSG.Open
  CFSG.EvenSporadicStandard.HSStd.Zassenhaus CFSG.EvenSporadicStandard.HSStd.Zassenhaus.Outer

theorem false_of_normal_l44_pumpT
    (hT : KGPumpTableT) {G : Type} [Group G] [Finite G] (h13 : FS79Thm13UseSec G)
    (hrank : KGPumpRank) (hrec : RankTwoStdRec)
    (hCo1 : Co1InvCentralizers) (thm24_1 : Sol78Thm24_1Use) (hlie : Hyp.OddLieCompNotSporadic)
    (hS : CFSG.SeitzReduction.SeitzExclusion CFSG.SeitzReduction.HighPSL)
    (hL4 : L4CentralTwoTrivial)
    {L : Subgroup G} {t : G} {S : Subgroup G} {z n v s : G}
    (h : HSOuterSetup G L t S z n v s) (W : Subgroup (OuterSection v)) (hW : W.Normal)
    (hLie : LieModel ↥W .PSL 4 2 2) : False := by
  have ctx : PumpCtx G := pumpCtx_of_setup h
  have hs := isSimpleGroup_of_lieModel_psl_four_two hLie
  obtain ⟨hperf, hcen⟩ := perfect_centerless_of_simple (not_commutative_psl_four_two hLie)
  have hK : ⁅W, W⁆ = W := commutator_eq_self_of_commutator_top hperf
  have hsub : W.IsSubnormal := hW.isSubnormal
  have hv2 : orderOf v = 2 :=
    orderOf_eq_prime (by rw [pow_two]; exact h.ctx.v_sq) h.v_ne_one
  have e := outerLiftQuotientEquiv v hK hcen
  have hM := isCompIn_outerLift_of_simple v hK hcen hsub
  have hp0 : ∃ i : ℕ, 1 ≤ i ∧
      LieModel (↥(outerLift v W) ⧸ center ↥(outerLift v W)) .PSL 4 2 (2 ^ i) :=
    ⟨1, le_rfl, by rw [pow_one]; exact CFSG.LieType.CurtisTits.lieModel_of_mulEquiv e.symm hLie⟩
  obtain ⟨M', hM', hmax, -⟩ := exists_maximalF_above (K₀ := outerLift v W) ⟨v, hv2, hM⟩
  have hrefl : ReflTransGen LtF (outerLift v W) M' := by
    rcases hM' with rfl | hT'
    · exact ReflTransGen.refl
    · exact hT'.to_reflTransGen
  obtain ⟨i, hi, hL⟩ := l4Type_of_reflTransGen ctx hT hrefl hp0
  have hpM : PumpType (↥M' ⧸ center ↥M') := Or.inr (Or.inr (Or.inr (Or.inr ⟨i, hi, hL⟩)))
  have hstdc : standardComponentIsStandard M' :=
    standard_of_maximalF_pumpType ctx h13 hrank hmax hpM
  obtain ⟨t', ht', hMt⟩ := hmax.1
  have hZ : IsPGroup 2 (center ↥M') := ctx.isPGroup_center ht' hMt
  have hHS := dvd_card_of_setup h
  have := ctx.simple
  by_cases hr : 2 ≤ CFSG.Open.pRank 2 (centralizer (M' : Set G))
  · exact false_of_standard_pumpType_rank_two hrec hCo1 ctx.nonabelian ctx.kProper hHS
      (exists_involution_of_setup h) hstdc hr
  · obtain ⟨hstd, -⟩ := stdHyp_of_rank_one_of_comp thm24_1 hlie ctx.simple ctx.nonabelian hHS
      ctx.kProper (fun y hy => ctx.balanced y hy) hstdc hZ (sporadicInvComp_of_setup h) (by omega)
    exact false_of_standard_l4_of_highPSL hS hL4 hstd hi hL

theorem hsOuterL44Free_of_pumpT
    (hT : KGPumpTableT) (h13 : FS79Thm13UseHered) (hrank : KGPumpRank) (hrec : RankTwoStdRec)
    (hCo1 : Co1InvCentralizers) (thm24_1 : Sol78Thm24_1Use) (hlie : Hyp.OddLieCompNotSporadic)
    (hS : CFSG.SeitzReduction.SeitzExclusion CFSG.SeitzReduction.HighPSL)
    (hL4 : L4CentralTwoTrivial) : HSOuterL44Free :=
  fun _ _ _ _ _ _ _ _ _ _ hG h W hW hLie =>
    false_of_normal_l44_pumpT hT (h13.sec hG) hrank hrec hCo1 thm24_1 hlie hS hL4 h W hW hLie

end CFSG.EvenSporadicStandard.HSStd
