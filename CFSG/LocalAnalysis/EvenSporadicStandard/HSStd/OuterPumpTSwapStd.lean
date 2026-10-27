module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.OuterPumpTKillStd
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.S5SecLookupSwap
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.OuterPumpTSwap
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.OuterPumpL4Seitz
import CFSG.LocalAnalysis.OddStandard.GlueAlt
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.OuterPumpChainStd
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.OuterPumpGlobal
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.OuterPumpLift
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.OuterPumpTGood
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.OuterPumpTSetup
public import CFSG.LocalAnalysis.OddStandard.ONanSylowFacts

public section

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus.Outer

open Subgroup Relation CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.EvenSporadicStandard
  CFSG.EvenSporadicStandard.Induction CFSG.EvenSporadicStandard.Solomon78
  CFSG.EvenSporadicStandard.HSStd CFSG.Open CFSG.Assembly.LowTwoRank

section Cases

variable {G : Type} [Group G] [Finite G] {M : Subgroup G}

theorem false_of_standard_altT_std
    (hStd : CFSG.OddStandard.AltStdSec.AltStdFormBigStd)
    (h2An : CFSG.ComponentClassification.GSThmB.Solomon2AnInput)
    (hA8cyc : Nonempty (↥M ⧸ center ↥M ≃* alternatingGroup (Fin 8)) → center ↥M = ⊥ →
      StdHyp G M → False)
    (hA10cyc : Nonempty (↥M ⧸ center ↥M ≃* alternatingGroup (Fin 10)) → center ↥M = ⊥ →
      StdHyp G M → False)
    (h : StdHyp G M) (hHS : 44352000 ∣ Nat.card G)
    (ht : ∃ t : G, orderOf t = 2 ∧ Nat.card (centralizer ({t} : Set G)) = 177408000)
    {k : ℕ} (hk : 4 ≤ k) (e : Nonempty (↥M ⧸ center ↥M ≃* alternatingGroup (Fin (2 * k)))) :
    False := by
  by_cases hcase : 12 ≤ 2 * k ∨ Nat.card (center ↥M) = 2
  · exact false_of_standard_altT_big_std hStd h2An h hHS ht hk e hcase
  · push Not at hcase
    have : Group.IsPerfect ↥M := (isQuasisimple_of_stdHyp h).1
    have hle : Nat.card (center ↥M) ≤ 2 :=
      CFSG.OddStandard.GlueAlt.card_center_le_two_of_alt (n := 2 * k) (by omega) e.some
    have hpos : 0 < Nat.card (center ↥M) := Nat.card_pos
    have hZ : center ↥M = ⊥ := Subgroup.card_eq_one.1 (by omega)
    rcases (show k = 4 ∨ k = 5 by omega) with rfl | rfl
    · exact hA8cyc e hZ h
    · exact hA10cyc e hZ h

theorem false_of_standard_pumpT_std
    (hrec : RankTwoStdRec) (hCo1 : Co1InvCentralizers) (thm24_1 : Sol78Thm24_1Use)
    (hlie : Hyp.OddLieCompNotSporadic)
    (hStd : CFSG.OddStandard.AltStdSec.AltStdFormBigStd)
    (h2An : CFSG.ComponentClassification.GSThmB.Solomon2AnInput)
    (hCTB : CentralTwoBound) (hLE : ∀ L : Subgroup G, StdHyp G L → ¬ IsSporadic ↥L .HN)
    (hX : McLStdExclusion)
    (hS : CFSG.SeitzReduction.SeitzExclusion CFSG.SeitzReduction.HighPSL)
    (hL4 : L4CentralTwoTrivial)
    (hA8cyc : Nonempty (↥M ⧸ center ↥M ≃* alternatingGroup (Fin 8)) → center ↥M = ⊥ →
      StdHyp G M → False)
    (hA10cyc : Nonempty (↥M ⧸ center ↥M ≃* alternatingGroup (Fin 10)) → center ↥M = ⊥ →
      StdHyp G M → False)
    (hHScyc : IsSporadic (↥M ⧸ center ↥M) .HS → StdHyp G M → False)
    (hsimp : IsSimpleGroup G) (hnonab : ∃ a b : G, a * b ≠ b * a)
    (hK : CFSG.Assembly.KProper CFSG.Blueprint.Catalog G)
    (hbal : ∀ t : G, orderOf t = 2 → standardComponentOddCore (centralizer ({t} : Set G)) = ⊥)
    (hM : standardComponentIsStandard M) (hZ : IsPGroup 2 (center ↥M))
    (hpump : PumpType (↥M ⧸ center ↥M)) (hHS : 44352000 ∣ Nat.card G)
    (ht : ∃ t : G, orderOf t = 2 ∧ Nat.card (centralizer ({t} : Set G)) = 177408000)
    (hcomp : SporadicInvComp G) : False := by
  by_cases hr : 2 ≤ CFSG.Open.pRank 2 (centralizer (M : Set G))
  · exact false_of_standard_pumpType_rank_two hrec hCo1 hnonab hK hHS ht hM hr
  · obtain ⟨hstd, -⟩ := stdHyp_of_rank_one_of_comp thm24_1 hlie hsimp hnonab hHS hK hbal hM hZ
      hcomp (by omega)
    rcases hpump with ⟨k, hk, e⟩ | e | e | e | ⟨i, hi, e⟩
    · exact false_of_standard_altT_std hStd h2An hA8cyc hA10cyc hstd hHS ht hk e
    · exact hHScyc e hstd
    · exact false_of_standard_mcl hCTB hX hstd e
    · exact false_of_standard_hn_loc hCTB hLE hstd e
    · exact false_of_standard_l4_of_highPSL hS hL4 hstd hi e

end Cases

section Self

variable {G : Type} [Group G] [Finite G]

theorem false_of_pump_component_selfT_std
    (hT : KGPumpTableT) (h13 : FS79Thm13UseSec G) (hrank : KGPumpRank) (hrec : RankTwoStdRec)
    (hCo1 : Co1InvCentralizers) (thm24_1 : Sol78Thm24_1Use) (hlie : Hyp.OddLieCompNotSporadic)
    (hStd : CFSG.OddStandard.AltStdSec.AltStdFormBigStd)
    (h2An : CFSG.ComponentClassification.GSThmB.Solomon2AnInput) (hCTB : CentralTwoBound)
    (hLE : ∀ L' : Subgroup G, StdHyp G L' → ¬ IsSporadic ↥L' .HN) (hX : McLStdExclusion)
    (hS : CFSG.SeitzReduction.SeitzExclusion CFSG.SeitzReduction.HighPSL)
    (hL4 : L4CentralTwoTrivial) (ctx : PumpCtx G) (hHS : 44352000 ∣ Nat.card G)
    (ht : ∃ t : G, orderOf t = 2 ∧ Nat.card (centralizer ({t} : Set G)) = 177408000)
    (hcomp : SporadicInvComp G) {x : G} (hx : orderOf x = 2) {M : Subgroup G}
    (hM : IsCompIn M (centralizer ({x} : Set G))) (hp : PumpType (↥M ⧸ center ↥M))
    (hnA8 : ¬ Nonempty (↥M ⧸ center ↥M ≃* alternatingGroup (Fin 8)))
    (hselfHS : IsSporadic (↥M ⧸ center ↥M) .HS → StdHyp G M → False)
    (hselfA10 : Nonempty (↥M ⧸ center ↥M ≃* alternatingGroup (Fin 10)) → center ↥M = ⊥ →
      StdHyp G M → False) : False := by
  have hTab := kgPumpTable_of_T hT
  obtain ⟨M', hM', hmax, -⟩ := exists_maximalF_above (K₀ := M) ⟨x, hx, hM⟩
  have hpM : PumpType (↥M' ⧸ center ↥M') := by
    rcases hM' with rfl | hT'
    · exact hp
    · exact pumpType_of_transGen ctx hTab hT' hp
  have hstd : StdBare M' := stdBare_of_maximalF_pumpType ctx h13 hrank hmax hpM
  have hstdc : standardComponentIsStandard M' := standard_of_maximalF_pumpType ctx h13 hrank hmax
    hpM
  obtain ⟨t', ht', hMt⟩ := hmax.1
  have hZ : IsPGroup 2 (center ↥M') := ctx.isPGroup_center ht' hMt
  have hlast : ∀ (hT' : TransGen LtF M M'), M ≠ M' →
      (Nonempty (↥M' ⧸ center ↥M' ≃* alternatingGroup (Fin 10)) ∨
        IsSporadic (↥M' ⧸ center ↥M') .HS) → False := by
    intro hT' hne hM10
    obtain ⟨K, s, t, hl, -, -, hall⟩ := last_link_of_a10_or_hs ctx hT hp hT' hne hstd hM10
    refine hnA8 (hall M ReflTransGen.refl ?_)
    rcases hl.chain with rfl | hch
    · exact ReflTransGen.refl
    · exact hch.to_reflTransGen
  refine false_of_standard_pumpT_std hrec hCo1 thm24_1 hlie hStd h2An hCTB hLE hX hS hL4
    (fun e _ _ => ?_) (fun e hZ0 hSH => ?_) (fun hHS' hSH => ?_) ctx.simple ctx.nonabelian
    ctx.kProper (fun y hy => ctx.balanced y hy) hstdc hZ hpM hHS ht hcomp
  · rcases hM' with rfl | hT'
    · exact hnA8 e
    · by_cases hne : M = M'
      · subst hne
        exact hnA8 e
      · exact false_of_a8_maximal hT ctx hp hT' hne hstd e
  · rcases hM' with rfl | hT'
    · exact hselfA10 e hZ0 hSH
    · by_cases hne : M = M'
      · subst hne
        exact hselfA10 e hZ0 hSH
      · exact hlast hT' hne (Or.inl e)
  · rcases hM' with rfl | hT'
    · exact hselfHS hHS' hSH
    · by_cases hne : M = M'
      · subst hne
        exact hselfHS hHS' hSH
      · exact hlast hT' hne (Or.inr hHS')

theorem false_of_commuting_a8_componentT_std
    (hT : KGPumpTableT) (h13 : FS79Thm13UseSec G) (hrank : KGPumpRank) (hKG : KGHSA8)
    (hsplit : KGHSNoDoubleA8) (hCo1 : Co1InvCentralizers) (hrec : RankTwoStdRec)
    (thm24_1 : Sol78Thm24_1Use) (hlie : Hyp.OddLieCompNotSporadic)
    (hStd : CFSG.OddStandard.AltStdSec.AltStdFormBigStd)
    (h2An : CFSG.ComponentClassification.GSThmB.Solomon2AnInput)
    (hCTB : CentralTwoBound) (hLE : ∀ L' : Subgroup G, StdHyp G L' → ¬ IsSporadic ↥L' .HN)
    (hX : McLStdExclusion) (hS : CFSG.SeitzReduction.SeitzExclusion CFSG.SeitzReduction.HighPSL)
    (hL4 : L4CentralTwoTrivial)
    (hSol : TwoHS.SolomonTwoHSCentralizer) (hSI : SolomonIAltCentralizer) (hKA : KGA10A8)
    (ctx : PumpCtx G) (hHS : 44352000 ∣ Nat.card G)
    (ht : ∃ t : G, orderOf t = 2 ∧ Nat.card (centralizer ({t} : Set G)) = 177408000)
    (hcomp : SporadicInvComp G) {x g : G} (hx : orderOf x = 2) {M₂ : Subgroup G}
    (hM : IsCompIn M₂ (centralizer ({x} : Set G)))
    (h8 : Nonempty (↥M₂ ⧸ center ↥M₂ ≃* alternatingGroup (Fin 8)))
    (hc : ⁅M₂, M₂.map (MulAut.conj g).toMonoidHom⁆ = ⊥) : False := by
  have hTab := kgPumpTable_of_T hT
  have hp : PumpType (↥M₂ ⧸ center ↥M₂) := Or.inl ⟨4, le_refl _, h8⟩
  obtain ⟨M, hch, hne, hmax, hpM, hstd, hstdc⟩ :=
    exists_standard_maximal_pump_above ctx hTab h13 hrank ⟨x, hx, hM⟩ hp g hc
  obtain ⟨t', ht', hMt⟩ := hmax.1
  have hZ : IsPGroup 2 (center ↥M) := ctx.isPGroup_center ht' hMt
  exact false_of_standard_pumpT_std hrec hCo1 thm24_1 hlie hStd h2An hCTB hLE hX hS hL4
    (fun e _ _ => false_of_a8_maximal hT ctx hp hch hne hstd e)
    (fun e hZ0 hSH => false_of_a10_standard hT hSI hKA ctx hp hch hne hstd e hZ0 hSH hc)
    (fun hHS' hSH => false_of_hs_standard hKG hTab hsplit hCTB hSol ctx hp hch hne hstd hHS' hSH hc)
    ctx.simple ctx.nonabelian ctx.kProper (fun y hy => ctx.balanced y hy) hstdc hZ hpM hHS ht
    hcomp

end Self

theorem false_of_swap_pumpT_std {G : Type} [Group G] [Finite G]
    (hT : KGPumpTableT) (h13 : FS79Thm13UseSec G) (hrank : KGPumpRank) (hKG : KGHSA8)
    (hsplit : KGHSNoDoubleA8) (hCo1 : Co1InvCentralizers) (hrec : RankTwoStdRec)
    (thm24_1 : Sol78Thm24_1Use) (hlie : Hyp.OddLieCompNotSporadic)
    (hStd : CFSG.OddStandard.AltStdSec.AltStdFormBigStd)
    (h2An : CFSG.ComponentClassification.GSThmB.Solomon2AnInput)
    (hCTB : CentralTwoBound) (hLE : ∀ L' : Subgroup G, StdHyp G L' → ¬ IsSporadic ↥L' .HN)
    (hX : McLStdExclusion) (hS : CFSG.SeitzReduction.SeitzExclusion CFSG.SeitzReduction.HighPSL)
    (h15 : FS79Lemma15Sec G) (hL4 : L4CentralTwoTrivial)
    (hSol : TwoHS.SolomonTwoHSCentralizer) (hSI : SolomonIAltCentralizer) (hKA : KGA10A8)
    (hq8 : KGA8Q8) (hcover : KGA8CoverElem)
    {L : Subgroup G} {t : G} {S : Subgroup G} {z n v s : G} (h : HSOuterSetup G L t S z n v s)
    (hF : ¬ F v t) : False := by
  have ctx : PumpCtx G := pumpCtx_of_setup h
  have hv2 : orderOf v = 2 :=
    orderOf_eq_prime (by rw [pow_two]; exact h.ctx.v_sq) h.v_ne_one
  obtain ⟨g', hgv, hgL, hgt, hg2⟩ := exists_swap_involution h hF
  have hE8 : SwapNoE8 L v := fun E hE hE2 =>
    card_le_four_of_le_centralizer_derived_of_hs hKG h hE hE2
  rcases swap_layer_dichotomy h15 hq8 hcover h hE8 with ⟨M, hM⟩ | ⟨Q₁, Q₂, hP⟩
  · refine false_of_pump_component_selfT_std hT h13 hrank hrec hCo1 thm24_1 hlie hStd h2An hCTB
      hLE hX hS hL4 ctx (dvd_card_of_setup h) (exists_involution_of_setup h)
      (sporadicInvComp_of_setup h) hv2 hM.comp hM.pump
      (not_alt8_of_swapSingle h hM)
      (fun hHS' hSH => false_of_swapSingle_hs hKG hCTB hSol h hM hHS' hSH hgv hgL hgt hg2)
      (fun hA10 hZ0 hSH => ?_)
    have eM : ↥M ≃* ↥M ⧸ center ↥M :=
      MulEquiv.ofBijective (QuotientGroup.mk' (center ↥M))
        ⟨(MonoidHom.ker_eq_bot_iff _).1 (by rw [QuotientGroup.ker_mk']; exact hZ0),
          QuotientGroup.mk'_surjective _⟩
    exact false_of_swapSingle_gen h hM (fixerBound_of_a10 hKA hA10) hSH
      (hSI G M hSH 10 (by norm_num) ⟨eM.trans hA10.some⟩) hgv hgL hgt hg2
  · have hc : ⁅Q₁, Q₁.map (MulAut.conj t).toMonoidHom⁆ = ⊥ := by
      rw [← hP.swap, Subgroup.commutator_eq_bot_iff_le_centralizer]
      intro a ha
      rw [mem_centralizer_iff]
      intro b hb
      exact (hP.commute a ha b hb).symm
    exact false_of_commuting_a8_componentT_std hT h13 hrank hKG hsplit hCo1 hrec thm24_1 hlie
      hStd h2An hCTB hLE hX hS hL4 hSol hSI hKA ctx (dvd_card_of_setup h)
      (exists_involution_of_setup h) (sporadicInvComp_of_setup h) hv2 hP.comp₁ hP.alt₁ hc

section Good

variable {G : Type} [Group G] [Finite G]

theorem false_of_outerSwap_pumpT_std
    (hT : KGPumpTableT) (h13 : FS79Thm13UseSec G) (hrank : KGPumpRank) (hKG : KGHSA8)
    (hsplit : KGHSNoDoubleA8) (hCo1 : Co1InvCentralizers) (hrec : RankTwoStdRec)
    (thm24_1 : Sol78Thm24_1Use) (hlie : Hyp.OddLieCompNotSporadic)
    (hStd : CFSG.OddStandard.AltStdSec.AltStdFormBigStd)
    (h2An : CFSG.ComponentClassification.GSThmB.Solomon2AnInput)
    (hCTB : CentralTwoBound) (hLE : ∀ L' : Subgroup G, StdHyp G L' → ¬ IsSporadic ↥L' .HN)
    (hX : McLStdExclusion) (hS : CFSG.SeitzReduction.SeitzExclusion CFSG.SeitzReduction.HighPSL)
    (hL4 : L4CentralTwoTrivial)
    (hSol : TwoHS.SolomonTwoHSCentralizer) (hSI : SolomonIAltCentralizer) (hKA : KGA10A8)
    {L : Subgroup G} {t : G} {S : Subgroup G} {z n v s : G} (h : HSOuterSetup G L t S z n v s)
    {K : Subgroup (OuterSection v)}
    (hK : OuterSwap (OuterSection v) (sectionImage v (derivedCentralizerIn L v)) h.tBar K) :
    False := by
  have ctx : PumpCtx G := pumpCtx_of_setup h
  obtain ⟨e⟩ := hK.alt8
  have hv2 : orderOf v = 2 :=
    orderOf_eq_prime (by rw [pow_two]; exact h.ctx.v_sq) h.v_ne_one
  exact false_of_commuting_a8_componentT_std hT h13 hrank hKG hsplit hCo1 hrec thm24_1 hlie hStd
    h2An hCTB hLE hX hS hL4 hSol hSI hKA ctx (dvd_card_of_setup h)
    (exists_involution_of_setup h) (sporadicInvComp_of_setup h) hv2
    (isCompIn_outerLift v hK.comp.2 e) (nonempty_quotient_outerLift v e)
    (commutator_outerLift_conj v e t (mem_centralizer_singleton_iff.2 h.t_comm_v) hK.commute)

end Good

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus.Outer

namespace CFSG.EvenSporadicStandard.HSStd

open Subgroup CFSG.EvenSporadicStandard CFSG.EvenSporadicStandard.Induction
  CFSG.EvenSporadicStandard.Solomon78 CFSG.EvenSporadicStandard.HSStd.Zassenhaus
  CFSG.EvenSporadicStandard.HSStd.Zassenhaus.Outer

theorem hsOuterGoodCase_of_pumpT_std
    (hT : KGPumpTableT) (h13 : FS79Thm13UseHered) (hrank : KGPumpRank) (hKG : KGHSA8)
    (hsplit : KGHSNoDoubleA8) (hCo1 : Co1InvCentralizers) (hrec : RankTwoStdRec)
    (thm24_1 : Sol78Thm24_1Use) (hlie : Hyp.OddLieCompNotSporadic)
    (hStd : CFSG.OddStandard.AltStdSec.AltStdFormBigStd)
    (h2An : CFSG.ComponentClassification.GSThmB.Solomon2AnInput)
    (hCTB : CentralTwoBound) (hLE : HNStdExclusionHered)
    (hX : McLStdExclusion) (hS : CFSG.SeitzReduction.SeitzExclusion CFSG.SeitzReduction.HighPSL)
    (h15 : FS79Lemma15Hered) (hL4 : L4CentralTwoTrivial)
    (hSol : TwoHS.SolomonTwoHSCentralizer) (hSI : SolomonIAltCentralizer) (hKA : KGA10A8)
    (hq8 : KGA8Q8) (hcover : KGA8CoverElem) : HSOuterGoodCase :=
  fun G _ _ _ _ _ _ _ _ _ hG h => Classical.byContradiction fun hF =>
    false_of_swap_pumpT_std hT (h13.sec hG) hrank hKG hsplit hCo1 hrec thm24_1 hlie hStd h2An hCTB
      (fun L' hL' => hLE G hG L' hL') hX hS (h15.sec hG) hL4 hSol hSI hKA hq8 hcover h hF

theorem hsOuterSwapFree_of_pumpT_std
    (hT : KGPumpTableT) (h13 : FS79Thm13UseHered) (hrank : KGPumpRank) (hKG : KGHSA8)
    (hsplit : KGHSNoDoubleA8) (hCo1 : Co1InvCentralizers) (hrec : RankTwoStdRec)
    (thm24_1 : Sol78Thm24_1Use) (hlie : Hyp.OddLieCompNotSporadic)
    (hStd : CFSG.OddStandard.AltStdSec.AltStdFormBigStd)
    (h2An : CFSG.ComponentClassification.GSThmB.Solomon2AnInput)
    (hCTB : CentralTwoBound) (hLE : HNStdExclusionHered)
    (hX : McLStdExclusion) (hS : CFSG.SeitzReduction.SeitzExclusion CFSG.SeitzReduction.HighPSL)
    (hL4 : L4CentralTwoTrivial)
    (hSol : TwoHS.SolomonTwoHSCentralizer) (hSI : SolomonIAltCentralizer) (hKA : KGA10A8) :
    HSOuterSwapFree :=
  fun G _ _ _ _ _ _ _ _ _ hG h _ hK =>
    false_of_outerSwap_pumpT_std hT (h13.sec hG) hrank hKG hsplit hCo1 hrec thm24_1 hlie hStd h2An
      hCTB (fun L' hL' => hLE G hG L' hL') hX hS hL4 hSol hSI hKA h hK

end CFSG.EvenSporadicStandard.HSStd
