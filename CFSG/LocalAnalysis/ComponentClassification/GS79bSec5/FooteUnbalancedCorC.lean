module

public import CFSG.LocalAnalysis.ComponentClassification.GS79bSec5.FooteUnbalanced
import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4CorCEnd
import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4CorCDiagFus
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedGSBFixedLayerNormalizer
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4CorCSteps
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBIsoInput
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCorollaryC
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitGeneral
public import CFSG.LocalAnalysis.ComponentClassification.GSFMMaximal
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitFixedHe
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeldFixA
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeldFixB
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL2Balance
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4CorCClimb
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4CorCRankGap
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4CorCTransfer
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4CorCTypes
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitLocalBalanceHe
public import CFSG.LocalAnalysis.ComponentClassification.UGSChainEqualOrderComposition
public import CFSG.LocalAnalysis.ComponentClassification.UGSChainRankDominant
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrSwapReplacement

public section

namespace CFSG.ComponentClassification.GSThmB

namespace CorC

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ComponentClassification.UnbalancedGS
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)

section

variable {X : Type} [Group X] [Finite X]

theorem Config.alternating_of_target_of_footeUnbalanced
    (hTB : GSLit.ThompsonBurgoyneInput) (hSA : SolAltLit.SolomonAlternatingOddInput)
    (hS : SchreierFor Blueprint.Catalog) (hB : GrSLit.TheoremBReachInput)
    (hH : GSLit.HarrisInput) (hFU : FooteLit.FooteMaximalUnbalancedInput)
    (hHSF : GSLit.HarrisSolomonFritzInput) (hCI : GSLit.ClassicalInvolutionInput)
    (hSol : GrSLit.SolomonCommutingCoreInput) [IsSimpleGroup X]
    (hnonab : ∃ a b : X, a * b ≠ b * a) (hK : Assembly.KProper Blueprint.Catalog X)
    (hz : ∃ z : X, orderOf z = 2 ∧ oddCore (centralizer ({z} : Set X)) ≠ ⊥)
    (hU : ¬ OutcomeLocal.UOutcome X) {a : X} {J E : Subgroup X} (h : Config a J E) {b : X}
    (hb : orderOf b = 2) (hab : a * b = b * a) (hbJ : b ∈ normalizer (J : Set X))
    (hJb : ∀ j ∈ J, j⁻¹ * b⁻¹ * j * b ∈ (pPrimeCore 2 J).map J.subtype)
    (hbE : ∀ e ∈ E, e * b = b * e) {y : X} {M : Subgroup X} (hUM : GSUnbalancingTriple b y M)
    (hT : UnbalancedGS.gsFixedLayer J b ≤ M ⊔ conjugate M a) :
    Nonempty (M ⧸ pPrimeCore 2 M ≃* alternatingGroup (Fin 7)) := by
  obtain ⟨-, -, -, hMb, hMc, -, -⟩ := gsUnbalancingTriple_iff.mp hUM
  have hEb : E ≤ centralizer ({b} : Set X) := fun e he =>
    mem_centralizer_singleton_iff.mpr (hbE e he)
  have hE : E ≤ normalizer (M : Set X) ⊓ centralizer ({b} : Set X) :=
    le_inf (h.le_normalizer_target hSol hb hab hbJ hJb hbE hMb hMc hT) hEb
  have hE4 := h.four
  have hW : ¬ ⁅M, GrSLit.wGroup E ⊓ centralizer ({b} : Set X)⁆ ≤
      (pPrimeCore 2 (centralizer ({b} : Set X))).map (centralizer ({b} : Set X)).subtype := by
    refine h.not_commutator_le_target hb hab hbJ hJb hbE hMb hT fun d hd => ?_
    obtain ⟨hdF, hdb⟩ := mem_inf.mp hd
    rw [GrSLit.wGroup_eq_iInf_of_four h.card_eq fun e he => h.mul_self_eq he]
    exact mem_inf.mpr ⟨(mem_inf.mp hdF).2, hdb⟩
  rcases hTB X hnonab hK hz hU b y M hUM with ⟨n, hodd, hn, he⟩ |
      (h7 | ⟨p, f, hp, hp2, -, -, hL⟩) | (hHe | h34)
  · exact absurd ⟨b, M, n, hb, hodd, hn, hMb, hMc, he⟩ (hSA X hnonab hK hz hU)
  · exact h7
  · exfalso
    have hR := GrSLit.gsRestrictedType_of_gsUnbalancingTriple_of_footeUnbalanced hTB hSA hS hB hH hFU hHSF hCI
      (GrSLit.heldFixedInput_of_inner GrSLit.HeldFix.isL34Type_of_isPComponent_centralizer_heA0
          GrSLit.HeldFix.not_isPComponent_centralizer_heT1P)
      GrSLit.l34FixedInput GrSLit.a7FixedInput GrSLit.l2FixedInput hnonab hK hz hU hUM
    have hs := FooteLit.isSimpleGroup_of_lieModel_psl_two hL
    have hcard := GSThmB.card_of_lieModel_psl_two hp2 hL
    have hq : Odd (p ^ f) := (hp.eq_two_or_odd'.resolve_left hp2).pow
    rcases hR with hHe' | h34' | h7' | h5' | h7''
    · obtain ⟨eH⟩ := hHe'
      have hc : Nat.card (M ⧸ Open.fusionZStar M) = 4030387200 := by
        rw [Nat.card_congr eH.toEquiv, Sporadic.He.card_He]
      have hZ := GrSLit.fusionZStar_eq_pPrimeCore_of_simple hs (fusionZStar_ne_top (by omega))
      rw [Nat.card_congr (QuotientGroup.quotientMulEquivOfEq hZ).toEquiv, hcard] at hc
      exact ordA_one_ne_held hq hc
    · exact GrSLit.false_of_psl34_of_psl_two h34' hp2 hL
    · obtain ⟨e7⟩ := h7'
      have hc : Nat.card (M ⧸ Open.fusionZStar M) = 2520 := by
        rw [Nat.card_congr e7.toEquiv, GSThmB.card_alternatingGroup_seven]
      have hZ := GrSLit.fusionZStar_eq_pPrimeCore_of_simple hs (fusionZStar_ne_top (by omega))
      rw [Nat.card_congr (QuotientGroup.quotientMulEquivOfEq hZ).toEquiv, hcard] at hc
      exact GSThmB.ordA_one_ne_2520 _ hc
    · exact hW (GrSLit.commutator_wGroup_le_of_l2 hMb hMc (Or.inl h5') hE hE4)
    · exact hW (GrSLit.commutator_wGroup_le_of_l2 hMb hMc (Or.inr h7'') hE hE4)
  · exact (hW (GrSLit.commutator_wGroup_le_of_held hMb hMc hHe hE hE4)).elim
  · exact (hW (GrSLit.commutator_wGroup_le_of_psl34 hMb hMc h34 hE hE4)).elim

theorem Config.config_of_unbalancing_target_of_footeUnbalanced
    (hTB : GSLit.ThompsonBurgoyneInput) (hSA : SolAltLit.SolomonAlternatingOddInput)
    (hS : SchreierFor Blueprint.Catalog) (hB : GrSLit.TheoremBReachInput)
    (hH : GSLit.HarrisInput) (hFU : FooteLit.FooteMaximalUnbalancedInput)
    (hHSF : GSLit.HarrisSolomonFritzInput) (hCI : GSLit.ClassicalInvolutionInput)
    (hSol : GrSLit.SolomonCommutingCoreInput) [IsSimpleGroup X]
    (hnonab : ∃ a b : X, a * b ≠ b * a) (hK : Assembly.KProper Blueprint.Catalog X)
    (hz : ∃ z : X, orderOf z = 2 ∧ oddCore (centralizer ({z} : Set X)) ≠ ⊥)
    (hU : ¬ OutcomeLocal.UOutcome X) {a : X} {J E : Subgroup X} (h : Config a J E) {b : X}
    (hb : orderOf b = 2) (hab : a * b = b * a) (hbJ : b ∈ normalizer (J : Set X))
    (hJb : ∀ j ∈ J, j⁻¹ * b⁻¹ * j * b ∈ (pPrimeCore 2 J).map J.subtype)
    (hbE : ∀ e ∈ E, e * b = b * e) {y : X} {M : Subgroup X} (hUM : GSUnbalancingTriple b y M)
    (hT : UnbalancedGS.gsFixedLayer J b ≤ M ⊔ conjugate M a) : Config b M E := by
  obtain ⟨-, -, -, hMb, hMc, -, -⟩ := gsUnbalancingTriple_iff.mp hUM
  exact h.config_of_target hSol hb hab hbJ hJb hbE hMb hMc hT
    (h.alternating_of_target_of_footeUnbalanced hTB hSA hS hB hH hFU hHSF hCI hSol hnonab hK hz hU hb hab hbJ hJb hbE
      hUM hT)

theorem Config.isoCorr_of_gsCorr_of_footeUnbalanced
    (hTB : GSLit.ThompsonBurgoyneInput) (hSA : SolAltLit.SolomonAlternatingOddInput)
    (hS : SchreierFor Blueprint.Catalog) (hB : GrSLit.TheoremBReachInput)
    (hH : GSLit.HarrisInput) (hFU : FooteLit.FooteMaximalUnbalancedInput)
    (hHSF : GSLit.HarrisSolomonFritzInput) (hCI : GSLit.ClassicalInvolutionInput)
    (hSol : GrSLit.SolomonCommutingCoreInput) [IsSimpleGroup X]
    (hnonab : ∃ a b : X, a * b ≠ b * a) (hK : Assembly.KProper Blueprint.Catalog X)
    (hz : ∃ z : X, orderOf z = 2 ∧ oddCore (centralizer ({z} : Set X)) ≠ ⊥)
    (hU : ¬ OutcomeLocal.UOutcome X) {a : X} {J E : Subgroup X} (h : Config a J E)
    (hmax : LexMax a J) {S : Subgroup X}
    (hSH : S ≤ centralizer ({a} : Set X) ⊓ normalizer (J : Set X))
    (hSsyl : ∃ P : Sylow 2 ↥(centralizer ({a} : Set X) ⊓ normalizer (J : Set X)),
      (P : Subgroup _) = S.subgroupOf (centralizer ({a} : Set X) ⊓ normalizer (J : Set X)))
    (hES : E ≤ S) {y : X} (hyS : y ∈ S) {b₀ : X} {L₀ : Subgroup X} (hb₀S : b₀ ∈ S)
    (hb₀E : ∀ e ∈ E, e * b₀ = b₀ * e) (hC₀ : UnbalancedGS.GSCorr a J b₀ L₀)
    (hU₀ : GSUnbalancingTriple b₀ y L₀) : UnbalancedGS.GSIsoCorr a J b₀ L₀ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (Subgroup X) :=
    Finite.of_injective (fun H : Subgroup X => (H : Set X)) SetLike.coe_injective
  by_contra hnot₀
  let F := {p : X × Subgroup X // p.1 ∈ S ∧ (∀ e ∈ E, e * p.1 = p.1 * e) ∧
    UnbalancedGS.GSCorr a J p.1 p.2 ∧ GSUnbalancingTriple p.1 y p.2 ∧
    ¬ UnbalancedGS.GSIsoCorr a J p.1 p.2}
  have : Nonempty F := ⟨⟨(b₀, L₀), hb₀S, hb₀E, hC₀, hU₀, hnot₀⟩⟩
  obtain ⟨⟨⟨b, L⟩, hbS, hbE, hC, hUL, hnot⟩, hbest⟩ :=
    Finite.exists_max (fun p : F => Nat.card ↥(S ⊓ centralizer ({p.1.1} : Set X)))
  dsimp only at hbS hbE hC hUL hnot hbest
  obtain ⟨ha, hbo, hab, hJa, hJ, hLb, hLc, hbN, hcomm, -⟩ := id hC
  have hTL : UnbalancedGS.gsFixedLayer J b ≤ L ⊔ conjugate L a :=
    (GrSLit.GSWeakCorr.of_gsCorr hC).2.2.2.2.2.2.2.2.2
  have hcL : Config b L E := h.config_of_unbalancing_target_of_footeUnbalanced hTB hSA hS hB hH hFU hHSF hCI hSol
    hnonab hK hz hU hbo hab hbN hcomm hbE hUL hTL
  have hdLJ : (pPrimeCore 2 L).index = (pPrimeCore 2 J).index := by
    rw [hcL.index_eq, h.index_eq]
  have hrank : (pPrimeCore 2 L).index = (pPrimeCore 2 J).index →
      pRank 2 ↥(centralizer ({b} : Set X) ⊓ normalizer (L : Set X) ⊓ coreActionKernel L) ≤
        pRank 2 ↥(centralizer ({a} : Set X) ⊓ normalizer (J : Set X) ⊓ coreActionKernel J) :=
    fun _ => by
      rcases hmax b L E hcL with hlt | ⟨heq, -⟩
      · exact hlt.le
      · exact heq.le
  obtain ⟨e₀, he₀E, he₀1, -⟩ := h.exists_involution
  have hJ2 : 2 ≤ pRank 2 ↥J := GSLit.two_le_pRank_of_gsUnbalancingTriple hTB hSA hnonab hK hz hU
    (h.gsUnbalancingTriple hSol he₀E he₀1)
  obtain ⟨hLne, hdeq, hTP, hT8⟩ :=
    rank_gap_of_bound ha hJa hJ hC hnot hdLJ.le hrank hSH hSsyl hbS rfl rfl hJ2
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, e, he, -, -, hQlt, heP, heN, heJ, heK, hea,
    heb, heQ⟩ := swapped_correspondence_large_kernel_centralizer_replacement hC hLne hdeq.symm
      hSH hSsyl hbS rfl rfl rfl hTP hT8
  have heE : ∀ x ∈ E, x * e = e * x := fun x hx =>
    (heQ x (mem_inf.mpr ⟨hES hx, mem_centralizer_singleton_iff.mpr (hbE x hx)⟩)).symm
  have hey : e * y = y * e :=
    heQ y (mem_inf.mpr ⟨hyS, mem_centralizer_singleton_iff.mpr hUL.2.2.1.symm⟩)
  have heZ : e ∉ center X := GSLit.not_mem_center_of_orderOf_eq_two hnonab he
  obtain ⟨heL, -, hLe, -⟩ := UGSChain.kProper_core_trivial_orbit_fixed_layer_containment_of_schreier
    hS hK hbo he hab heb.symm heZ hLb hLc heK
  obtain ⟨M, -, -, hUM, hTM, -, hle, hcorr, -⟩ :=
    UGSChain.kProper_unbalancing_orbit_target_production_of_schreier hS hK hUL he heZ heb.symm
      hey.symm heL hLe
  have hM7 := hcL.alternating_of_target_of_footeUnbalanced hTB hSA hS hB hH hFU hHSF hCI hSol hnonab hK hz hU he
    heb.symm heL hLe heE hUM hTM
  have hdLM : (pPrimeCore 2 L).index = (pPrimeCore 2 M).index := by
    rw [hcL.index_eq, index_eq_of_alternating hM7]
  have hdJM : (pPrimeCore 2 J).index = (pPrimeCore 2 M).index := by
    rw [h.index_eq, index_eq_of_alternating hM7]
  have hC2 : UnbalancedGS.GSCorr b L e M := hcorr (Or.inr hdLM)
  obtain ⟨hC3, hmoved⟩ := UGSChain.equal_order_core_trivial_correspondence_composition_of_schreier
    hS hK hC hC2 hea.symm heZ heN heJ hdJM
  have hbest' := hbest ⟨(e, M), (mem_inf.mp heP).1, heE, hC3, hUM, (hmoved (Ne.symm hLne)).2⟩
  exact absurd hbest' (not_le.mpr (card_lt_of_lt hQlt))

theorem Config.isoCorr_of_centralizes_of_footeUnbalanced
    (hTB : GSLit.ThompsonBurgoyneInput) (hSA : SolAltLit.SolomonAlternatingOddInput)
    (hS : SchreierFor Blueprint.Catalog) (hB : GrSLit.TheoremBReachInput)
    (hH : GSLit.HarrisInput) (hFU : FooteLit.FooteMaximalUnbalancedInput)
    (hHSF : GSLit.HarrisSolomonFritzInput) (hCI : GSLit.ClassicalInvolutionInput)
    (hSol : GrSLit.SolomonCommutingCoreInput) [IsSimpleGroup X]
    (hnonab : ∃ a b : X, a * b ≠ b * a) (hK : Assembly.KProper Blueprint.Catalog X)
    (hz : ∃ z : X, orderOf z = 2 ∧ oddCore (centralizer ({z} : Set X)) ≠ ⊥)
    (hU : ¬ OutcomeLocal.UOutcome X) {a : X} {J E : Subgroup X} (h : Config a J E)
    (hmax : LexMax a J) {S : Subgroup X}
    (hSH : S ≤ centralizer ({a} : Set X) ⊓ normalizer (J : Set X))
    (hSsyl : ∃ P : Sylow 2 ↥(centralizer ({a} : Set X) ⊓ normalizer (J : Set X)),
      (P : Subgroup _) = S.subgroupOf (centralizer ({a} : Set X) ⊓ normalizer (J : Set X)))
    (hES : E ≤ S) {y : X} (hyS : y ∈ S) {b : X} (hbS : b ∈ S) (hbE : ∀ e ∈ E, e * b = b * e)
    {M : Subgroup X} (hW : GrSLit.GSWeakCorr a J b M) (hUM : GSUnbalancingTriple b y M) :
    UnbalancedGS.GSIsoCorr a J b M := by
  obtain ⟨ha, hb, hab, hJa, hJ, hMb, hMc, hbN, hcomm, hTM⟩ := id hW
  have hM7 := h.alternating_of_target_of_footeUnbalanced hTB hSA hS hB hH hFU hHSF hCI hSol hnonab hK hz hU hb hab
    hbN hcomm hbE hUM hTM
  have hbZ : b ∉ center X := GSLit.not_mem_center_of_orderOf_eq_two hnonab hb
  obtain ⟨hTN, hTpc, ⟨φ⟩⟩ := GrSLit.gsFixedLayer_isPComponent_of_gsWeakCorr hS hK hW hbZ
  obtain ⟨-, -, heqcase⟩ := UGSChain.orbit_fixed_component_comparison ha hab hMb hMc hTN hTpc
  have hTidx : (pPrimeCore 2 (UnbalancedGS.gsFixedLayer J b)).index =
      (pPrimeCore 2 M).index := by
    rw [index_eq_card, Nat.card_congr φ.toEquiv, ← index_eq_card, h.index_eq,
      index_eq_of_alternating hM7]
  obtain ⟨hfix, hsup⟩ := heqcase hTidx
  have hC : UnbalancedGS.GSCorr a J b M :=
    ⟨ha, hb, hab, hJa, hJ, hMb, hMc, hbN, hcomm, hfix.symm⟩
  by_cases hMa : M = conjugate M a
  · rw [UnbalancedGS.gsIsoCorr_iff_sup]
    exact ⟨hC, by rw [← hMa, sup_idem], hsup hMa⟩
  · exact h.isoCorr_of_gsCorr_of_footeUnbalanced hTB hSA hS hB hH hFU hHSF hCI hSol hnonab hK hz hU hmax hSH hSsyl
      hES hyS hbS hbE hC hUM

theorem Config.exists_isoCorr_of_centralizes_of_footeUnbalanced
    (hTB : GSLit.ThompsonBurgoyneInput) (hSA : SolAltLit.SolomonAlternatingOddInput)
    (hS : SchreierFor Blueprint.Catalog) (hB : GrSLit.TheoremBReachInput)
    (hH : GSLit.HarrisInput) (hFU : FooteLit.FooteMaximalUnbalancedInput)
    (hHSF : GSLit.HarrisSolomonFritzInput) (hCI : GSLit.ClassicalInvolutionInput)
    (hSol : GrSLit.SolomonCommutingCoreInput) [IsSimpleGroup X]
    (hnonab : ∃ a b : X, a * b ≠ b * a) (hK : Assembly.KProper Blueprint.Catalog X)
    (hz : ∃ z : X, orderOf z = 2 ∧ oddCore (centralizer ({z} : Set X)) ≠ ⊥)
    (hU : ¬ OutcomeLocal.UOutcome X) {a : X} {J E : Subgroup X} (h : Config a J E)
    (hmax : LexMax a J) {S : Subgroup X}
    (hSH : S ≤ centralizer ({a} : Set X) ⊓ normalizer (J : Set X))
    (hSsyl : ∃ P : Sylow 2 ↥(centralizer ({a} : Set X) ⊓ normalizer (J : Set X)),
      (P : Subgroup _) = S.subgroupOf (centralizer ({a} : Set X) ⊓ normalizer (J : Set X)))
    (hES : E ≤ S) {e₀ : X} (he₀E : e₀ ∈ E) (he₀1 : e₀ ≠ 1) {b : X} (hb : orderOf b = 2)
    (hbS : b ∈ S) (hbK : b ∈ coreActionKernel J) (hbE : ∀ e ∈ E, e * b = b * e) :
    ∃ M : Subgroup X, UnbalancedGS.GSIsoCorr a J b M ∧ GSUnbalancingTriple b e₀ M := by
  have hU₀ := h.gsUnbalancingTriple hSol he₀E he₀1
  have hab : a * b = b * a := (mem_centralizer_singleton_iff.mp (mem_inf.mp (hSH hbS)).1).symm
  obtain ⟨hbN, hbc⟩ := mem_coreActionKernel.mp hbK
  obtain ⟨M, hW, hUM, -, -⟩ := GrSLit.exists_gsWeakCorr_of_target hS hK hU₀ hb
    (GSLit.not_mem_center_of_orderOf_eq_two hnonab hb) hab (hbE e₀ he₀E) hbN hbc
  exact ⟨M, h.isoCorr_of_centralizes_of_footeUnbalanced hTB hSA hS hB hH hFU hHSF hCI hSol hnonab hK hz hU hmax hSH
    hSsyl hES (hES he₀E) hbS hbE hW hUM, hUM⟩

theorem Config.eq_of_held_target_of_footeUnbalanced
    (hTB : GSLit.ThompsonBurgoyneInput) (hSA : SolAltLit.SolomonAlternatingOddInput)
    (hS : SchreierFor Blueprint.Catalog) (hB : GrSLit.TheoremBReachInput)
    (hH : GSLit.HarrisInput) (hFU : FooteLit.FooteMaximalUnbalancedInput)
    (hHSF : GSLit.HarrisSolomonFritzInput) (hCI : GSLit.ClassicalInvolutionInput)
    (hSol : GrSLit.SolomonCommutingCoreInput) [IsSimpleGroup X]
    (hnonab : ∃ a b : X, a * b ≠ b * a) (hK : Assembly.KProper Blueprint.Catalog X)
    (hz : ∃ z : X, orderOf z = 2 ∧ oddCore (centralizer ({z} : Set X)) ≠ ⊥)
    (hU : ¬ OutcomeLocal.UOutcome X) {a : X} {J E : Subgroup X} (h : Config a J E)
    (hmax : LexMax a J) {S : Subgroup X}
    (hSH : S ≤ centralizer ({a} : Set X) ⊓ normalizer (J : Set X))
    (hSsyl : ∃ P : Sylow 2 ↥(centralizer ({a} : Set X) ⊓ normalizer (J : Set X)),
      (P : Subgroup _) = S.subgroupOf (centralizer ({a} : Set X) ⊓ normalizer (J : Set X)))
    (hES : E ≤ S) {b y : X} {M : Subgroup X} (hbSK : b ∈ S ⊓ coreActionKernel J)
    (hUM : GSUnbalancingTriple b y M) (hMa : conjugate M a = M)
    (hTM : UnbalancedGS.gsFixedLayer J b ≤ M) (hHe : GrSLit.IsHeldType (M ⧸ Open.fusionZStar M))
    {q : X} (hq : orderOf q = 2) (hqSK : q ∈ S ⊓ coreActionKernel J) (hqb : q * b = b * q)
    (hqE : ∀ e ∈ E, e * q = q * e) : q = a := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hb, -, -, hMb, hMc, -, -⟩ := gsUnbalancingTriple_iff.mp hUM
  obtain ⟨hbS, hbK⟩ := mem_inf.mp hbSK
  obtain ⟨hbN, hbc⟩ := mem_coreActionKernel.mp hbK
  have ha := h.orderOf_eq
  have hJa := h.le_centralizer
  have hJ := h.isPComponent
  have hab : a * b = b * a := (mem_centralizer_singleton_iff.mp (mem_inf.mp (hSH hbS)).1).symm
  have hbZ : b ∉ center X := GSLit.not_mem_center_of_orderOf_eq_two hnonab hb
  have hHe' := held_equiv_of_unbalancing hTB hSA hnonab hK hz hU hUM hHe
  have hMsup : M ⊔ conjugate M a = M := by rw [hMa, sup_idem]
  have hW : GrSLit.GSWeakCorr a J b M :=
    ⟨ha, hb, hab, hJa, hJ, hMb, hMc, hbN, hbc, by rw [hMsup]; exact hTM⟩
  obtain ⟨hTN, hTpc, ⟨φ⟩⟩ := GrSLit.gsFixedLayer_isPComponent_of_gsWeakCorr hS hK hW hbZ
  rw [hMsup] at hTN hTpc
  obtain ⟨e7⟩ := h.equiv
  set T := UnbalancedGS.gsFixedLayer J b with hTdef
  have hT7 : Nonempty (↥T ⧸ pPrimeCore 2 ↥T ≃* alternatingGroup (Fin 7)) := ⟨φ.trans e7⟩
  have hTperf : ⁅T, T⁆ = T := GSThmB.commutator_eq_self_of_isPComponent hTN hTpc
  have hTO : ¬ T ≤ (pPrimeCore 2 (centralizer ({b} : Set X))).map
      (centralizer ({b} : Set X)).subtype := by
    obtain ⟨e⟩ := hT7
    have : Nontrivial (alternatingGroup (Fin 7)) :=
      alternatingGroup.nontrivial_of_three_le_card (by simp)
    exact not_le_oddIn_of_nontrivial e.toEquiv.nontrivial
  have hawN : a ∈ normalizer (M : Set X) := mem_normalizer_of_conjugate_eq hMa
  have houter : ∀ (w : X) (hw2 : orderOf w = 2), w ∈ S ⊓ coreActionKernel J → w * b = b * w →
      (∀ e ∈ E, e * w = w * e) → ∃ hwM : w ∈ normalizer (M : Set X),
        oddQuotConj M ⟨w, hwM⟩ ∉ (MulAut.conj : (↥M ⧸ pPrimeCore 2 ↥M) →*
          MulAut (↥M ⧸ pPrimeCore 2 ↥M)).range := by
    intro w hw2 hwSK hwb hwE
    obtain ⟨hwS, hwK⟩ := mem_inf.mp hwSK
    obtain ⟨hwN, hwc⟩ := mem_coreActionKernel.mp hwK
    have hww : w * w = 1 := by rw [← pow_two, ← hw2, pow_orderOf_eq_one]
    have hwa : a * w = w * a := (mem_centralizer_singleton_iff.mp (mem_inf.mp (hSH hwS)).1).symm
    obtain ⟨e₀, he₀E, he₀1, -⟩ := h.exists_involution
    obtain ⟨Kw, hKiso, -⟩ := h.exists_isoCorr_of_centralizes_of_footeUnbalanced hTB hSA hS hB hH hFU hHSF hCI hSol
      hnonab hK hz hU hmax hSH hSsyl hES he₀E he₀1 hw2 hwS hwK hwE
    have hwCb : w ∈ centralizer ({b} : Set X) := mem_centralizer_singleton_iff.mpr hwb
    have hwT : w ∈ normalizer (T : Set X) := by
      have : (pLayer ↥(J ⊓ centralizer ({b} : Set X)) 2).Characteristic :=
        CatalogueBPrimeJoin.pLayer_characteristic
      exact UnbalancedGS.normalizer_le_normalizer_map_of_characteristic
        (J ⊓ centralizer ({b} : Set X)) (pLayer ↥(J ⊓ centralizer ({b} : Set X)) 2)
        (normalizer_inf_mem hwN (Subgroup.le_normalizer hwCb))
    have hwM : w ∈ normalizer (M : Set X) :=
      mem_normalizer_of_le hMb hMc hTM hTperf hTO hwCb hwT
    refine ⟨hwM, ?_⟩
    obtain ⟨hAN, -, -, -, -, -, -, hset, -⟩ :=
      isomorphic_correspondence_sylow_growth hKiso rfl rfl rfl rfl
    have hbA : b ∈ centralizer ({w} : Set X) ⊓ normalizer (J : Set X) :=
      mem_inf.mpr ⟨mem_centralizer_singleton_iff.mpr hwb.symm, hbN⟩
    have hbK' : b ∈ coreActionKernel Kw := by
      have h1 : b ∈ {g | g ∈ centralizer ({w} : Set X) ⊓ normalizer (J : Set X) ∧
          ∀ j ∈ J, j⁻¹ * g⁻¹ * j * g ∈ (pPrimeCore 2 J).map J.subtype} := ⟨hbA, hbc⟩
      rw [hset] at h1
      exact mem_coreActionKernel.mpr ⟨hAN hbA, h1.2⟩
    have hVM := fixedLayer_le_of_isoCorr hS hK hKiso hW hwb hbZ hbK hbK'
    rw [hMsup] at hVM
    obtain ⟨-, -, -, -, -, hKw, hKwc, -, -, -⟩ := hKiso.1
    obtain ⟨hbNK, hbcK⟩ := mem_coreActionKernel.mp hbK'
    have hMw : conjugate M w = M := conjugate_eq_of_mem_normalizer hwM
    have hW' : GrSLit.GSWeakCorr w Kw b M :=
      ⟨hw2, hb, hwb, hKw, hKwc, hMb, hMc, hbNK, hbcK, by rw [hMw, sup_idem]; exact hVM⟩
    obtain ⟨hVN, hVpc, ⟨ψ⟩⟩ := GrSLit.gsFixedLayer_isPComponent_of_gsWeakCorr hS hK hW' hbZ
    rw [hMw, sup_idem] at hVN hVpc
    obtain ⟨e7'⟩ := (config_of_isoCorr hSol h hw2 hwc hwE hKiso).equiv
    exact not_mem_conj_range_of_fixed_alternating GrSLit.HeldFix.isL34Type_of_isPComponent_centralizer_heA0
        GrSLit.HeldFix.not_isPComponent_centralizer_heT1P hHe'
      hwM hww hVN hVpc (nonempty_fusionZStar_equiv_alternating ⟨ψ.trans e7'⟩)
  have haa : a * a = 1 := by rw [← pow_two, ← ha, pow_orderOf_eq_one]
  have hσa := not_mem_conj_range_of_fixed_alternating GrSLit.HeldFix.isL34Type_of_isPComponent_centralizer_heA0
      GrSLit.HeldFix.not_isPComponent_centralizer_heT1P
    hHe' hawN haa hTN hTpc (nonempty_fusionZStar_equiv_alternating hT7)
  by_contra hqa
  obtain ⟨hqS, hqK⟩ := mem_inf.mp hqSK
  have hqa' : a * q = q * a := (mem_centralizer_singleton_iff.mp (mem_inf.mp (hSH hqS)).1).symm
  obtain ⟨hqM, hσq⟩ := houter q hq hqSK hqb hqE
  have haS : a ∈ S := (mem_inf.mp (mem_inf_coreActionKernel_of_sylow ha hJa hSsyl)).1
  have haK : a ∈ coreActionKernel J :=
    (mem_inf.mp (mem_inf.mp (mem_inf_coreActionKernel_of_sylow ha hJa hSsyl)).2).2
  have hqq : q * q = 1 := by rw [← pow_two, ← hq, pow_orderOf_eq_one]
  have haq2 : orderOf (a * q) = 2 := by
    refine orderOf_eq_prime ?_ fun h1 => hqa ?_
    · rw [pow_two]
      calc a * q * (a * q) = a * (q * a) * q := by group
        _ = a * (a * q) * q := by rw [hqa']
        _ = (a * a) * (q * q) := by group
        _ = 1 := by rw [haa, hqq, one_mul]
    · calc q = a⁻¹ * (a * q) := by group
        _ = a := by rw [h1, mul_one, inv_eq_of_mul_eq_one_right haa]
  have haqE : ∀ e ∈ E, e * (a * q) = a * q * e := by
    intro e he
    have hea : e * a = a * e := mem_centralizer_singleton_iff.mp (mem_inf.mp (h.le_H he)).1
    calc e * (a * q) = (e * a) * q := by group
      _ = a * (e * q) := by rw [hea]; group
      _ = a * (q * e) := by rw [hqE e he]
      _ = a * q * e := by group
  have haqb : a * q * b = b * (a * q) := by
    calc a * q * b = a * (q * b) := by group
      _ = a * (b * q) := by rw [hqb]
      _ = (a * b) * q := by group
      _ = b * (a * q) := by rw [hab]; group
  obtain ⟨haqM, hσaq⟩ := houter (a * q) haq2 (mul_mem (mem_inf.mpr ⟨haS, haK⟩) hqSK) haqb haqE
  apply hσaq
  have hmul : (⟨a * q, haqM⟩ : ↥(normalizer (M : Set X))) = ⟨a, hawN⟩ * ⟨q, hqM⟩ := rfl
  rw [hmul, map_mul]
  obtain ⟨θ₀⟩ := hHe'
  exact held_mul_mem_conj_range θ₀ hσa hσq

theorem Config.eq_of_diagonal_target_of_footeUnbalanced
    (hTB : GSLit.ThompsonBurgoyneInput) (hSA : SolAltLit.SolomonAlternatingOddInput)
    (hS : SchreierFor Blueprint.Catalog) (hB : GrSLit.TheoremBReachInput)
    (hH : GSLit.HarrisInput) (hFU : FooteLit.FooteMaximalUnbalancedInput)
    (hHSF : GSLit.HarrisSolomonFritzInput) (hCI : GSLit.ClassicalInvolutionInput)
    (hSol : GrSLit.SolomonCommutingCoreInput) [IsSimpleGroup X]
    (hnonab : ∃ a b : X, a * b ≠ b * a) (hK : Assembly.KProper Blueprint.Catalog X)
    (hz : ∃ z : X, orderOf z = 2 ∧ oddCore (centralizer ({z} : Set X)) ≠ ⊥)
    (hU : ¬ OutcomeLocal.UOutcome X) {a : X} {J E : Subgroup X} (h : Config a J E)
    (hmax : LexMax a J) {S : Subgroup X}
    (hSH : S ≤ centralizer ({a} : Set X) ⊓ normalizer (J : Set X))
    (hSsyl : ∃ P : Sylow 2 ↥(centralizer ({a} : Set X) ⊓ normalizer (J : Set X)),
      (P : Subgroup _) = S.subgroupOf (centralizer ({a} : Set X) ⊓ normalizer (J : Set X)))
    (hES : E ≤ S) {b : X} {M : Subgroup X} (hb : orderOf b = 2)
    (hbSK : b ∈ S ⊓ coreActionKernel J) (hMb : M ≤ centralizer ({b} : Set X))
    (hMc : IsPComponent 2 (M.subgroupOf (centralizer ({b} : Set X))))
    (hMa : conjugate M a ≠ M) (hTM : gsFixedLayer J b ≤ M ⊔ conjugate M a) {q : X}
    (hq : orderOf q = 2) (hqSK : q ∈ S ⊓ coreActionKernel J) (hqb : q * b = b * q)
    (hqE : ∀ e ∈ E, e * q = q * e) : q = a := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hbS, hbK⟩ := mem_inf.mp hbSK
  obtain ⟨hbN, hbc⟩ := mem_coreActionKernel.mp hbK
  have ha := h.orderOf_eq
  have hJa := h.le_centralizer
  have hJ := h.isPComponent
  have haa : a * a = 1 := by rw [← pow_two, ← ha, pow_orderOf_eq_one]
  have hab : a * b = b * a := (mem_centralizer_singleton_iff.mp (mem_inf.mp (hSH hbS)).1).symm
  have hbZ : b ∉ center X := GSLit.not_mem_center_of_orderOf_eq_two hnonab hb
  have hcc : ∀ (K : Subgroup X) {g : X}, g * g = 1 → conjugate (conjugate K g) g = K :=
    fun K g hg => by rw [conjugate_conjugate, hg, conjugate_one]
  have hcmono : ∀ {K L : Subgroup X} (g : X), K ≤ L → conjugate K g ≤ conjugate L g :=
    fun g hKL x hx => mem_conjugate_iff.mpr (hKL (mem_conjugate_iff.mp hx))
  obtain ⟨hMab, hMac⟩ := UGSChain.conjugate_isPComponent_centralizer hab hMb hMc
  have hW : GrSLit.GSWeakCorr a J b M := ⟨ha, hb, hab, hJa, hJ, hMb, hMc, hbN, hbc, hTM⟩
  have h7nt : Nontrivial (alternatingGroup (Fin 7)) :=
    alternatingGroup.nontrivial_of_three_le_card (by simp)
  have hmove : ∀ w : X, orderOf w = 2 → w ∈ S ⊓ coreActionKernel J → w * b = b * w →
      (∀ e ∈ E, e * w = w * e) → conjugate M w ≠ M := by
    intro w hw2 hwSK hwb hwE hMw
    obtain ⟨hwS, hwK⟩ := mem_inf.mp hwSK
    obtain ⟨hwN, hwc⟩ := mem_coreActionKernel.mp hwK
    have hww : w * w = 1 := by rw [← pow_two, ← hw2, pow_orderOf_eq_one]
    have hwa : a * w = w * a := (mem_centralizer_singleton_iff.mp (mem_inf.mp (hSH hwS)).1).symm
    obtain ⟨e₀, he₀E, he₀1, -⟩ := h.exists_involution
    obtain ⟨Kw, hKiso, -⟩ := h.exists_isoCorr_of_centralizes_of_footeUnbalanced hTB hSA hS hB hH hFU hHSF hCI hSol
      hnonab hK hz hU hmax hSH hSsyl hES he₀E he₀1 hw2 hwS hwK hwE
    obtain ⟨hAN, -, -, -, -, -, -, hset, -⟩ :=
      isomorphic_correspondence_sylow_growth hKiso rfl rfl rfl rfl
    have hbA : b ∈ centralizer ({w} : Set X) ⊓ normalizer (J : Set X) :=
      mem_inf.mpr ⟨mem_centralizer_singleton_iff.mpr hwb.symm, hbN⟩
    have hbK' : b ∈ coreActionKernel Kw := by
      have h1 : b ∈ {g | g ∈ centralizer ({w} : Set X) ⊓ normalizer (J : Set X) ∧
          ∀ j ∈ J, j⁻¹ * g⁻¹ * j * g ∈ (pPrimeCore 2 J).map J.subtype} := ⟨hbA, hbc⟩
      rw [hset] at h1
      exact mem_coreActionKernel.mpr ⟨hAN hbA, h1.2⟩
    obtain ⟨⟨-, -, -, -, -, hKw, hKwc, -, -, -⟩, hKwa, -⟩ := id hKiso
    have hVM := fixedLayer_le_of_isoCorr hS hK hKiso hW hwb hbZ hbK hbK'
    have hKww : conjugate Kw w = Kw := conjugate_eq_self_of_le_centralizer hKw
    have hKe : ∀ k ∈ Kw ⊔ conjugate Kw w, k⁻¹ * b⁻¹ * k * b ∈
        (pPrimeCore 2 (centralizer ({w} : Set X))).map (centralizer ({w} : Set X)).subtype := by
      rw [hKww, sup_idem]
      intro k hk
      exact GSLit.map_pPrimeCore_le_of_isPComponent hKw hKwc
        ((mem_coreActionKernel.mp hbK').2 k hk)
    obtain ⟨-, -, -, -, hVwb, hVpc, hVV, hVE, -, -, ψ, -⟩ :=
      UGSChain.kProper_core_trivial_orbit_fixed_layer_containment_of_schreier hS hK (a := w)
        (b := w) (e := b) hw2 hb rfl hwb hbZ hKw hKwc hKe
    set V := gsFixedLayer Kw b with hVdef
    obtain ⟨e7⟩ := (config_of_isoCorr hSol h hw2 hwc hwE hKiso).equiv
    have hVO : ¬ V ≤ (pPrimeCore 2 (centralizer ({b} : Set X))).map
        (centralizer ({b} : Set X)).subtype :=
      not_le_oddIn_of_nontrivial (ψ.trans e7).toEquiv.nontrivial
    have hVperf : ⁅V, V⁆ = V := gsFixedLayer_perfect Kw b
    have hKa : conjugate Kw a ≤ Kw := le_sup_right.trans hKwa.le
    have haKw : conjugate Kw a = Kw := le_antisymm hKa (by
      have h1 := hcmono a hKa
      rwa [hcc Kw haa] at h1)
    have hVa : conjugate V a = V := conjugate_eq_of_mem_normalizer
      (UnbalancedGS.mem_normalizer_gsFixedLayer (mem_normalizer_of_conjugate_eq haKw)
        (mem_centralizer_singleton_iff.mpr hab))
    have key : ∀ {N₀ : Subgroup X}, N₀ ≤ centralizer ({b} : Set X) →
        IsPComponent 2 (N₀.subgroupOf (centralizer ({b} : Set X))) → N₀ ≠ conjugate N₀ a →
        ¬ V ≤ N₀ := by
      intro N₀ hN₀b hN₀c hN₀ne hVN₀
      obtain ⟨hN₀ab, hN₀ac⟩ := UGSChain.conjugate_isPComponent_centralizer hab hN₀b hN₀c
      have hVN₀a : V ≤ conjugate N₀ a := by
        rw [← hVa]
        exact hcmono a hVN₀
      apply hVO
      rw [← hVperf]
      exact (commutator_mono hVN₀ hVN₀a).trans
        (commutator_le_oddIn_of_ne hN₀b hN₀ab hN₀c hN₀ac hN₀ne)
    obtain ⟨N, hNb, hNc, hVN, -⟩ :=
      UGSChain.exists_orbit_component_of_le_pLayer hw2 hwb hVwb hVpc (hVV.trans hVE)
    obtain ⟨hNwb, hNwc⟩ := UGSChain.conjugate_isPComponent_centralizer hwb hNb hNc
    have hMaw : conjugate (conjugate M a) w = conjugate M a := by
      rw [conjugate_conjugate, hwa, ← conjugate_conjugate, hMw]
    have hMa' : conjugate M a ≠ conjugate (conjugate M a) a := by
      rw [hcc M haa]
      exact hMa
    rcases eq_or_eq_of_le_sup_sup hNb hNwb hMb hMab hNc hNwc hMc hMac hVN hVM hVperf hVO with
      hh | hh | hh | hh
    · rw [hh, hMw, sup_idem] at hVN
      exact key hMb hMc (Ne.symm hMa) hVN
    · rw [hh, hMaw, sup_idem] at hVN
      exact key hMab hMac hMa' hVN
    · have hN : N = M := by rw [← hcc N hww, hh, hMw]
      rw [hN, hMw, sup_idem] at hVN
      exact key hMb hMc (Ne.symm hMa) hVN
    · have hN : N = conjugate M a := by rw [← hcc N hww, hh, hMaw]
      rw [hN, hMaw, sup_idem] at hVN
      exact key hMab hMac hMa' hVN
  by_contra hqa
  obtain ⟨hqS, hqK⟩ := mem_inf.mp hqSK
  obtain ⟨hqN, -⟩ := mem_coreActionKernel.mp hqK
  have hqa' : a * q = q * a := (mem_centralizer_singleton_iff.mp (mem_inf.mp (hSH hqS)).1).symm
  have hMq := hmove q hq hqSK hqb hqE
  obtain ⟨-, -, ⟨φ⟩⟩ := GrSLit.gsFixedLayer_isPComponent_of_gsWeakCorr hS hK hW hbZ
  obtain ⟨e7⟩ := h.equiv
  have hTperf := gsFixedLayer_perfect J b
  have hTO : ¬ gsFixedLayer J b ≤ (pPrimeCore 2 (centralizer ({b} : Set X))).map
      (centralizer ({b} : Set X)).subtype :=
    not_le_oddIn_of_nontrivial (φ.trans e7).toEquiv.nontrivial
  have hTq : conjugate (gsFixedLayer J b) q = gsFixedLayer J b := conjugate_eq_of_mem_normalizer
    (UnbalancedGS.mem_normalizer_gsFixedLayer hqN (mem_centralizer_singleton_iff.mpr hqb))
  obtain ⟨hMqb, hMqc⟩ := UGSChain.conjugate_isPComponent_centralizer hqb hMb hMc
  obtain ⟨hMaqb, hMaqc⟩ := UGSChain.conjugate_isPComponent_centralizer hqb hMab hMac
  have hTMq : gsFixedLayer J b ≤ conjugate M q ⊔ conjugate (conjugate M a) q := by
    rw [← hTq, ← UnbalancedLayer.conjugate_sup]
    exact hcmono q hTM
  have haS : a ∈ S := (mem_inf.mp (mem_inf_coreActionKernel_of_sylow ha hJa hSsyl)).1
  have haK : a ∈ coreActionKernel J :=
    (mem_inf.mp (mem_inf.mp (mem_inf_coreActionKernel_of_sylow ha hJa hSsyl)).2).2
  have hqq : q * q = 1 := by rw [← pow_two, ← hq, pow_orderOf_eq_one]
  have haq2 : orderOf (a * q) = 2 := by
    refine orderOf_eq_prime ?_ fun h1 => hqa ?_
    · rw [pow_two]
      calc a * q * (a * q) = a * (q * a) * q := by group
        _ = a * (a * q) * q := by rw [hqa']
        _ = (a * a) * (q * q) := by group
        _ = 1 := by rw [haa, hqq, one_mul]
    · calc q = a⁻¹ * (a * q) := by group
        _ = a := by rw [h1, mul_one, inv_eq_of_mul_eq_one_right haa]
  have haqE : ∀ e ∈ E, e * (a * q) = a * q * e := by
    intro e he
    have hea : e * a = a * e := mem_centralizer_singleton_iff.mp (mem_inf.mp (h.le_H he)).1
    calc e * (a * q) = (e * a) * q := by group
      _ = a * (e * q) := by rw [hea]; group
      _ = a * (q * e) := by rw [hqE e he]
      _ = a * q * e := by group
  have haqb : a * q * b = b * (a * q) := by
    calc a * q * b = a * (q * b) := by group
      _ = a * (b * q) := by rw [hqb]
      _ = (a * b) * q := by group
      _ = b * (a * q) := by rw [hab]; group
  have hMaq := hmove (a * q) haq2 (mul_mem (mem_inf.mpr ⟨haS, haK⟩) hqSK) haqb haqE
  rcases eq_or_eq_of_le_sup_sup hMb hMab hMqb hMaqb hMc hMac hMqc hMaqc hTM hTMq hTperf hTO with
    hh | hh | hh | hh
  · exact hMq hh.symm
  · apply hMaq
    rw [← conjugate_conjugate]
    exact hh.symm
  · apply hMaq
    rw [hqa', ← conjugate_conjugate, ← hh, hcc M haa]
  · apply hMq
    have h1 := congrArg (fun K => conjugate K a) hh
    simp only [conjugate_conjugate] at h1
    rw [haa, conjugate_one, hqa', mul_assoc, haa, mul_one] at h1
    exact h1.symm

theorem Config.isoCorr_of_weak_of_footeUnbalanced
    (hTB : GSLit.ThompsonBurgoyneInput) (hSA : SolAltLit.SolomonAlternatingOddInput)
    (hS : SchreierFor Blueprint.Catalog) (hB : GrSLit.TheoremBReachInput)
    (hH : GSLit.HarrisInput) (hFU : FooteLit.FooteMaximalUnbalancedInput)
    (hHSF : GSLit.HarrisSolomonFritzInput) (hCI : GSLit.ClassicalInvolutionInput)
    (hSol : GrSLit.SolomonCommutingCoreInput) (hN1 : CorCHeldTargetStep)
    (hN2 : CorCDiagonalStep) [IsSimpleGroup X]
    (hnonab : ∃ a b : X, a * b ≠ b * a) (hK : Assembly.KProper Blueprint.Catalog X)
    (hz : ∃ z : X, orderOf z = 2 ∧ oddCore (centralizer ({z} : Set X)) ≠ ⊥)
    (hU : ¬ OutcomeLocal.UOutcome X) {a : X} {J E : Subgroup X} (h : Config a J E)
    (hmax : LexMax a J) {S : Subgroup X}
    (hSH : S ≤ centralizer ({a} : Set X) ⊓ normalizer (J : Set X))
    (hSsyl : ∃ P : Sylow 2 ↥(centralizer ({a} : Set X) ⊓ normalizer (J : Set X)),
      (P : Subgroup _) = S.subgroupOf (centralizer ({a} : Set X) ⊓ normalizer (J : Set X)))
    (hES : E ≤ S) {y : X} (hyS : y ∈ S) {b : X} (hb : orderOf b = 2) (hbS : b ∈ S)
    (hbK : b ∈ coreActionKernel J) {M : Subgroup X} (hW : GrSLit.GSWeakCorr a J b M)
    (hUM : GSUnbalancingTriple b y M) : UnbalancedGS.GSIsoCorr a J b M := by
  by_cases hbE : ∀ e ∈ E, e * b = b * e
  · exact h.isoCorr_of_centralizes_of_footeUnbalanced hTB hSA hS hB hH hFU hHSF hCI hSol hnonab hK hz hU hmax hSH
      hSsyl hES hyS hbS hbE hW hUM
  obtain ⟨ha, -, hab, hJa, hJ, hMb, hMc, hbN, hcomm, -⟩ := id hW
  have hbZ : b ∉ center X := GSLit.not_mem_center_of_orderOf_eq_two hnonab hb
  obtain ⟨hTN, hTpc, ⟨φ⟩⟩ := GrSLit.gsFixedLayer_isPComponent_of_gsWeakCorr hS hK hW hbZ
  obtain ⟨hidxle, -, heqcase⟩ := UGSChain.orbit_fixed_component_comparison ha hab hMb hMc hTN hTpc
  obtain ⟨e7⟩ := h.equiv
  have hT7 : Nonempty (UnbalancedGS.gsFixedLayer J b ⧸
      pPrimeCore 2 (UnbalancedGS.gsFixedLayer J b) ≃* alternatingGroup (Fin 7)) := ⟨φ.trans e7⟩
  have hbSK : b ∈ S ⊓ coreActionKernel J := mem_inf.mpr ⟨hbS, hbK⟩
  by_cases hMa : M = conjugate M a
  · by_cases hidx : (pPrimeCore 2 (UnbalancedGS.gsFixedLayer J b)).index =
        (pPrimeCore 2 M).index
    · obtain ⟨hfix, hsup⟩ := heqcase hidx
      rw [UnbalancedGS.gsIsoCorr_iff_sup]
      exact ⟨⟨ha, hb, hab, hJa, hJ, hMb, hMc, hbN, hcomm, hfix.symm⟩, by rw [← hMa, sup_idem],
        hsup hMa⟩
    · exfalso
      have hlt := lt_of_le_of_ne hidxle hidx
      rw [← hMa, sup_idem] at hTN hTpc
      have hR := GrSLit.gsRestrictedType_of_gsUnbalancingTriple_of_footeUnbalanced hTB hSA hS hB hH hFU hHSF hCI
        (GrSLit.heldFixedInput_of_inner GrSLit.HeldFix.isL34Type_of_isPComponent_centralizer_heA0
            GrSLit.HeldFix.not_isPComponent_centralizer_heT1P)
        GrSLit.l34FixedInput GrSLit.a7FixedInput GrSLit.l2FixedInput hnonab hK hz hU hUM
      rcases hR with hHe | h34 | h7' | h5 | h7''
      · exact hN1 X hnonab hK hz hU a J E h hmax S hSH hSsyl hES b y M hb hbSK hbE hyS hUM
          hMa.symm (hTN.trans inf_le_left) hlt hHe
      · rcases GrSLit.l34FixedInput X a b M _ ha hb hab hMb hMc hMa.symm hTN hTpc hlt h34 with
          h5 | h7
        · exact not_isL2Type_of_alternating (by norm_num) hT7 h5
        · exact not_isL2Type_of_alternating (by norm_num) hT7 h7
      · exact not_isL2Type_of_alternating (by norm_num) hT7
          (GrSLit.a7FixedInput X a b M _ ha hb hab hMb hMc hMa.symm hTN hTpc hlt h7')
      · exact GrSLit.l2FixedInput.1 X a b M _ ha hb hab hMb hMc hMa.symm hTN hTpc hlt h5
      · exact GrSLit.l2FixedInput.2 X a b M _ ha hb hab hMb hMc hMa.symm hTN hTpc hlt h7''
  · exfalso
    rcases GrSLit.gsWeakCorr_type_dichotomy hS hK hW hbZ with heJM | ⟨hMa', -⟩
    · obtain ⟨eJM⟩ := heJM
      have hZJ := fusionZStar_eq_of_alternating h.equiv
      exact hN2 X hnonab hK hz hU a J E h hmax S hSH hSsyl hES b y M hb hbSK hbE hyS hUM
        (fun h' => hMa h'.symm) hW.2.2.2.2.2.2.2.2.2
        ⟨eJM.symm.trans ((QuotientGroup.quotientMulEquivOfEq hZJ).trans e7)⟩
    · exact hMa hMa'.symm

theorem Config.gsMaximalUnbalancingTriple_of_steps_of_footeUnbalanced
    (hTB : GSLit.ThompsonBurgoyneInput) (hSA : SolAltLit.SolomonAlternatingOddInput)
    (hS : SchreierFor Blueprint.Catalog) (hB : GrSLit.TheoremBReachInput)
    (hH : GSLit.HarrisInput) (hFU : FooteLit.FooteMaximalUnbalancedInput)
    (hHSF : GSLit.HarrisSolomonFritzInput) (hCI : GSLit.ClassicalInvolutionInput)
    (hSol : GrSLit.SolomonCommutingCoreInput) (hN1 : CorCHeldTargetStep)
    (hN2 : CorCDiagonalStep) [IsSimpleGroup X]
    (hnonab : ∃ a b : X, a * b ≠ b * a) (hK : Assembly.KProper Blueprint.Catalog X)
    (hz : ∃ z : X, orderOf z = 2 ∧ oddCore (centralizer ({z} : Set X)) ≠ ⊥)
    (hU : ¬ OutcomeLocal.UOutcome X) {a : X} {J E : Subgroup X} (h : Config a J E)
    (hmax : LexMax a J) {e₀ : X} (he₀E : e₀ ∈ E) (he₀1 : e₀ ≠ 1) :
    GSMaximalUnbalancingTriple a e₀ J := by
  refine ⟨h.gsUnbalancingTriple hSol he₀E he₀1, fun b L hb hba hC =>
    ⟨fun y hy hUL => ?_, fun S hSH hSsyl hbS hbc => ?_⟩⟩
  ·
    obtain ⟨-, -, -, -, -, -, -, hbN, hcomm, -⟩ := id hC
    have hbb : b * b = 1 := by rw [← pow_two, ← hb, pow_orderOf_eq_one]
    have hyy : y * y = 1 := by rw [← pow_two, ← hUL.2.1, pow_orderOf_eq_one]
    have hbH : b ∈ centralizer ({a} : Set X) ⊓ normalizer (J : Set X) := mem_inf.mpr ⟨hba, hbN⟩
    have hle : closure ({b, y} : Set X) ≤ centralizer ({a} : Set X) ⊓ normalizer (J : Set X) := by
      rw [closure_le]
      rintro _ (rfl | rfl)
      · exact hbH
      · exact hy
    obtain ⟨S, hSH, hSsyl, hbyS⟩ :=
      UGSChain.exists_sylow_two_le hle (isPGroup_closure_pair hbb hyy hUL.2.2.1)
    have hbS : b ∈ S := hbyS (subset_closure (Set.mem_insert b {y}))
    have hyS : y ∈ S := hbyS (subset_closure (Set.mem_insert_of_mem b (Set.mem_singleton y)))
    obtain ⟨E', hE', hE'S⟩ := h.exists_le_sylow hSsyl
    exact hE'.isoCorr_of_weak_of_footeUnbalanced hTB hSA hS hB hH hFU hHSF hCI hSol hN1 hN2 hnonab hK hz hU hmax hSH
      hSsyl hE'S hyS hb hbS (mem_coreActionKernel.mpr ⟨hbN, hcomm⟩) (GrSLit.GSWeakCorr.of_gsCorr hC)
      hUL
  ·
    obtain ⟨E', hE', hE'S⟩ := h.exists_le_sylow hSsyl
    obtain ⟨ha, -, hab, hJa, hJ, -, -, hbN, hcomm, -⟩ := id hC
    have hbK : b ∈ coreActionKernel J := mem_coreActionKernel.mpr ⟨hbN, hcomm⟩
    obtain ⟨e₁, he₁E, he₁1, -⟩ := hE'.exists_involution
    obtain ⟨K, hKiso, -⟩ := hE'.exists_isoCorr_of_centralizes_of_footeUnbalanced hTB hSA hS hB hH hFU hHSF hCI hSol
      hnonab hK hz hU hmax hSH hSsyl hE'S he₁E he₁1 hb hbS hbK fun e he => hbc e (hE'S he)
    have hLK : L = K := by
      rcases GrSLit.diamond_target_weak (GSLit.gsIsoCorr_self ha hJa hJ)
          (GrSLit.GSWeakCorr.of_gsCorr hC) hKiso hab hbK hbK with hKL | hKL
      · exact hKL.symm
      · have haa : a * a = 1 := by rw [← pow_two, ← ha, pow_orderOf_eq_one]
        have hKa := conjugate_eq_of_sup_eq (UnbalancedGS.gsIsoCorr_iff_sup.mp hKiso).2.1
        rw [← hKa, hKL, conjugate_conjugate, haa, conjugate_one]
    rw [hLK]
    exact centralLex hSol hE' hmax hSH hSsyl hE'S b K hb hcomm hKiso hbc

theorem Config.isoInput_of_steps_of_footeUnbalanced
    (hTB : GSLit.ThompsonBurgoyneInput) (hSA : SolAltLit.SolomonAlternatingOddInput)
    (hS : SchreierFor Blueprint.Catalog) (hB : GrSLit.TheoremBReachInput)
    (hH : GSLit.HarrisInput) (hFU : FooteLit.FooteMaximalUnbalancedInput)
    (hHSF : GSLit.HarrisSolomonFritzInput) (hCI : GSLit.ClassicalInvolutionInput)
    (hSol : GrSLit.SolomonCommutingCoreInput) (hN1 : CorCHeldTargetStep)
    (hN2 : CorCDiagonalStep) [IsSimpleGroup X]
    (hnonab : ∃ a b : X, a * b ≠ b * a) (hK : Assembly.KProper Blueprint.Catalog X)
    (hz : ∃ z : X, orderOf z = 2 ∧ oddCore (centralizer ({z} : Set X)) ≠ ⊥)
    (hU : ¬ OutcomeLocal.UOutcome X) {a : X} {J E : Subgroup X} (h : Config a J E)
    (hmax : LexMax a J) :
    ∀ y b : X, y ∈ centralizer ({a} : Set X) ⊓ normalizer (J : Set X) →
      GSUnbalancingTriple a y J → orderOf b = 2 → a * b = b * a → y * b = b * y →
      b ∈ coreActionKernel J →
      ∃ M : Subgroup X, UnbalancedGS.GSIsoCorr a J b M ∧ GSUnbalancingTriple b y M := by
  intro y b hy hUy hb hab hyb hbK
  obtain ⟨hbN, hbc⟩ := mem_coreActionKernel.mp hbK
  obtain ⟨M, hW, hUM, -, -⟩ := GrSLit.exists_gsWeakCorr_of_target hS hK hUy hb
    (GSLit.not_mem_center_of_orderOf_eq_two hnonab hb) hab hyb hbN hbc
  have hbb : b * b = 1 := by rw [← pow_two, ← hb, pow_orderOf_eq_one]
  have hyy : y * y = 1 := by rw [← pow_two, ← hUy.2.1, pow_orderOf_eq_one]
  have hbH : b ∈ centralizer ({a} : Set X) ⊓ normalizer (J : Set X) :=
    mem_inf.mpr ⟨mem_centralizer_singleton_iff.mpr hab.symm, hbN⟩
  have hle : closure ({b, y} : Set X) ≤ centralizer ({a} : Set X) ⊓ normalizer (J : Set X) := by
    rw [closure_le]
    rintro _ (rfl | rfl)
    · exact hbH
    · exact hy
  obtain ⟨S, hSH, hSsyl, hbyS⟩ :=
    UGSChain.exists_sylow_two_le hle (isPGroup_closure_pair hbb hyy hyb.symm)
  have hbS : b ∈ S := hbyS (subset_closure (Set.mem_insert b {y}))
  have hyS : y ∈ S := hbyS (subset_closure (Set.mem_insert_of_mem b (Set.mem_singleton y)))
  obtain ⟨E', hE', hE'S⟩ := h.exists_le_sylow hSsyl
  exact ⟨M, hE'.isoCorr_of_weak_of_footeUnbalanced hTB hSA hS hB hH hFU hHSF hCI hSol hN1 hN2 hnonab hK hz hU hmax
    hSH hSsyl hE'S hyS hb hbS hbK hW hUM, hUM⟩

end

end CorC

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)

theorem corCHeldTargetStep_holds_of_footeUnbalanced
    (hTB : GSLit.ThompsonBurgoyneInput) (hSA : SolAltLit.SolomonAlternatingOddInput)
    (hS : SchreierFor Blueprint.Catalog) (hB : GrSLit.TheoremBReachInput)
    (hH : GSLit.HarrisInput) (hFU : FooteLit.FooteMaximalUnbalancedInput)
    (hHSF : GSLit.HarrisSolomonFritzInput) (hCI : GSLit.ClassicalInvolutionInput)
    (hSol : GrSLit.SolomonCommutingCoreInput) : CorCHeldTargetStep := by
  intro X _ _ _ hnonab hK hz hU a J E h hmax S hSH hSsyl hES b y M hb hbSK hbE _ hUM hMa hTM _
    hHe
  obtain ⟨hbS, hbK⟩ := mem_inf.mp hbSK
  have hab : a * b = b * a :=
    (mem_centralizer_singleton_iff.mp (mem_inf.mp (hSH hbS)).1).symm
  exact h.false_of_fusion hSH hSsyl hES hbSK hbE
    (fun q hqSK hq hqS => h.eq_of_held_target_of_footeUnbalanced hTB hSA hS hB hH hFU hHSF hCI hSol hnonab hK hz hU
      hmax hSH hSsyl hES hbSK hUM hMa hTM hHe hq hqSK (hqS b hbS).symm
      fun e he => hqS e (hES he))
    (fun z hzSJ hz2 hzS => h.held_fusion hTB hSA hS hnonab hK hz hU hb hbK hab hUM hMa hTM hHe
      (mem_inf.mp hzSJ).2 hz2 (hzS b hbS).symm)

theorem corCDiagonalStep_holds_of_footeUnbalanced
    (hTB : GSLit.ThompsonBurgoyneInput) (hSA : SolAltLit.SolomonAlternatingOddInput)
    (hS : SchreierFor Blueprint.Catalog) (hB : GrSLit.TheoremBReachInput)
    (hH : GSLit.HarrisInput) (hFU : FooteLit.FooteMaximalUnbalancedInput)
    (hHSF : GSLit.HarrisSolomonFritzInput) (hCI : GSLit.ClassicalInvolutionInput)
    (hSol : GrSLit.SolomonCommutingCoreInput) : CorCDiagonalStep := by
  intro X _ _ _ hnonab hK hz hU a J E h hmax S hSH hSsyl hES b y M hb hbSK hbE _ hUM hMa hTM h7
  obtain ⟨hbS, hbK⟩ := mem_inf.mp hbSK
  obtain ⟨-, -, -, hMb, hMc, -, -⟩ := gsUnbalancingTriple_iff.mp hUM
  have hab : a * b = b * a :=
    (mem_centralizer_singleton_iff.mp (mem_inf.mp (hSH hbS)).1).symm
  exact h.false_of_fusion hSH hSsyl hES hbSK hbE
    (fun q hqSK hq hqS => h.eq_of_diagonal_target_of_footeUnbalanced hTB hSA hS hB hH hFU hHSF hCI hSol hnonab hK hz
      hU hmax hSH hSsyl hES hb hbSK hMb hMc hMa hTM hq hqSK (hqS b hbS).symm
      fun e he => hqS e (hES he))
    (fun z hzSJ hz2 hzS => h.diagonal_fusion hTB hSA hnonab hK hz hU hb hbK hab hUM hMa hTM h7
      (mem_inf.mp hzSJ).2 hz2 (hzS b hbS).symm)

theorem corollaryCStatement_of_steps_of_footeUnbalanced
    (hTB : GSLit.ThompsonBurgoyneInput) (hSA : SolAltLit.SolomonAlternatingOddInput)
    (hS : SchreierFor Blueprint.Catalog) (hTBI : TheoremBIsoInput) (hH : GSLit.HarrisInput)
    (hFU : FooteLit.FooteMaximalUnbalancedInput) (hHSF : GSLit.HarrisSolomonFritzInput)
    (hCI : GSLit.ClassicalInvolutionInput) (hSol : GrSLit.SolomonCommutingCoreInput)
    (hN1 : CorCHeldTargetStep) (hN2 : CorCDiagonalStep) : CorollaryCStatement := by
  intro X _ _ _ hnonab hK hz hU a₀ J₀ ha₀ hJa₀ hJ₀ h7 E₀ hE₀ hE4 hcomm
  exfalso
  have hB := theoremBReachInput_of_iso hS hTBI
  have h₀ : CorC.Config a₀ J₀ E₀ := ⟨ha₀, hJa₀, hJ₀, h7, hE₀, hE4, hcomm⟩
  obtain ⟨a, J, E, h, hmax⟩ := CorC.exists_lexMax_config ⟨a₀, J₀, E₀, h₀⟩
  obtain ⟨e₀, he₀E, he₀1, -⟩ := h.exists_involution
  have hM := h.gsMaximalUnbalancingTriple_of_steps_of_footeUnbalanced hTB hSA hS hB hH hFU hHSF hCI hSol hN1 hN2
    hnonab hK hz hU hmax he₀E he₀1
  have hI := h.isoInput_of_steps_of_footeUnbalanced hTB hSA hS hB hH hFU hHSF hCI hSol hN1 hN2 hnonab hK hz hU hmax
  rcases hTBI X hnonab hK hz hU a e₀ J hM hI (Or.inl h.equiv) with
    ⟨⟨p, f, -, hp2, -, hL⟩, -⟩ | ⟨hB2a, hB2b⟩
  · obtain ⟨e7⟩ := h.equiv
    have hc := GSThmB.card_of_lieModel_psl_two hp2 hL
    rw [Nat.card_congr e7.toEquiv, GSThmB.card_alternatingGroup_seven] at hc
    exact GSThmB.ordA_one_ne_2520 _ hc.symm
  · have hE2 : IsPGroup 2 E := IsPGroup.of_card (n := 2) (by rw [h.card_eq]; norm_num)
    obtain ⟨S, hSH, hSsyl, -⟩ := UGSChain.exists_sylow_two_le h.le_H hE2
    have hset : GSLit.B2Setting a J S :=
      ⟨h.orderOf_eq, h.le_centralizer, h.isPComponent, hSH, hSsyl, hB2a,
        fun b K hb hbH hbJ hK hbS hbc => hB2b b K hb hbH hbJ hK S hSH hSsyl hbS hbc⟩
    exact GSFM.false_of_footeMaximal_small_of_footeUnbalanced hH hFU hHSF hCI hnonab hK hz hU h.orderOf_eq
      h.le_centralizer h.isPComponent hset.gsMaximalComponent hM.1
      (GSFM.footeMaximal_of_b2Setting hset) (Or.inl h.equiv)

theorem corollaryCStatement_of_footeUnbalanced
    (hTB : GSLit.ThompsonBurgoyneInput) (hSA : SolAltLit.SolomonAlternatingOddInput)
    (hS : SchreierFor Blueprint.Catalog) (hTBI : TheoremBIsoInput) (hH : GSLit.HarrisInput)
    (hFU : FooteLit.FooteMaximalUnbalancedInput) (hHSF : GSLit.HarrisSolomonFritzInput)
    (hCI : GSLit.ClassicalInvolutionInput) (hSol : GrSLit.SolomonCommutingCoreInput) :
    CorollaryCStatement :=
  have hB := theoremBReachInput_of_iso hS hTBI
  corollaryCStatement_of_steps_of_footeUnbalanced hTB hSA hS hTBI hH hFU hHSF hCI hSol
    (corCHeldTargetStep_holds_of_footeUnbalanced hTB hSA hS hB hH hFU hHSF hCI hSol)
    (corCDiagonalStep_holds_of_footeUnbalanced hTB hSA hS hB hH hFU hHSF hCI hSol)

end CFSG.ComponentClassification.GSThmB
