module

public import CFSG.LocalAnalysis.OddStandard.Solomon75Ys04Assembly
public import CFSG.Milestones.CL_LIT_GH74_sectional_two_rank_four
import CFSG.LocalAnalysis.OddStandard.Solomon75Sec6Assembly
import CFSG.LocalAnalysis.OddStandard.Solomon75Sec6Entry
import CFSG.LocalAnalysis.OddStandard.Solomon75Sec6SE
import CFSG.LocalAnalysis.OddStandard.Solomon75Sec6PumpUp
import CFSG.LocalAnalysis.OddStandard.Solomon75Sec6TwoRank
import CFSG.LocalAnalysis.OddStandard.Solomon75Sec6Ctrl
import CFSG.LocalAnalysis.OddStandard.Solomon75Sec6CtrlN
import CFSG.LocalAnalysis.OddStandard.Solomon75Sec6Lemma61BC
import CFSG.LocalAnalysis.OddStandard.Solomon75Sec6Lambda1
import CFSG.LocalAnalysis.OddStandard.Solomon75Sec6SigOdd
import CFSG.LocalAnalysis.OddStandard.Solomon75Sec6SigKill
import CFSG.LocalAnalysis.OddStandard.Solomon75Sec6SigCenA1
import CFSG.LocalAnalysis.OddStandard.Solomon75Sec6SigCenA
import CFSG.LocalAnalysis.OddStandard.Solomon75Sec6FusIII
import CFSG.LocalAnalysis.OddStandard.Solomon75Sec6FusStep2
import CFSG.LocalAnalysis.OddStandard.Solomon75Sec6Lemma66
import CFSG.LocalAnalysis.OddStandard.Solomon75Sec6OddCentral
import CFSG.LocalAnalysis.OddStandard.Solomon75Sec6ExtCanon
import CFSG.LocalAnalysis.OddStandard.Solomon75Sec6Thm67Cen
import CFSG.LocalAnalysis.OddStandard.Solomon75Sec6Gen45
import CFSG.Timmesfeld.Bridge.SchurNarrow

public section

namespace CFSG.OddStandard.Solomon75

open Subgroup CFSG CFSG.GH74.GLS

theorem caseNotA_false :
    ∀ (X : Type) [Group X] [Finite X], SolCEx X → ¬ HypA X → False := by
  intro X _ _ hc hA
  have hAsc : Timmesfeld.Bridge.Asc73For X :=
    Timmesfeld.Bridge.asc73For_of ShultStronglyClosedTI.theoremTwo
      Timmesfeld.Bridge.schurNarrowInput X
  have hgenM : ∀ (G : Type) [Group G] [Finite G], Nonempty (G ≃* Blueprint.NativeSporadic.McL) →
      ∀ x y : G, orderOf x = 2 → orderOf y = 2 → x ≠ y → x * y = y * x →
        centralizer ({x} : Set G) ⊔ centralizer ({y} : Set G) = ⊤ :=
    fun _ _ _ ⟨e⟩ _ _ hx hy hxy hc => mcl_sup_centralizer_eq_top e hx hy hxy hc
  have hgenL : ∀ (G : Type) [Group G] [Finite G], Nonempty (G ≃* Blueprint.NativeSporadic.Ly) →
      ∀ x y : G, orderOf x = 2 → orderOf y = 2 → x ≠ y → x * y = y * x →
        centralizer ({x} : Set G) ⊔ centralizer ({y} : Set G) = ⊤ :=
    fun _ _ _ ⟨e⟩ _ _ hx hy hxy hc => ly_sup_centralizer_eq_top e hx hy hxy hc
  haveI := hc.simple
  obtain ⟨n, hn⟩ := hc.toSolMinCEx.exists_isMaxAhatDeg
  have hK := sec6Lemma51 hc hn
  have hEn := sec6Entry_of_pumpUp hA hn (sec6PumpUpHolds X n hc hn hK)
  obtain ⟨hdeg, -⟩ := hEn.exists_mcomp
  obtain ⟨t, hS⟩ := sec6Setting_exists hc hA hn hEn fun t ht =>
    sec6CentralChoiceHolds X n t hc hA hn hdeg hK ht
  have hrank := sec6TwoRankHolds X n t hS
  have hLa := sec6L61_a hS hK
  have hC := sec6CtrlHolds X n t hS hK hLa
  have h61 := sec6L61_of hS hK hLa hC
  have hU : ∀ x ∈ Sec6M X n (cen t), orderOf x = 2 → ∀ L F : Subgroup X,
      Sec6MComp X n (cen t) L → Sec6KComp X n (cen x) F → sec6Piece L x ≤ F →
        F = oddCoreOf F ⊔ sec6Piece L x :=
    fun x hx hx2 L F hL hF hLF => sec6_mpiece_unpumped hS hK hC hx hx2 hL hF hLF
  obtain ⟨hodd, hcan⟩ := sec6SigOdd_of_lambda1At hS hK (sec6Lambda1At_of_ctrl hS hK hC hU)
  have hII := sec6CtrlNHolds X n t hS hK hLa hC
  have hfus : ∀ N : Subgroup X, N ≠ ⊤ → cen t ≤ N →
      (∀ x ∈ Sec6R X n N, orderOf x = 2 → cen x ≤ N) → Sec6Fusion X N (Sec6Y X n N) :=
    fun N hN hCt hI => sec6Thm64Fusion_of_ctrl hS hK h61 hC N hN hCt (hII N hN hCt) hI
      (sec6FusMemK_of_step2 (sec6FusIII_of hK N)
        (sec6FusStep2_of hS hK h61 hC N hN hCt (hII N hN hCt) hI hgenM hgenL))
  have hV0 : sec6Sig X n t = ⊥ := by
    by_contra hne
    have hNtop := sec6_normalizer_ne_top_of_odd hodd hne hS.choice.inv
    have hCt := cen_le_normalizer_sec6Sig n t
    have hI : ∀ x ∈ Sec6R X n (normalizer (sec6Sig X n t : Set X)), orderOf x = 2 →
        cen x ≤ normalizer (sec6Sig X n t : Set X) := by
      by_cases hA1 : K0 X n (cen t) = ⊥
      · exact sec6SigCen_of_A_eq_bot hS hK hC hA1 hU (hII _ hNtop hCt) hcan
      · exact sec6SigCen_of_A_ne_bot hS hK h61 hC hA1 hU (hII _ hNtop hCt)
          (fun E hEB hE hE8 hEM => sec6_extCanon hS hK hC hcan hEB hE hE8 hEM) hne
    exact sec6_false_of_fusion hAsc hrank (hfus _ hNtop hCt hI)
  have h65 := sec6L65_of_ctrl hS hC fun b hb hb2 =>
    le_bot_iff.1 (hV0 ▸ oddCoreOf_cen_le_sec6Sig hb hb2)
  have hVst := sec6L66_V hS h61 hC hU h65
  have hOZ := sec6_oddCoreOf_K_le_centralizer hS hC hU h65
  have hNV : normalizer (sec6V X n t : Set X) ≠ ⊤ := sec6Thm67_ne_top hS hVst
  have hCtV := cen_le_normalizer_sec6V n t
  exact sec6_false_of_fusion hAsc hrank (hfus _ hNV hCtV
    (sec6Thm67Cen_ofV hS hK h61 hC h65 hVst hOZ (hII _ hNV hCtV) hgenM hgenL).2)

theorem solomon2AnInput_of_gh74Milestone
    (hGH : type_of% @CFSG.Milestones.cl_lit_gh74_sectional_two_rank_four_models) :
    ComponentClassification.GSThmB.Solomon2AnInput :=
  solomon2AnInput_of_gh74_of_caseNotA (fun G _ _ _ hnonab hrank hsect => hGH G hnonab hrank hsect)
    caseNotA_false

end CFSG.OddStandard.Solomon75
