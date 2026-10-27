module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalORigidStated
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalORigidCen5
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalORigidPlusFacts
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalORigidReindex
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalORigidSetup
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalOPlusRigidM123
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofOPlusEightSim
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofOKlein
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofRigidDefs

public section

namespace CFSG.ComponentClassification.RankTwoClassical

open Matrix Subgroup CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.Spin
open CFSG.ComponentClassification.RankTwoStandard
open scoped MatrixGroups

theorem rigidLeviChoice_orthPlus : RigidLeviChoiceFor .orthPlus := by
  intro G _ _ A D hD hA hZ hq p hp
  cases D with
  | orthPlus n m hn hm K hK e =>
    have hm2 : 2 ≤ m := by
      have hq' : 2 ^ 2 ≤ 2 ^ m := hq
      exact (Nat.pow_le_pow_iff_right (by norm_num)).mp hq'
    have : CharP K 2 := charP_two_of_card hK
    have h4 := four_le_card hK hm2
    have hSL : commutator SL(2, K) = ⊤ :=
      (CFSG.LinearGroups.special_linear_dimension_two_perfect
        (exists_finset_four h4)).commutator_eq_top
    obtain ⟨t, ht0, ht1⟩ := exists_ne_zero_ne_one h4
    have hp' : IsSingularRankTwo e (StatedQuadPlus n K) p := hp
    obtain ⟨hpo, M, ⟨hpA', hMH, he⟩, hM2, hr, hsing⟩ := hp'
    have hp2 : p ^ 2 = 1 := by rw [← hpo, pow_orderOf_eq_one]
    obtain ⟨hS, hconj, hcen⟩ := ORigid.orthPlus_m123 h4 hn hMH hM2 hr hsing
    rcases (show n = 2 + 2 ∨ 5 ≤ n by omega) with rfl | h5
    ·
      obtain ⟨θ, hker, hθ, hα, hpA, hθp⟩ := ORigid.exists_oLeviTheta_top_spec (oe := plusOe 2)
        (coe_quadPlus _ K) (coe_quadPlus _ K) (nondegenerate_polarBilin_quadPlus _ K)
        (statedQuadPlus_plusOe 2) hSL e hp
      have hinj := oProj_injective_plus (K := K) (k := 2 + 2) (by omega)
      have hcomm := commutant_statedOmega_quadPlus (K := K) (by omega) (k := 2) le_rfl
      have hw₀ : StatedQuadPlus 2 K (plusVec (by omega)) ≠ 0 := by
        rw [statedQuadPlus_plusVec]
        exact one_ne_zero
      have hperf := commutator_statedOmega_quadPlus_two (K := K) h4
      have hsemi := fun β hW hL => omegaPlusEightThreeA1Similarity K h4 hSL β hW hL
      have hchoice := leviChoice_orth_four_of (D := .orthPlus (2 + 2) m hn hm K hK e) hm2 hK hA.1
        hZ hker hθ hinj hcomm
        (statedQuadPlus_smul 2) hw₀ ht0 ht1 hperf hsemi rfl rfl hα (Or.inr (Or.inr ⟨rfl,
          statedClassicalModel_oLeviW₂ hm2 hK hker hθ hinj⟩)) (fun h => h) fun hL4 => ?sym
      case sym =>
        have hK4 : Nat.card K = 4 := by
          have h' : 2 + 2 = 4 ∧ m = 2 := hL4
          rw [hK, h'.2]
          norm_num
        obtain ⟨ω, hω0, -, hω⟩ := exists_cube_root_of_card_four hK4
        obtain ⟨s₀, hs₀⟩ := exists_swap_mem_plus (K := K)
        exact sym_oEight hA.1 hker hθ hZ hm2 hK hinj hcomm (statedQuadPlus_smul 2) hw₀ ht0 ht1
          hperf hsemi hω hω0 swapOneGL_mul_self quadPlus_two_swapOneMat hs₀
      refine ⟨_, _, hchoice, ?_⟩
      exact leviRigid_of_model e hZ hpA' hp2 hMH he hM2 hS hconj hcen
        (hchoice.Y_le.trans inf_le_right)
        (ORigid.rigidCore_orth_four_stated (coe_quadPlus _ K) (coe_quadPlus _ K)
          (statedQuadPlus_plusOe 2) hSL hperf (nondegenerate_polarBilin_quadPlus _ K)
          (fun w hw => ORigid.eq_zero_of_forall_statedOmega_quadPlus_two h4 hw)
          (ORigid.noNormalTwo_statedOmega_quadPlus_two h4) (ORigid.noNormalTwo_top_sl_two h4)
          h4 hcomm (statedQuadPlus_smul 2) hw₀ ht0 ht1 hinj hθ hker hZ hpA hp2 hθp)
    ·
      obtain ⟨k', rfl⟩ : ∃ k', n = k' + 2 + 2 := ⟨n - 4, by omega⟩
      obtain ⟨θ, hker, hθ, hα, hpA, hθp⟩ := ORigid.exists_oLeviTheta_nested_spec
        (oe := plusOe (k' + 2)) (oe' := plusOe k') (coe_quadPlus _ K) (coe_quadPlus _ K)
        (coe_quadPlus _ K) (nondegenerate_polarBilin_quadPlus _ K)
        (statedQuadPlus_plusOe (k' + 2)) (statedQuadPlus_plusOe k') hSL e hp
      have hk : 3 ≤ k' + 2 := by omega
      have hinj := oProj_injective_plus (K := K) (k := k' + 2 + 2) (by omega)
      have hperf : commutator (StatedOmega (StatedQuadPlus (k' + 2) K)) = ⊤ :=
        (isPerfect_statedOmega_quadPlus hk).commutator_eq_top
      have hcomm := commutant_statedOmega_quadPlus (K := K) (by omega) (k := k' + 2) (by omega)
      have hw₀ : StatedQuadPlus (k' + 2) K (plusVec (by omega)) ≠ 0 := by
        rw [statedQuadPlus_plusVec]
        exact one_ne_zero
      have hchoice := leviChoice_orth_of (hSL := hSL) (D := .orthPlus (k' + 2 + 2) m hn hm K hK e)
        hm2 hK hA.1 hZ hker hθ hinj ht0 ht1 hperf
        (isQuasisimple_statedOmega_quadPlus hk) (odd_card_center_statedOmega_quadPlus hk) rfl rfl
        hα ?type ?noInv (fun h => h) (fun h => by have := h.1; omega)
      case type =>
        rcases (show k' = 1 ∨ 2 ≤ k' by omega) with rfl | hk'
        · exact Or.inr (Or.inl ⟨rfl, statedClassicalModel_psl_four hm hK h4
            (oLeviLQuotEquiv hker hθ hinj hperf)⟩)
        · exact Or.inl ⟨by omega, ⟨Nat.prime_two, hm, by omega⟩, K, inferInstance, inferInstance,
            hK, ⟨(oLeviLQuotEquiv hker hθ hinj hperf).trans
              (QuotientGroup.quotientMulEquivOfEq (center_statedOmega_quadPlus hk))⟩⟩
      case noInv =>
        intro β _ hW hW₂ hL
        obtain ⟨σ, A', μ, -, hAQ, hβ⟩ := exists_semilinear_plus (n := k' + 2 + 2) (by omega) β
        exact eq_one_of_fixes_oBars hinj (commutant_statedOmega_quadPlus (by omega) (by omega))
          (statedQuadPlus_smul _) (w₀ := plusVec (by omega))
          (by rw [statedQuadPlus_plusVec]; exact one_ne_zero) ht0 ht1 hAQ hβ hW hW₂ hL
      refine ⟨_, _, hchoice, leviRigid_of_model e hZ hpA' hp2 hMH he hM2 hS hconj hcen
        (hchoice.Y_le.trans inf_le_right) ?_⟩
      have hQP := statedQuadPlus_plusOe (K := K) k'
      have hNN := ORigid.noNormalTwo_centralizer_oBarTwo_sup_oBarOne
        (statedQuadPlus_plusOe (k' + 2)) hSL hinj ht0 ht1
        (ORigid.noNormalTwo_statedOmega_quadPlus_of_three_le hk) hcomm (statedQuadPlus_smul _) hw₀
      rw [ORigid.oBarTwo_eq_oeP (statedQuadPlus_plusOe (k' + 2)) hQP hQP hSL,
        ORigid.oBarOne_eq_oeP (statedQuadPlus_plusOe (k' + 2)) hQP hQP hSL] at hNN ⊢
      rw [ORigid.oProj_oKappa_oRhoOne_eq (statedQuadPlus_plusOe (k' + 2)) hQP hQP hSL] at hθp
      exact ORigid.rigidCore_orth_five_stated (coe_quadPlus _ K) (coe_quadPlus _ K)
        (ORigid.quad_oeP (statedQuadPlus_plusOe (k' + 2)) hQP hQP) hSL (coe_quadPlus _ K) hQP
        hperf (nondegenerate_polarBilin_quadPlus _ K)
        (fun w hw => ORigid.eq_zero_of_forall_statedOmega_quadPlus_mulVec_eq (by omega)
          (by omega) hw)
        (ORigid.noNormalTwo_statedOmega_quadPlus_of_three_le hk)
        (ORigid.noNormalTwo_top_sl_two h4) (ORigid.isSimpleGroup_sl_two h4)
        (ORigid.isSimpleGroup_statedOmega_quadPlus_of_three_le hk)
        (ORigid.card_statedOmega_ne_card_sl (plusOe k') hQP hSL) ht0 ht1 hinj hNN hθ hker hZ hpA
        hp2 hθp
  | linear => simp [ClassicalModel.family] at hD
  | unitary => simp [ClassicalModel.family] at hD
  | symplectic => simp [ClassicalModel.family] at hD
  | orthMinus => simp [ClassicalModel.family] at hD

end CFSG.ComponentClassification.RankTwoClassical
