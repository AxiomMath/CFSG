module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalOMinusRigidM123
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalOMinusRigidLevi
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalORigidStated
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalORigidCen5
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalORigidPlusFacts
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalORigidReindex
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofRigidDefs

public section

namespace CFSG.ComponentClassification.RankTwoClassical

open Matrix Subgroup CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.Spin
open CFSG.ComponentClassification.RankTwoStandard
open scoped MatrixGroups

section Cases

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {m : ℕ} {K : Type} [Field K]
  [Finite K] (hK : Nat.card K = 2 ^ m) (b c : K) (hbc : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
  (hA : CFSG.Open.IsQuasisimple ↥A) (hZ : Odd (Nat.card (center ↥A))) (hm2 : 2 ≤ m)
include hK hbc hA hZ hm2

theorem rigidLeviChoice_orthMinus_four (hn : 4 ≤ 1 + 3) (hm : 1 ≤ m)
    (e : rankTwoQuot A ≃* StatedProj (StatedOmega (StatedQuadMinus (1 + 3) K b c))) {p : G}
    (hp : IsSingularRankTwo e (StatedQuadMinus (1 + 3) K b c) p) :
    ∃ W Y : Subgroup G,
      LeviChoice (ClassicalModel.orthMinus (1 + 3) m hn hm K hK b c hbc e) p W Y ∧
        LeviRigid A p Y := by
  have : CharP K 2 := charP_two_of_card hK
  have h4 := four_le_card hK hm2
  have hSL : commutator SL(2, K) = ⊤ :=
    (CFSG.ClassicalModels.specialLinear_isPerfect_two_of_four_le_card K h4).commutator_eq_top
  obtain ⟨t, ht0, ht1⟩ := exists_ne_zero_ne_one h4
  obtain ⟨θ, hker, hθ, ⟨hpA, hθp⟩, hchoice⟩ :=
    ORigid.exists_leviChoice_orthMinus_four_spec hn hm hK b c hbc e hA hZ hm2 hSL hp
  obtain ⟨hpo, M, ⟨hpA', hMH, he⟩, hM2, hr, hsing⟩ := hp
  have hp2 : p ^ 2 = 1 := by rw [← hpo, pow_orderOf_eq_one]
  obtain ⟨hS, hconj, hcen⟩ := ORigid.orthMinus_m123 h4 hn hbc hMH hM2 hr hsing
  have hw₀ : StatedQuadMinus (1 + 1) K b c (minusVec _) ≠ 0 := by
    rw [statedQuadMinus_minusVec]
    exact one_ne_zero
  have : Nonempty (Fin (1 + 1 - 1) ⊕ Fin (1 + 1 - 1) ⊕ Fin 2) := ⟨.inr (.inr 0)⟩
  refine ⟨_, _, hchoice, leviRigid_of_model e hZ hpA' hp2 hMH he hM2 hS hconj hcen
    (hchoice.Y_le.trans inf_le_right) ?_⟩
  exact ORigid.rigidCore_orth_four_stated (coe_quadMinus (1 + 3) K b c)
    (coe_quadMinus (1 + 1) K b c) (statedQuadMinus_minusOe 1 b c) hSL
    (ORigid.commutator_statedOmega_quadMinus_eq_top (by norm_num) hbc)
    (nondegenerate_polarBilin_quadMinus_of_finite (1 + 1) K hbc)
    (fun w hw => ORigid.eq_zero_of_forall_statedOmega_quadMinus_mulVec_eq (by norm_num) hbc hw)
    (ORigid.noNormalTwo_statedOmega_quadMinus (by norm_num) hbc) (ORigid.noNormalTwo_top_sl_two h4)
    h4 (commutant_statedOmega_quadMinus (by omega) (by norm_num) hbc)
    (statedQuadMinus_smul _ b c) hw₀ ht0 ht1 (oProj_injective_minus (1 + 3) b c) hθ hker hZ hpA
    hp2 hθp

theorem rigidLeviChoice_orthMinus_of_five_le {j : ℕ} (hn : 4 ≤ j + 2 + 3) (hm : 1 ≤ m)
    (e : rankTwoQuot A ≃* StatedProj (StatedOmega (StatedQuadMinus (j + 2 + 3) K b c))) {p : G}
    (hp : IsSingularRankTwo e (StatedQuadMinus (j + 2 + 3) K b c) p) :
    ∃ W Y : Subgroup G,
      LeviChoice (ClassicalModel.orthMinus (j + 2 + 3) m hn hm K hK b c hbc e) p W Y ∧
        LeviRigid A p Y := by
  have : CharP K 2 := charP_two_of_card hK
  have h4 := four_le_card hK hm2
  have hSL : commutator SL(2, K) = ⊤ :=
    (CFSG.ClassicalModels.specialLinear_isPerfect_two_of_four_le_card K h4).commutator_eq_top
  obtain ⟨t, ht0, ht1⟩ := exists_ne_zero_ne_one h4
  obtain ⟨θ, hker, hθ, ⟨hpA, hθp⟩, hchoice⟩ :=
    ORigid.exists_leviChoice_orthMinus_of_five_le_spec hn hm hK b c hbc e hA hZ hm2 hSL hp
  obtain ⟨hpo, M, ⟨hpA', hMH, he⟩, hM2, hr, hsing⟩ := hp
  have hp2 : p ^ 2 = 1 := by rw [← hpo, pow_orderOf_eq_one]
  obtain ⟨hS, hconj, hcen⟩ := ORigid.orthMinus_m123 h4 hn hbc hMH hM2 hr hsing
  refine ⟨_, _, hchoice, leviRigid_of_model e hZ hpA' hp2 hMH he hM2 hS hconj hcen
    (hchoice.Y_le.trans inf_le_right) ?_⟩
  have hQP := statedQuadMinus_minusOe (K := K) j b c
  have hinj := oProj_injective_minus (K := K) (j + 2 + 3) b c
  have hw₀ : StatedQuadMinus (j + 2 + 1) K b c (minusVec _) ≠ 0 := by
    rw [statedQuadMinus_minusVec]
    exact one_ne_zero
  have hNN := ORigid.noNormalTwo_centralizer_oBarTwo_sup_oBarOne
    (statedQuadMinus_minusOe (j + 2) b c) hSL hinj ht0 ht1
    (ORigid.noNormalTwo_statedOmega_quadMinus (by omega) hbc)
    (commutant_statedOmega_quadMinus (by omega) (by omega) hbc) (statedQuadMinus_smul _ b c) hw₀
  rw [ORigid.oBarTwo_eq_oeP (statedQuadMinus_minusOe (j + 2) b c) hQP hQP hSL,
    ORigid.oBarOne_eq_oeP (statedQuadMinus_minusOe (j + 2) b c) hQP hQP hSL] at hNN ⊢
  rw [ORigid.oProj_oKappa_oRhoOne_eq (statedQuadMinus_minusOe (j + 2) b c) hQP hQP hSL] at hθp
  exact ORigid.rigidCore_orth_five_stated (coe_quadMinus (j + 2 + 3) K b c)
    (coe_quadMinus (j + 3) K b c) (ORigid.quad_oeP (statedQuadMinus_minusOe (j + 2) b c) hQP hQP)
    hSL (coe_quadMinus (j + 1) K b c) hQP
    (ORigid.commutator_statedOmega_quadMinus_eq_top (by omega) hbc)
    (nondegenerate_polarBilin_quadMinus_of_finite (j + 3) K hbc)
    (fun w hw => ORigid.eq_zero_of_forall_statedOmega_quadMinus_mulVec_eq (by omega) hbc hw)
    (ORigid.noNormalTwo_statedOmega_quadMinus (by omega) hbc) (ORigid.noNormalTwo_top_sl_two h4)
    (ORigid.isSimpleGroup_sl_two h4)
    (ORigid.isSimpleGroup_statedOmega_quadMinus_of_two_le (by omega) hbc)
    (ORigid.card_statedOmega_quadMinus_ne_card_sl j hSL) ht0 ht1 hinj hNN hθ hker hZ hpA hp2 hθp

end Cases

theorem rigidLeviChoice_orthMinus : RigidLeviChoiceFor .orthMinus := by
  intro G _ _ A D hD hA hZ hq p hp
  cases D with
  | orthMinus n m hn hm K hK b c hbc e =>
    have hm2 : 2 ≤ m := by
      have hq' : 2 ^ 2 ≤ 2 ^ m := hq
      exact (Nat.pow_le_pow_iff_right (by norm_num)).mp hq'
    rcases (show n = 1 + 3 ∨ 5 ≤ n by omega) with rfl | h5
    · exact rigidLeviChoice_orthMinus_four hK b c hbc hA hZ hm2 hn hm e hp
    · obtain ⟨j, rfl⟩ : ∃ j, n = j + 2 + 3 := ⟨n - 5, by omega⟩
      exact rigidLeviChoice_orthMinus_of_five_le hK b c hbc hA hZ hm2 hn hm e hp
  | linear => simp [ClassicalModel.family] at hD
  | unitary => simp [ClassicalModel.family] at hD
  | symplectic => simp [ClassicalModel.family] at hD
  | orthPlus => simp [ClassicalModel.family] at hD

end CFSG.ComponentClassification.RankTwoClassical
