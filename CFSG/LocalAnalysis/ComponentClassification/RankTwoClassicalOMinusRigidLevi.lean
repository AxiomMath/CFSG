module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalORigidSetup
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofOMinusLevi
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofOAut
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofOEightChoice

public section

namespace CFSG.ComponentClassification.RankTwoClassical.ORigid

open Matrix Subgroup CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.Spin
open CFSG.ComponentClassification.RankTwoStandard
open scoped MatrixGroups

theorem exists_leviChoice_orthMinus_four_spec {G : Type} [Group G] [Finite G] {A : Subgroup G}
    {m : ℕ} (hn : 4 ≤ 1 + 3) (hm : 1 ≤ m) {K : Type} [Field K] [Finite K] [CharP K 2]
    (hK : Nat.card K = 2 ^ m) (b c : K) (hbc : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (e : rankTwoQuot A ≃* StatedProj (StatedOmega (StatedQuadMinus (1 + 3) K b c)))
    (hA : CFSG.Open.IsQuasisimple ↥A) (hZ : Odd (Nat.card (center ↥A))) (hm2 : 2 ≤ m)
    (hSL : commutator SL(2, K) = ⊤) {p : G}
    (hp : IsSingularRankTwo e (StatedQuadMinus (1 + 3) K b c) p) :
    ∃ θ : ↥A →* StatedProj (StatedOmega (StatedQuadMinus (1 + 3) K b c)),
      θ.ker = center ↥A ∧ Function.Surjective θ ∧
      (∃ hpA : p ∈ A, θ ⟨p, hpA⟩ = oProj (StatedQuadMinus (1 + 3) K b c)
        (oRhoOne (minusOe 1) (statedQuadMinus_minusOe 1 b c) hSL (slTr 1))) ∧
      LeviChoice (ClassicalModel.orthMinus (1 + 3) m hn hm K hK b c hbc e) p
        (levLift θ (oBarTwo (minusOe 1) (statedQuadMinus_minusOe 1 b c) hSL))
        (levLift θ (oBarTwo (minusOe 1) (statedQuadMinus_minusOe 1 b c) hSL) ⊔
          levLift θ (oBarL (minusOe 1) (statedQuadMinus_minusOe 1 b c))) := by
  have h4 := four_le_card hK hm2
  obtain ⟨t, ht0, ht1⟩ := exists_ne_zero_ne_one h4
  obtain ⟨θ, hker, hθ, hα, hpA, hθp⟩ := exists_oLeviTheta_top_spec (oe := minusOe 1)
    (coe_quadMinus (1 + 3) K b c) (coe_quadMinus (1 + 1) K b c)
    (nondegenerate_polarBilin_quadMinus_of_finite _ K hbc) (statedQuadMinus_minusOe 1 b c) hSL e
    hp
  refine ⟨θ, hker, hθ, ⟨hpA, hθp⟩, ?_⟩
  have hinj := oProj_injective_minus (K := K) (1 + 3) b c
  have hcomm := commutant_statedOmega_quadMinus (K := K) (by omega) (n := 1 + 1) le_rfl hbc
  have hw₀ : StatedQuadMinus (1 + 1) K b c (minusVec _) ≠ 0 := by
    rw [statedQuadMinus_minusVec]
    exact one_ne_zero
  have hperf := (isSimpleGroup_statedOmega_quadMinus_small (K := K) (n := 1 + 1) (Or.inl rfl)
    hbc).2.1
  have hsemi := fun β (_ : ∀ x ∈ oBarTwo (minusOe 1) (statedQuadMinus_minusOe 1 b c) hSL, β x = x)
    (_ : ∀ x ∈ oBarL (minusOe 1) (statedQuadMinus_minusOe 1 b c), β x = x) =>
      exists_semilinear_minus (n := 1 + 3) (by omega) hbc β
  refine leviChoice_orth_four_of hm2 hK hA.1 hZ hker hθ hinj hcomm
    (statedQuadMinus_smul _ b c) hw₀ ht0 ht1 hperf hsemi rfl rfl hα (Or.inr (Or.inr ⟨rfl,
      statedClassicalModel_oLeviW₂ hm2 hK hker hθ hinj⟩)) (fun h => h) fun hL4 => ?_
  have hK4 : Nat.card K = 4 := by
    have h' : 1 + 3 = 4 ∧ m = 2 := hL4
    rw [hK, h'.2]
    norm_num
  obtain ⟨ω, hω0, -, hω⟩ := exists_cube_root_of_card_four hK4
  obtain ⟨s₀, hs₀⟩ := exists_swap_mem_minus hbc
  exact sym_oEight hA.1 hker hθ hZ hm2 hK hinj hcomm (statedQuadMinus_smul _ b c) hw₀ ht0 ht1
    hperf hsemi hω hω0 swapMinusGL_mul_self (statedQuadMinus_swapMinusMat b c) hs₀

theorem exists_leviChoice_orthMinus_of_five_le_spec {G : Type} [Group G] [Finite G]
    {A : Subgroup G} {j m : ℕ} (hn : 4 ≤ j + 2 + 3) (hm : 1 ≤ m) {K : Type} [Field K] [Finite K]
    [CharP K 2] (hK : Nat.card K = 2 ^ m) (b c : K) (hbc : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (e : rankTwoQuot A ≃* StatedProj (StatedOmega (StatedQuadMinus (j + 2 + 3) K b c)))
    (hA : CFSG.Open.IsQuasisimple ↥A) (hZ : Odd (Nat.card (center ↥A))) (hm2 : 2 ≤ m)
    (hSL : commutator SL(2, K) = ⊤) {p : G}
    (hp : IsSingularRankTwo e (StatedQuadMinus (j + 2 + 3) K b c) p) :
    ∃ θ : ↥A →* StatedProj (StatedOmega (StatedQuadMinus (j + 2 + 3) K b c)),
      θ.ker = center ↥A ∧ Function.Surjective θ ∧
      (∃ hpA : p ∈ A, θ ⟨p, hpA⟩ = oProj (StatedQuadMinus (j + 2 + 3) K b c)
        (oKappa (minusOe (j + 2)) (statedQuadMinus_minusOe (j + 2) b c)
          (oRhoOne (minusOe j) (statedQuadMinus_minusOe j b c) hSL (slTr 1)))) ∧
      LeviChoice (ClassicalModel.orthMinus (j + 2 + 3) m hn hm K hK b c hbc e) p
        (levLift θ (oBarTwo (minusOe (j + 2)) (statedQuadMinus_minusOe (j + 2) b c) hSL))
        (levLift θ (oBarTwo (minusOe (j + 2)) (statedQuadMinus_minusOe (j + 2) b c) hSL) ⊔
          levLift θ (oBarOne (minusOe (j + 2)) (statedQuadMinus_minusOe (j + 2) b c) hSL)) := by
  have h4 := four_le_card hK hm2
  obtain ⟨t, ht0, ht1⟩ := exists_ne_zero_ne_one h4
  obtain ⟨θ, hker, hθ, hα, hpA, hθp⟩ := exists_oLeviTheta_nested_spec (oe := minusOe (j + 2))
    (oe' := minusOe j) (coe_quadMinus (j + 2 + 3) K b c) (coe_quadMinus (j + 2 + 1) K b c)
    (coe_quadMinus (j + 1) K b c) (nondegenerate_polarBilin_quadMinus_of_finite _ K hbc)
    (statedQuadMinus_minusOe (j + 2) b c) (statedQuadMinus_minusOe j b c) hSL e hp
  refine ⟨θ, hker, hθ, ⟨hpA, hθp⟩, ?_⟩
  have hinj := oProj_injective_minus (K := K) (j + 2 + 3) b c
  obtain ⟨hperf, hqs, hZ₂⟩ : commutator (StatedOmega (StatedQuadMinus (j + 2 + 1) K b c)) = ⊤ ∧
      CFSG.IsQuasisimple (StatedOmega (StatedQuadMinus (j + 2 + 1) K b c)) ∧
      Odd (Nat.card (center (StatedOmega (StatedQuadMinus (j + 2 + 1) K b c)))) := by
    rcases (show j = 0 ∨ 1 ≤ j by omega) with rfl | hj
    · obtain ⟨hs, hp', hna⟩ := isSimpleGroup_statedOmega_quadMinus_small (K := K) (n := 3)
        (Or.inr rfl) hbc
      obtain ⟨hq, hc⟩ := isQuasisimple_of_isSimpleGroup hna
      exact ⟨hp', hq, by rw [hc, Subgroup.card_bot]; exact odd_one⟩
    · exact ⟨(isPerfect_statedOmega_quadMinus (by omega) hbc).commutator_eq_top,
        isQuasisimple_statedOmega_quadMinus (by omega) hbc,
        odd_card_center_statedOmega_quadMinus (by omega) hbc⟩
  refine leviChoice_orth_of (hSL := hSL) hm2 hK hA.1 hZ hker hθ hinj ht0 ht1 hperf hqs
    hZ₂ rfl rfl hα ?_ ?_ (fun h => h) (fun h => by have := h.1; omega)
  ·
    rcases (show j = 0 ∨ 1 ≤ j by omega) with rfl | hj
    · exact Or.inr (Or.inl ⟨rfl, statedClassicalModel_psu_four hm2 hK hbc
        (oLeviLQuotEquiv hker hθ hinj hperf)⟩)
    · exact Or.inl ⟨by omega, ⟨Nat.prime_two, hm, by omega⟩, K, inferInstance, inferInstance, hK,
        b, c, hbc, ⟨(oLeviLQuotEquiv hker hθ hinj hperf).trans
          (QuotientGroup.quotientMulEquivOfEq (center_statedOmega_quadMinus (by omega) hbc))⟩⟩
  ·
    intro β _ hW hW₂ hL
    obtain ⟨σ, A', μ, -, hAQ, hβ⟩ := exists_semilinear_minus (n := j + 2 + 3) (by omega) hbc β
    exact eq_one_of_fixes_oBars hinj (commutant_statedOmega_quadMinus (by omega) (by omega) hbc)
      (statedQuadMinus_smul _ b c) (w₀ := minusVec _)
      (by rw [statedQuadMinus_minusVec]; exact one_ne_zero) ht0 ht1 hAQ hβ hW hW₂ hL

end CFSG.ComponentClassification.RankTwoClassical.ORigid
