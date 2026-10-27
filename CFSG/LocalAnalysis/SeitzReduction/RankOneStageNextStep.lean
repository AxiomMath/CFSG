module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneStageNext
public import CFSG.LocalAnalysis.SeitzReduction.RankOneStageSylow

public section

namespace CFSG.SeitzReduction.RankOne

open Subgroup CFSG.LocalAnalysis

variable {D : Type} [Group D] [Finite D] {R X U P : Subgroup D} {n : ℕ}

theorem smallRoot_step (h : SmallRootStage R X U P n)
    (hP : ¬ ∃ S : Sylow 2 D, (S : Subgroup D) = P) (hE : GMSHasRegularNormal U R) :
    let V := U ⊔ R
    let W := normalizer (V : Set D) ⊓ centralizer (U : Set D)
    let Y := normalizer (V : Set D) ⊓ normalizer (R : Set D)
    IsPGroup 2 W ∧ Nat.card W = 2 * 2 ^ n * 2 ^ n ∧ V ≤ W ∧
    (W.subgroupOf (normalizer (V : Set D))).Normal ∧
    normalizer (V : Set D) ≤ normalizer (U : Set D) ∧
    W ⊓ normalizer (R : Set D) = V ∧ normalizer (V : Set D) = W ⊔ Y ∧
    (∀ x ∈ W, x * x ∈ U) ∧ (∀ x ∈ W, ∀ y ∈ W, x * y * x⁻¹ * y⁻¹ ∈ U) ∧
    ∃ Up : Subgroup D, U ≤ Up ∧ Up ≤ W ∧ Up ⊓ V = U ∧ Up ⊔ R = W ∧
      Y ≤ normalizer (Up : Set D) ∧ X ⊓ normalizer (U : Set D) ≤ normalizer (Up : Set D) ∧
      (∀ r ∈ R, r ≠ 1 → ∀ x ∈ Up, x * r * x⁻¹ * r⁻¹ ∈ U) ∧
      (∀ r ∈ R, r ≠ 1 → ∀ x ∈ Up, x * r * x⁻¹ * r⁻¹ = 1 → x ∈ U) ∧
      (∀ r ∈ R, r ≠ 1 → ∀ u ∈ U, ∃ x ∈ Up, x * r * x⁻¹ * r⁻¹ = u) ∧
      SmallRootStage (stageImg U R) (stageImg U (Up ⊔ (X ⊓ normalizer (U : Set D))))
        (stageImg U Up) (stageImg U (W ⊔ P)) n ∧
      stageImg U Y ⊔ stageImg U W =
        normalizer ((stageImg U R : Subgroup (StageQuot U)) : Set _) := by
  intro V W Y
  have h3 := h.three_le_of_not_sylow hP
  obtain ⟨hW2, hWcard, hVW, hWn, hVU, hWR, hVWY, -⟩ := smallRoot_translations h h3 hE
  obtain ⟨hsq, hcomm, Up, h1, h2, h3', h4, h5, h6, hc, h7, h8⟩ := smallRoot_layer h h3 hE
  exact ⟨hW2, hWcard, hVW, hWn, hVU, hWR, hVWY, hsq, hcomm, Up, h1, h2, h3', h4, h5, h6, hc, h7,
    h8, smallRoot_next h h3 hE h1 h2 h3' h4 h5 h6 h7 h8⟩

end CFSG.SeitzReduction.RankOne
