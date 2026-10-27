module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointPlusIndexBasic
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointPlusBorelSplit

public section

namespace CFSG.ComponentClassification.CatalogueBOrthogonalPointPlusIndex

open CFSG.Assembly.LowTwoRank CFSG.ClassicalGroups.Orthogonal
open CFSG.LieType.Universal.Spin
open CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit
open CatalogueBOrthogonalPointAction CatalogueBOrthogonalPointPlusBorel

variable {K : Type} [Field K] {n : ℕ}

theorem stated_subspace_stabilizer_map_split (hn : 3 ≤ n)
    (W : Submodule K (Fin n ⊕ Fin n → K)) :
    (statedProjectiveSubspaceStabilizer (StatedQuadPlus n K) W).map
        (plusProjectiveEquiv n K hn).toMonoidHom =
      MulAction.stabilizer (splitProj n K) W := by
  ext x
  constructor
  · rintro ⟨g, hg, rfl⟩
    change splitProjAction n K (plusProjectiveEquiv n K hn g) W = W
    rw [← plusProjectiveSubspaceAction n K hn g]
    exact hg
  · intro hx
    refine ⟨(plusProjectiveEquiv n K hn).symm x, ?_,
      (plusProjectiveEquiv n K hn).apply_symm_apply x⟩
    change statedProjectiveSubspaceAction (StatedQuadPlus n K)
      ((plusProjectiveEquiv n K hn).symm x) W = W
    rw [plusProjectiveSubspaceAction n K hn, MulEquiv.apply_symm_apply]
    exact hx

theorem stated_subspace_stabilizer_index (hn : 3 ≤ n) (W : Submodule K (Fin n ⊕ Fin n → K)) :
    (statedProjectiveSubspaceStabilizer (StatedQuadPlus n K) W).index =
      (MulAction.stabilizer (splitProj n K) W).index :=
  (Subgroup.index_map_equiv _ (plusProjectiveEquiv n K hn)).symm.trans
    (congrArg Subgroup.index (stated_subspace_stabilizer_map_split hn W))

@[expose] def pointOfLine (L : Submodule K (Fin n ⊕ Fin n → K)) (hL : Module.finrank K L = 1)
    (hsing : ∀ v ∈ L, StatedQuadPlus n K v = 0) : Points (quadPlus n K) :=
  ⟨L, hL, fun v hv => by rw [coe_quadPlus]; exact hsing v hv⟩

variable [Finite K]

theorem stated_line_stabilizer_index (hn : 3 ≤ n) (L : Submodule K (Fin n ⊕ Fin n → K))
    (hL : Module.finrank K L = 1) (hsing : ∀ v ∈ L, StatedQuadPlus n K v = 0) :
    (statedProjectiveSubspaceStabilizer (StatedQuadPlus n K) L).index =
      pointIndex (Nat.card K) n := by
  rw [stated_subspace_stabilizer_index hn]
  exact split_point_stabilizer_index hn (pointOfLine L hL hsing)

theorem stated_high_rank_index_gt_line (hn : 5 ≤ n) (L W : Submodule K (Fin n ⊕ Fin n → K))
    (hL : Module.finrank K L = 1) (hsingL : ∀ v ∈ L, StatedQuadPlus n K v = 0)
    (hW : ∀ v ∈ W, StatedQuadPlus n K v = 0) (hW2 : 2 ≤ Module.finrank K W) :
    (statedProjectiveSubspaceStabilizer (StatedQuadPlus n K) L).index <
      (statedProjectiveSubspaceStabilizer (StatedQuadPlus n K) W).index := by
  rw [stated_subspace_stabilizer_index (by omega), stated_subspace_stabilizer_index (by omega)]
  exact split_high_rank_index_gt_point hn W (fun v hv => by rw [coe_quadPlus]; exact hW v hv)
    hW2 (pointOfLine L hL hsingL)

theorem stated_four_maximal_index_eq_line (L W : Submodule K (Fin 4 ⊕ Fin 4 → K))
    (hL : Module.finrank K L = 1) (hsingL : ∀ v ∈ L, StatedQuadPlus 4 K v = 0)
    (hW : ∀ v ∈ W, StatedQuadPlus 4 K v = 0) (hW4 : Module.finrank K W = 4) :
    (statedProjectiveSubspaceStabilizer (StatedQuadPlus 4 K) W).index =
      (statedProjectiveSubspaceStabilizer (StatedQuadPlus 4 K) L).index := by
  rw [stated_subspace_stabilizer_index (by omega), stated_subspace_stabilizer_index (by omega)]
  exact split_four_maximal_index_eq_point W (fun v hv => by rw [coe_quadPlus]; exact hW v hv)
    hW4 (pointOfLine L hL hsingL)

theorem stated_four_intermediate_index_gt_line (L W : Submodule K (Fin 4 ⊕ Fin 4 → K))
    (hL : Module.finrank K L = 1) (hsingL : ∀ v ∈ L, StatedQuadPlus 4 K v = 0)
    (hW : ∀ v ∈ W, StatedQuadPlus 4 K v = 0)
    (hW23 : Module.finrank K W = 2 ∨ Module.finrank K W = 3) :
    (statedProjectiveSubspaceStabilizer (StatedQuadPlus 4 K) L).index <
      (statedProjectiveSubspaceStabilizer (StatedQuadPlus 4 K) W).index := by
  rw [stated_subspace_stabilizer_index (by omega), stated_subspace_stabilizer_index (by omega)]
  exact split_four_intermediate_index_gt_point W
    (fun v hv => by rw [coe_quadPlus]; exact hW v hv) hW23 (pointOfLine L hL hsingL)

theorem orthogonal_geometry_plus_model_geometric_index_comparison {G : Type} [Group G]
    {p f : ℕ} (h : StatedClassicalModel G .POmegaPlus n p f) (hK : Nat.card K = p ^ f) :
    (∀ L : Submodule K (Fin n ⊕ Fin n → K), Module.finrank K L = 1 →
      (∀ v ∈ L, StatedQuadPlus n K v = 0) →
        (statedProjectiveSubspaceStabilizer (StatedQuadPlus n K) L).index =
          ((p ^ f) ^ n - 1) * ((p ^ f) ^ (n - 1) + 1) / (p ^ f - 1)) ∧
    (5 ≤ n → ∀ L W : Submodule K (Fin n ⊕ Fin n → K), Module.finrank K L = 1 →
      (∀ v ∈ L, StatedQuadPlus n K v = 0) → (∀ v ∈ W, StatedQuadPlus n K v = 0) →
        2 ≤ Module.finrank K W →
        (statedProjectiveSubspaceStabilizer (StatedQuadPlus n K) L).index <
          (statedProjectiveSubspaceStabilizer (StatedQuadPlus n K) W).index) ∧
    (n = 4 → ∀ L W : Submodule K (Fin n ⊕ Fin n → K), Module.finrank K L = 1 →
      (∀ v ∈ L, StatedQuadPlus n K v = 0) → (∀ v ∈ W, StatedQuadPlus n K v = 0) →
        (Module.finrank K W = 4 →
          (statedProjectiveSubspaceStabilizer (StatedQuadPlus n K) W).index =
            (statedProjectiveSubspaceStabilizer (StatedQuadPlus n K) L).index) ∧
        (Module.finrank K W = 2 ∨ Module.finrank K W = 3 →
          (statedProjectiveSubspaceStabilizer (StatedQuadPlus n K) L).index <
            (statedProjectiveSubspaceStabilizer (StatedQuadPlus n K) W).index)) := by
  have hn : 4 ≤ n := h.1.2.2
  refine ⟨fun L hL hsing => ?_, fun h5 L W hL hsingL hW hW2 =>
    stated_high_rank_index_gt_line h5 L W hL hsingL hW hW2, fun h4 => ?_⟩
  · rw [stated_line_stabilizer_index (by omega) L hL hsing, hK]
    rfl
  · subst h4
    exact fun L W hL hsingL hW =>
      ⟨fun hW4 => stated_four_maximal_index_eq_line L W hL hsingL hW hW4,
        fun hW23 => stated_four_intermediate_index_gt_line L W hL hsingL hW hW23⟩

end CFSG.ComponentClassification.CatalogueBOrthogonalPointPlusIndex
