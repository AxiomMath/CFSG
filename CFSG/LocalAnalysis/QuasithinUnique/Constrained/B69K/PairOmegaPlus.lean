module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.B69K.PairModels
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.LieOver.OrthPlus
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointPlusIndexBasic
public import CFSG.Monster.B.TwoA.Census.PermClasses

public section

namespace CFSG.Quasithin

namespace B69K

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin.LieOver
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit
open QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin
open scoped Pointwise

theorem orthPlus_indep_weyl {n : ℕ} {K : Type} [Field K] (hn : 4 ≤ n)
    {W : Submodule K (Fin n ⊕ Fin n → K)} (hW : W ∈ pOmegaPlusSubspaces n K hn) :
    ∃ g : ↥(orthElementaryGroup (quadPlus n K)), g ∉ lf_stab n K W ∧
      ∀ W' ∈ pOmegaPlusSubspaces n K hn, W' ≠ W → g ∈ lf_stab n K W' := by
  have hr : 3 ≤ n := by omega
  have hmem : ∀ (k : Fin n) (V : Submodule K (Fin n ⊕ Fin n → K)),
      (⟨weylElt n K k, weylElt_mem k⟩ : ↥(orthElementaryGroup (quadPlus n K))) ∈ lf_stab n K V ↔
        weylElt n K k • V = V := fun k V =>
    ⟨fun h => MulAction.mem_stabilizer_iff.1 (Subgroup.mem_subgroupOf.1 h),
      fun h => Subgroup.mem_subgroupOf.2 (MulAction.mem_stabilizer_iff.2 h)⟩
  rcases hW with ⟨i, hi1, hi2, rfl⟩ | rfl | rfl
  · refine ⟨⟨weylElt n K ⟨i - 1, by omega⟩, weylElt_mem ⟨i - 1, by omega⟩⟩, fun h => ?_, ?_⟩
    · exact (lj_move_flag (K := K) hr hi1 hi2 ⟨i - 1, by omega⟩
        (by show i - 1 + 1 = i; omega)) ((hmem ⟨i - 1, by omega⟩ _).1 h)
    · intro W' hW' hne
      apply (hmem ⟨i - 1, by omega⟩ W').2
      rcases hW' with ⟨j, hj1, hj2, rfl⟩ | rfl | rfl
      · have hji : j ≠ i := fun h => hne (by rw [h])
        exact lj_fix_flag (K := K) hr hj1 hj2 ⟨i - 1, by omega⟩
          (by show i - 1 + 1 ≠ j; omega)
      · exact (lj_top (K := K) hr ⟨i - 1, by omega⟩ (by show i - 1 + 1 ≤ n - 2; omega)).1
      · exact (lj_top (K := K) hr ⟨i - 1, by omega⟩ (by show i - 1 + 1 ≤ n - 2; omega)).2
  · refine ⟨⟨weylElt n K ⟨n - 1, by omega⟩, weylElt_mem ⟨n - 1, by omega⟩⟩, fun h => ?_, ?_⟩
    · exact (lj_last (K := K) hr ⟨n - 1, by omega⟩ rfl).1 ((hmem ⟨n - 1, by omega⟩ _).1 h)
    · intro W' hW' hne
      apply (hmem ⟨n - 1, by omega⟩ W').2
      rcases hW' with ⟨j, hj1, hj2, rfl⟩ | rfl | rfl
      · exact lj_fix_flag (K := K) hr hj1 hj2 ⟨n - 1, by omega⟩
          (by show n - 1 + 1 ≠ j; omega)
      · exact absurd rfl hne
      · exact (lj_last (K := K) hr ⟨n - 1, by omega⟩ rfl).2
  · refine ⟨⟨weylElt n K ⟨n - 2, by omega⟩, weylElt_mem ⟨n - 2, by omega⟩⟩, fun h => ?_, ?_⟩
    · exact (lj_pen (K := K) hr ⟨n - 2, by omega⟩ rfl).1 ((hmem ⟨n - 2, by omega⟩ _).1 h)
    · intro W' hW' hne
      apply (hmem ⟨n - 2, by omega⟩ W').2
      rcases hW' with ⟨j, hj1, hj2, rfl⟩ | rfl | rfl
      · exact lj_fix_flag (K := K) hr hj1 hj2 ⟨n - 2, by omega⟩
          (by show n - 2 + 1 ≠ j; omega)
      · exact (lj_pen (K := K) hr ⟨n - 2, by omega⟩ rfl).2
      · exact absurd rfl hne

theorem lf_stab_index_eq_splitProj {n : ℕ} {K : Type} [Field K]
    (W : Submodule K (Fin n ⊕ Fin n → K)) :
    (lf_stab n K W).index = (MulAction.stabilizer (splitProj n K) W).index := by
  have h1 : lf_stab n K W = MulAction.stabilizer ↥(orthElementaryGroup (quadPlus n K)) W := by
    ext g
    exact Iff.rfl
  rw [h1, MulAction.index_stabilizer, MulAction.index_stabilizer, orbit_splitProj]

theorem lf_stab_index_lt_flag {n : ℕ} {K : Type} [Field K] [Finite K] (hn : 4 ≤ n) :
    (lf_stab n K (OrthogonalSplit.flag n K 1)).index <
      (lf_stab n K (OrthogonalSplit.flag n K 2)).index := by
  rw [lf_stab_index_eq_splitProj, lf_stab_index_eq_splitProj]
  have h1 : Module.finrank K (OrthogonalSplit.flag n K 1) = 1 :=
    OrthogonalSplit.finrank_flag (by omega)
  have h2 : Module.finrank K (OrthogonalSplit.flag n K 2) = 2 :=
    OrthogonalSplit.finrank_flag (by omega)
  exact CFSG.ComponentClassification.CatalogueBOrthogonalPointPlusIndex.split_intermediate_index_gt_point
    (by omega) (OrthogonalSplit.flag n K 2) (OrthogonalSplit.flag_singular (r := n) (K := K) 2)
    (by omega) (by omega)
    ⟨OrthogonalSplit.flag n K 1, h1, OrthogonalSplit.flag_singular (r := n) (K := K) 1⟩

theorem parabolicPair_orthPlus {n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2] (hn : 4 ≤ n) :
    ∃ U : Subgroup ↥(orthElementaryGroup (quadPlus n K)), IsSylowTwoOf U ⊤ ∧ ParabolicPair U := by
  haveI : Finite ↥(orthElementaryGroup (quadPlus n K)) := finite_orthElementaryGroup
  obtain ⟨S, hS⟩ := posUnip_isSylow (r := n) (K := K) 2 (by omega)
    (fun a ha => map_flag_top_ne_Xstar (r := n) (K := K) (by omega) ha)
  have hU : IsSylowTwoOf ((posUnip n K).subgroupOf (orthElementaryGroup (quadPlus n K))) ⊤ := by
    have h := CFSG.QuasithinUnique.B113Lie.isSylowTwoOf_top_of_sylow S
    rwa [hS] at h
  have h1mem : OrthogonalSplit.flag n K 1 ∈ pOmegaPlusSubspaces n K hn :=
    Or.inl ⟨1, le_rfl, by omega, rfl⟩
  have h2mem : OrthogonalSplit.flag n K 2 ∈ pOmegaPlusSubspaces n K hn :=
    Or.inl ⟨2, by norm_num, by omega, rfl⟩
  refine ⟨(posUnip n K).subgroupOf (orthElementaryGroup (quadPlus n K)), hU, ?_⟩
  refine parabolicPair_of_coatoms (Ps := pOmegaPlusParabolics n K hn) ?_ ?_ ?_ ?_
  · rintro P ⟨W, hW, rfl⟩
    exact ⟨(lj_coatom_holds n K hn W hW).isCoatom, lf_plus_sub_le hn hW⟩
  · intro A hA hAt
    obtain ⟨W, hW, hAW⟩ := lj_cover_holds n K hn A hA hAt
    exact ⟨lf_stab n K W, Set.mem_image_of_mem _ hW, hAW⟩
  · rintro P ⟨W, hW, rfl⟩
    obtain ⟨g, hgW, hg⟩ := orthPlus_indep_weyl hn hW
    refine ⟨g, hgW, ?_⟩
    rintro P' ⟨W', hW', rfl⟩ hne
    exact hg W' hW' (fun h => hne (by rw [h]))
  · exact ⟨lf_stab n K (OrthogonalSplit.flag n K 1), Set.mem_image_of_mem _ h1mem,
      lf_stab n K (OrthogonalSplit.flag n K 2), Set.mem_image_of_mem _ h2mem,
      ne_of_lt (lf_stab_index_lt_flag hn)⟩

theorem pairData_of_statedPOmegaPlus {C : Type} [Group C] {n f : ℕ} (hn : 4 ≤ n)
    (hmc : StatedClassicalModel C .POmegaPlus n 2 f) :
    ∃ U : Subgroup C, IsSylowTwoOf U ⊤ ∧ ParabolicPair U := by
  have hmod : CFSG.Blueprint.LieModel C .POmegaPlus n 2 f :=
    Or.inl ⟨by simp [classicalTags], hmc⟩
  obtain ⟨K, hK, hfin, hCh, -, -, ⟨e⟩⟩ := exists_mulEquiv_elementaryGroup_of_lieModel hmod
  exact pairData_of_mulEquiv e (parabolicPair_orthPlus (K := K) hn)

end B69K

end CFSG.Quasithin
