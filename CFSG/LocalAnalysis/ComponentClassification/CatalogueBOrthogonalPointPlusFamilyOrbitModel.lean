module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointPlusIndexPoints
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointPlusFamilyOrbitReduction
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointDataModelIntrinsic
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointReindexCovarianceTransport
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointPlusBorelMaximal
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointPlusBorelSylow
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointPlusFamilyOrbitTransport

public noncomputable section

namespace CFSG.ComponentClassification.CatalogueBOrthogonalPointPlusFamilyOrbit

open CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.Spin
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit
open CatalogueBOrthogonalSmallFamilyOrbit CatalogueBOrthogonalPointPlusBorel
open CatalogueBOrthogonalPointPlusIndex CatalogueBOrthogonalPointAction
open CatalogueBOrthogonalPointReindexCovariance CatalogueBStabilizerFamily
open scoped Pointwise

variable {n : ℕ} {K : Type} [Field K]

theorem statedPointStabilizer_eq_subspaceStabilizer (L : Points (quadPlus n K)) :
    statedPointStabilizer (coe_quadPlus n K) L =
      statedProjectiveSubspaceStabilizer (StatedQuadPlus n K) L.val := by
  ext g
  obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective _ g
  rw [mem_statedPointStabilizer_iff]
  change _ ↔ statedProjectiveSubspaceAction (StatedQuadPlus n K) (QuotientGroup.mk' _ a) L.val =
    L.val
  rw [statedProjectiveSubspaceAction_mk_apply, ← statedPointAction_mk_submodule (coe_quadPlus n K)
    a L]
  exact Subtype.ext_iff

@[expose] def firstPoint (hn : 1 ≤ n) : Points (quadPlus n K) :=
  ⟨flag n K 1, finrank_flag_of_le hn, flag_singular 1⟩

@[expose] def firstPointStabilizer : Subgroup (StatedProj (StatedOmega (StatedQuadPlus n K))) :=
  statedProjectiveSubspaceStabilizer (StatedQuadPlus n K) (flag n K 1)

theorem firstPointStabilizer_eq (hn : 1 ≤ n) :
    firstPointStabilizer (n := n) (K := K) =
      statedPointStabilizer (coe_quadPlus n K) (firstPoint hn) :=
  (statedPointStabilizer_eq_subspaceStabilizer (firstPoint hn)).symm

theorem stated_intrinsic (hn : 3 ≤ n) :
    CatalogueBOrthogonalPointData.IntrinsicPointAction (quadPlus n K)
      (statedPointAction (coe_quadPlus n K)) := by
  have hreg := CFSG.ClassicalGroups.Orthogonal.regular_quadPlus (K := K) (n := n) hn
  exact CatalogueBOrthogonalPointData.intrinsicPointAction_of_properties _ _
    (stated_action_properties (coe_quadPlus n K)
      (CFSG.ClassicalGroups.Orthogonal.commutator_orthogonalGroup_quadPlus hn) hreg.1 hreg.2)

theorem statedPointFamily_eq_conjugacyFamily (hn : 3 ≤ n) :
    statedPointFamily (coe_quadPlus n K) =
      conjugacyFamily (firstPointStabilizer (n := n) (K := K)) := by
  have h := ((stated_intrinsic (K := K) hn).2.2 (firstPoint (by omega))).1
  rw [firstPointStabilizer_eq (by omega)]
  exact h

theorem firstPointStabilizer_isCoatom (hn : 3 ≤ n) :
    IsCoatom (firstPointStabilizer (n := n) (K := K)) := by
  have h := ((stated_intrinsic (K := K) hn).2.2 (firstPoint (by omega))).2.1
  rw [firstPointStabilizer_eq (by omega)]
  exact h

theorem plusProjectiveBorel_le_firstPointStabilizer (hn : 2 ≤ n) :
    plusProjectiveBorel n K ≤ firstPointStabilizer (n := n) (K := K) :=
  iInf_le (fun i : Fin (n - 1) => statedProjectiveSubspaceStabilizer (StatedQuadPlus n K)
    (stdFlag n K i)) ⟨0, by omega⟩

theorem plusProjectiveBorel_aut_image [Finite K] (hn : 3 ≤ n)
    (alpha : MulAut (StatedProj (StatedOmega (StatedQuadPlus n K)))) :
    ∃ g : StatedProj (StatedOmega (StatedQuadPlus n K)),
      (plusProjectiveBorel n K).map alpha.toMonoidHom =
        (plusProjectiveBorel n K).map (MulAut.conj g).toMonoidHom := by
  let p := ringChar K
  have : Fact p.Prime := ⟨CharP.char_is_prime K p⟩
  obtain ⟨S, hS⟩ := plusProjectiveUnipotent_isSylow n K p hn
  have hN := plusProjectiveUnipotent_normalizer n K hn
  rw [← hS] at hN
  rw [← hN]
  exact sylow_normalizer_image_conjugate S alpha

@[expose] def chamberStabilizers (hn : 1 ≤ n) :
    Set (Subgroup (StatedProj (StatedOmega (StatedQuadPlus n K)))) :=
  {M | (∃ i : ℕ, 1 ≤ i ∧ i ≤ n - 2 ∧
      M = statedProjectiveSubspaceStabilizer (StatedQuadPlus n K) (flag n K i)) ∨
    M = statedProjectiveSubspaceStabilizer (StatedQuadPlus n K) (Xstar n K hn) ∨
    M = statedProjectiveSubspaceStabilizer (StatedQuadPlus n K) (flag n K n)}

theorem maximal_overgroup_mem_chamberStabilizers [Finite K] (hn : 3 ≤ n)
    (M : Subgroup (StatedProj (StatedOmega (StatedQuadPlus n K))))
    (hM : IsCoatom M) (hBM : plusProjectiveBorel n K ≤ M) :
    M ∈ chamberStabilizers (K := K) (n := n) (by omega) :=
  plusProjectiveMaximalBorel_overgroups n K hn M hM hBM

theorem flag_data {i : ℕ} (hi : i ≤ n) :
    Module.finrank K (flag n K i) = i ∧ ∀ v ∈ flag n K i, StatedQuadPlus n K v = 0 :=
  ⟨finrank_flag_of_le hi, fun v hv => by rw [← coe_quadPlus]; exact flag_singular i v hv⟩

theorem Xstar_data [Finite K] (hn : 3 ≤ n) :
    Module.finrank K (Xstar n K (by omega)) = n ∧
      ∀ v ∈ Xstar n K (by omega), StatedQuadPlus n K v = 0 := by
  obtain ⟨-, ⟨hdim, hsing⟩, -⟩ := orthogonal_geometry_split_maximal_family_orbits (K := K) hn
  exact ⟨hdim, fun v hv => by rw [← coe_quadPlus]; exact hsing v hv⟩

theorem chamber_index_eq_point_iff [Finite K] (hn : 5 ≤ n)
    (M : Subgroup (StatedProj (StatedOmega (StatedQuadPlus n K))))
    (hM : M ∈ chamberStabilizers (K := K) (n := n) (by omega))
    (hindex : M.index = (firstPointStabilizer (n := n) (K := K)).index) :
    M = firstPointStabilizer (n := n) (K := K) := by
  have h1 := flag_data (n := n) (K := K) (i := 1) (by omega)
  have hlt : ∀ W : Submodule K (Fin n ⊕ Fin n → K), (∀ v ∈ W, StatedQuadPlus n K v = 0) →
      2 ≤ Module.finrank K W →
      M = statedProjectiveSubspaceStabilizer (StatedQuadPlus n K) W → False := by
    intro W hW hW2 hMW
    have := stated_high_rank_index_gt_line hn (flag n K 1) W h1.1 h1.2 hW hW2
    rw [← hMW] at this
    exact absurd hindex (by rw [firstPointStabilizer]; omega)
  rcases hM with ⟨i, hi1, hi2, hMi⟩ | hMs | hMn
  · rcases Nat.lt_or_ge i 2 with hlt2 | hge2
    · have hi : i = 1 := by omega
      subst hi
      exact hMi
    · have hi := flag_data (n := n) (K := K) (i := i) (by omega)
      exact (hlt _ hi.2 (by omega) hMi).elim
  · have hs := Xstar_data (K := K) (n := n) (by omega)
    exact (hlt _ hs.2 (by omega) hMs).elim
  · have hX := flag_data (n := n) (K := K) (i := n) le_rfl
    exact (hlt _ hX.2 (by omega) hMn).elim

theorem chamber_index_eq_point_four [Finite K] (hn : n = 4)
    (M : Subgroup (StatedProj (StatedOmega (StatedQuadPlus n K))))
    (hM : M ∈ chamberStabilizers (K := K) (n := n) (by omega))
    (hindex : M.index = (firstPointStabilizer (n := n) (K := K)).index) :
    M = firstPointStabilizer (n := n) (K := K) ∨
      M = statedProjectiveSubspaceStabilizer (StatedQuadPlus n K) (flag n K n) ∨
      M = statedProjectiveSubspaceStabilizer (StatedQuadPlus n K) (Xstar n K (by omega)) := by
  subst hn
  rcases hM with ⟨i, hi1, hi2, hMi⟩ | hMs | hMn
  · rcases Nat.lt_or_ge i 2 with hlt2 | hge2
    · have hi : i = 1 := by omega
      subst hi
      exact Or.inl hMi
    · have hi : i = 2 := by omega
      subst hi
      have h1 := flag_data (n := 4) (K := K) (i := 1) (by omega)
      have h2 := flag_data (n := 4) (K := K) (i := 2) (by omega)
      have := stated_four_intermediate_index_gt_line (flag 4 K 1) (flag 4 K 2) h1.1 h1.2 h2.2
        (Or.inl h2.1)
      rw [← hMi] at this
      exact absurd hindex (by rw [firstPointStabilizer]; omega)
  · exact Or.inr (Or.inr hMs)
  · exact Or.inr (Or.inl hMn)

theorem stated_pointFamily_fixed [Finite K] (hn : 5 ≤ n)
    (alpha : MulAut (StatedProj (StatedOmega (StatedQuadPlus n K)))) :
    alpha • statedPointFamily (coe_quadPlus n K) = statedPointFamily (coe_quadPlus n K) := by
  rw [statedPointFamily_eq_conjugacyFamily (by omega)]
  exact automorphism_family_fixed_of_borel (plusProjectiveBorel n K)
    (firstPointStabilizer (n := n) (K := K))
    (plusProjectiveBorel_le_firstPointStabilizer (by omega))
    (firstPointStabilizer_isCoatom (by omega)) (plusProjectiveBorel_aut_image (by omega))
    (chamberStabilizers (K := K) (n := n) (by omega))
    (maximal_overgroup_mem_chamberStabilizers (by omega))
    (chamber_index_eq_point_iff hn) alpha

theorem stated_pointFamily_orbit_subset [Finite K] (hn : n = 4) :
    MulAction.orbit (MulAut (StatedProj (StatedOmega (StatedQuadPlus n K))))
        (statedPointFamily (coe_quadPlus n K)) ⊆
      {statedPointFamily (coe_quadPlus n K),
        conjugacyFamily (statedProjectiveSubspaceStabilizer (StatedQuadPlus n K) (flag n K n)),
        conjugacyFamily (statedProjectiveSubspaceStabilizer (StatedQuadPlus n K)
          (Xstar n K (by omega)))} := by
  rw [statedPointFamily_eq_conjugacyFamily (by omega)]
  exact familyOrbit_subset_three_of_borel (plusProjectiveBorel n K)
    (firstPointStabilizer (n := n) (K := K)) _ _
    (plusProjectiveBorel_le_firstPointStabilizer (by omega))
    (firstPointStabilizer_isCoatom (by omega)) (plusProjectiveBorel_aut_image (by omega))
    (chamberStabilizers (K := K) (n := n) (by omega))
    (maximal_overgroup_mem_chamberStabilizers (by omega))
    (chamber_index_eq_point_four hn)

@[expose] def plusCoordinateEquiv (n : ℕ) (K : Type) [Field K] :
    StatedProj (StatedOmega (StatedQuadPlus n K)) ≃*
      CatalogueBOrthogonalSemilinear.matrixProjectiveDerived
        (CatalogueBOrthogonalPointData.coordinateQuadPlus n K) :=
  statedProjectiveReindexEquiv (CatalogueBOrthogonalPointData.plusIndexEquiv n) (quadPlus n K)
    (coe_quadPlus n K)

@[expose] def plusCX (n : ℕ) (K : Type) [Field K] :
    Set (Subgroup (CatalogueBOrthogonalSemilinear.matrixProjectiveDerived
      (CatalogueBOrthogonalPointData.coordinateQuadPlus n K))) :=
  conjugacyFamily ((statedProjectiveSubspaceStabilizer (StatedQuadPlus n K) (flag n K n)).map
    (plusCoordinateEquiv n K).toMonoidHom)

@[expose] def plusCXstar (n : ℕ) (K : Type) [Field K] (hn : 0 < n) :
    Set (Subgroup (CatalogueBOrthogonalSemilinear.matrixProjectiveDerived
      (CatalogueBOrthogonalPointData.coordinateQuadPlus n K))) :=
  conjugacyFamily ((statedProjectiveSubspaceStabilizer (StatedQuadPlus n K)
    (Xstar n K hn)).map (plusCoordinateEquiv n K).toMonoidHom)

theorem plusCoordinate_pointFamily :
    familyTransport (plusCoordinateEquiv n K) (statedPointFamily (coe_quadPlus n K)) =
      CatalogueBOrthogonalPointData.projectivePointFamily
        (CatalogueBOrthogonalPointData.coordinateQuadPlus n K) :=
  statedPointFamily_reindex (CatalogueBOrthogonalPointData.plusIndexEquiv n) (quadPlus n K)
    (coe_quadPlus n K)

theorem coordinate_plus_pointFamilyAut_eq_top [Finite K] (hn : 5 ≤ n) :
    CatalogueBOrthogonalPointData.projectivePointFamilyAut
      (CatalogueBOrthogonalPointData.coordinateQuadPlus n K) = ⊤ := by
  refine eq_top_iff.mpr fun beta _ => ?_
  rw [CatalogueBOrthogonalPointData.mem_projectivePointFamilyAut_iff]
  obtain ⟨alpha, rfl⟩ := (MulAut.congr (plusCoordinateEquiv n K)).surjective beta
  have key := familyTransport_automorphism (plusCoordinateEquiv n K)
    (statedPointFamily (coe_quadPlus n K)) alpha
  rw [stated_pointFamily_fixed hn alpha, plusCoordinate_pointFamily] at key
  exact key.symm

theorem ncard_triple_le {α : Type*} (a b c : α) : ({a, b, c} : Set α).ncard ≤ 3 := by
  have h1 := Set.ncard_insert_le a ({b, c} : Set α)
  have h2 := Set.ncard_insert_le b ({c} : Set α)
  rw [Set.ncard_singleton] at h2
  omega

theorem coordinate_plus_pointFamily_orbit_subset [Finite K] (hn : n = 4) :
    MulAction.orbit (MulAut (CatalogueBOrthogonalSemilinear.matrixProjectiveDerived
        (CatalogueBOrthogonalPointData.coordinateQuadPlus n K)))
        (CatalogueBOrthogonalPointData.projectivePointFamily
          (CatalogueBOrthogonalPointData.coordinateQuadPlus n K)) ⊆
      {CatalogueBOrthogonalPointData.projectivePointFamily
          (CatalogueBOrthogonalPointData.coordinateQuadPlus n K),
        plusCX n K, plusCXstar n K (by omega)} := by
  rw [← plusCoordinate_pointFamily, ← familyTransport_orbit]
  rintro _ ⟨T, hT, rfl⟩
  rcases stated_pointFamily_orbit_subset (K := K) hn hT with rfl | rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr (Or.inl (familyTransport_conjugacy _ _))
  · exact Or.inr (Or.inr (familyTransport_conjugacy _ _))

theorem orthogonal_geometry_plus_point_family_orbit {G : Type} [Group G] {p f : ℕ}
    (h : StatedClassicalModel G .POmegaPlus n p f) [Finite K] (hK : Nat.card K = p ^ f)
    (e : G ≃* StatedProj (StatedOmega (StatedQuadPlus n K))) :
    (∀ L : Points (quadPlus n K), statedPointFamily (coe_quadPlus n K) =
      conjugacyFamily (statedPointStabilizer (coe_quadPlus n K) L)) ∧
    (5 ≤ n → ∀ alpha : MulAut (StatedProj (StatedOmega (StatedQuadPlus n K))),
      alpha • statedPointFamily (coe_quadPlus n K) = statedPointFamily (coe_quadPlus n K)) ∧
    (∀ hn4 : n = 4,
      MulAction.orbit (MulAut (StatedProj (StatedOmega (StatedQuadPlus n K))))
          (statedPointFamily (coe_quadPlus n K)) ⊆
        {statedPointFamily (coe_quadPlus n K),
          conjugacyFamily (statedProjectiveSubspaceStabilizer (StatedQuadPlus n K) (flag n K n)),
          conjugacyFamily (statedProjectiveSubspaceStabilizer (StatedQuadPlus n K)
            (Xstar n K (by omega)))} ∧
      (MulAction.orbit (MulAut (StatedProj (StatedOmega (StatedQuadPlus n K))))
          (statedPointFamily (coe_quadPlus n K))).ncard ≤ 3) ∧
    (∀ L : Points (CatalogueBOrthogonalPointData.coordinateQuadPlus n K),
      CatalogueBOrthogonalPointData.projectivePointFamily
          (CatalogueBOrthogonalPointData.coordinateQuadPlus n K) =
        conjugacyFamily (CatalogueBOrthogonalPointData.projectivePointStabilizer
          (CatalogueBOrthogonalPointData.coordinateQuadPlus n K) L)) ∧
    (5 ≤ n → CatalogueBOrthogonalPointData.projectivePointFamilyAut
      (CatalogueBOrthogonalPointData.coordinateQuadPlus n K) = ⊤) ∧
    (∀ hn4 : n = 4,
      MulAction.orbit (MulAut (CatalogueBOrthogonalSemilinear.matrixProjectiveDerived
          (CatalogueBOrthogonalPointData.coordinateQuadPlus n K)))
          (CatalogueBOrthogonalPointData.projectivePointFamily
            (CatalogueBOrthogonalPointData.coordinateQuadPlus n K)) ⊆
        {CatalogueBOrthogonalPointData.projectivePointFamily
            (CatalogueBOrthogonalPointData.coordinateQuadPlus n K),
          plusCX n K, plusCXstar n K (by omega)} ∧
      (MulAction.orbit (MulAut (CatalogueBOrthogonalSemilinear.matrixProjectiveDerived
          (CatalogueBOrthogonalPointData.coordinateQuadPlus n K)))
          (CatalogueBOrthogonalPointData.projectivePointFamily
            (CatalogueBOrthogonalPointData.coordinateQuadPlus n K))).ncard ≤ 3) := by
  have hn : 4 ≤ n := h.1.2.2
  obtain ⟨-, hc, -⟩ := CatalogueBOrthogonalPointData.coordinate_model_intrinsic_plus h K hK e
  refine ⟨fun L => ((stated_intrinsic (K := K) (by omega)).2.2 L).1,
    fun h5 alpha => stated_pointFamily_fixed h5 alpha, fun hn4 => ?_,
    fun L => (hc.2.2 L).1, fun h5 => coordinate_plus_pointFamilyAut_eq_top h5,
    fun hn4 => ?_⟩
  · have hsub := stated_pointFamily_orbit_subset (K := K) hn4
    exact ⟨hsub, (Set.ncard_le_ncard hsub (Set.toFinite _)).trans (ncard_triple_le _ _ _)⟩
  · have hsub := coordinate_plus_pointFamily_orbit_subset (K := K) hn4
    exact ⟨hsub, (Set.ncard_le_ncard hsub (Set.toFinite _)).trans (ncard_triple_le _ _ _)⟩

end CFSG.ComponentClassification.CatalogueBOrthogonalPointPlusFamilyOrbit
