module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotFusionOuter
public import CFSG.LocalAnalysis.SeitzReduction.FusionGenericAutU2Outer
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotFiveFamily

public section

namespace CFSG.SeitzReduction.OmegaPilot

open Subgroup
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  (matrixProjectiveDerived matrixProjectiveImage)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  (plusIndexEquiv coordinateQuadPlus projectivePointFamily)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointPlusFamilyOrbit
  (plusCX plusCXstar coordinate_plus_pointFamily_orbit_subset)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointReindexCovariance
  (statedProjectiveReindexEquiv)
open scoped Pointwise

section Index

variable {K : Type} [Field K] [Finite K] [CharP K 2]

omit [CharP K 2] in
theorem orbit_pointFamily_ncard_four :
    (MulAction.orbit (MulAut (matrixProjectiveDerived (coordinateQuadPlus 4 K)))
        (projectivePointFamily (coordinateQuadPlus 4 K))).ncard = 1 ∨
      (MulAction.orbit (MulAut (matrixProjectiveDerived (coordinateQuadPlus 4 K)))
        (projectivePointFamily (coordinateQuadPlus 4 K))).ncard = 3 := by
  classical
  set F := projectivePointFamily (coordinateQuadPlus 4 K) with hF
  set A := plusCX 4 K with hA
  set B := plusCXstar 4 K (by norm_num) with hB
  set O := MulAction.orbit (MulAut (matrixProjectiveDerived (coordinateQuadPlus 4 K))) F with hO
  have hsub : O ⊆ {F, A, B} := coordinate_plus_pointFamily_orbit_subset (n := 4) (K := K) rfl
  set γ := plusFlipAut 4 K (by norm_num) with hγ
  have hγF : γ • F = F := plusFlipAut_smul_pointFamily 4 K _
  have hγA : γ • A = B := plusFlipAut_smul_plusCX 4 K _
  have hγB : γ • B = A := plusFlipAut_smul_plusCXstar 4 K _
  have hAB : A ≠ B := plusCX_ne_plusCXstar 4 K (by norm_num)
  have hFA : F ≠ A := fun h => hAB (by rw [← hγA, ← h, hγF])
  have hFB : F ≠ B := fun h => hAB (by rw [← hγB, ← h, hγF])
  have hFO : F ∈ O := MulAction.mem_orbit_self F
  have hclosed : ∀ S ∈ O, γ • S ∈ O := by
    rintro S ⟨α, rfl⟩
    exact ⟨γ * α, mul_smul γ α F⟩
  by_cases hAO : A ∈ O
  · right
    have hBO : B ∈ O := hγA ▸ hclosed A hAO
    have hOeq : O = {F, A, B} := le_antisymm hsub (by
      intro S hS
      rcases hS with rfl | rfl | rfl
      · exact hFO
      · exact hAO
      · exact hBO)
    rw [hOeq, Set.ncard_insert_of_notMem (by simp [hFA, hFB]),
      Set.ncard_pair hAB]
  · by_cases hBO : B ∈ O
    · exact absurd (hγB ▸ hclosed B hBO) hAO
    · left
      have hOeq : O = {F} := by
        refine le_antisymm (fun S hS => ?_) (by simpa using hFO)
        rcases hsub hS with h | h | h
        · exact h
        · exact absurd (h ▸ hS) hAO
        · exact absurd (h ▸ hS) hBO
      rw [hOeq, Set.ncard_singleton]

theorem ordProj_two_index_matrixProjectiveImage_four :
    ordProj[2] (matrixProjectiveImage (coordinateQuadPlus 4 K)).index = 1 := by
  have hstab : matrixProjectiveImage (coordinateQuadPlus 4 K) =
      MulAction.stabilizer (MulAut (matrixProjectiveDerived (coordinateQuadPlus 4 K)))
        (projectivePointFamily (coordinateQuadPlus 4 K)) := by
    ext δ
    rw [mem_image_iff_smul_pointFamily le_rfl, MulAction.mem_stabilizer_iff]
  rw [hstab, MulAction.index_stabilizer]
  rcases orbit_pointFamily_ncard_four (K := K) with h | h <;> rw [h]
  · exact CFSG.LocalAnalysis.ComponentInitial.ordProj_two_eq_one_of_odd odd_one
  · exact CFSG.LocalAnalysis.ComponentInitial.ordProj_two_eq_one_of_odd (by decide)

theorem ordProj_two_card_outer_le_two_plus_four {X : Type} [Group X] {f : ℕ} (hf : Odd f)
    (hK : Nat.card K = 2 ^ f) (e : X ≃* matrixProjectiveDerived (coordinateQuadPlus 4 K)) :
    ordProj[2] (Nat.card (Outer X)) ≤ 2 := by
  have hst : CFSG.Assembly.LowTwoRank.StatedClassicalModel X .POmegaPlus 4 2 f :=
    ⟨⟨Nat.prime_two, hf.pos, le_rfl⟩, K, inferInstance, inferInstance, hK,
      ⟨e.trans (statedProjectiveReindexEquiv (plusIndexEquiv 4)
        (CFSG.LieType.Universal.Spin.quadPlus 4 K)
        (CFSG.LieType.Universal.Spin.coe_quadPlus 4 K)).symm⟩⟩
  have hab := CFSG.LocalAnalysis.ComponentInitial.orthogonal_model_isometry_abelianization_order_bound
    X .POmegaPlus (.inr (.inl rfl)) 4 2 f hst K hK (CFSG.LieType.Universal.Spin.quadPlus 4 K)
    (CFSG.LieType.Universal.Spin.coe_quadPlus 4 K)
    (e.trans (statedProjectiveReindexEquiv (plusIndexEquiv 4)
        (CFSG.LieType.Universal.Spin.quadPlus 4 K)
        (CFSG.LieType.Universal.Spin.coe_quadPlus 4 K)).symm)
  have hQ := (CFSG.ComponentClassification.CatalogueBOrthogonalPointData.coordinate_model_intrinsic_plus
    hst K hK (e.trans (statedProjectiveReindexEquiv (plusIndexEquiv 4)
        (CFSG.LieType.Universal.Spin.quadPlus 4 K)
        (CFSG.LieType.Universal.Spin.coe_quadPlus 4 K)).symm)).1
  obtain ⟨h2, -⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.OrthogonalOuter.ordProj_two_card_outer_reindex_le
      Nat.prime_two hf.pos hK (plusIndexEquiv 4) (CFSG.LieType.Universal.Spin.quadPlus 4 K) hab
      (Qc := coordinateQuadPlus 4 K) rfl hQ
  have hout : Nat.card (Outer X) =
      Nat.card (Outer (matrixProjectiveDerived (coordinateQuadPlus 4 K))) :=
    Nat.card_congr (CFSG.ComponentClassification.OuterAutomorphisms.equivalence e).toEquiv
  rw [hout]
  have h := h2 rfl
  rw [ordProj_two_index_matrixProjectiveImage_four, ordProj_two_eq_one_of_odd' hf] at h
  simpa using h

end Index

section Habel

variable {K : Type} [Field K] [Finite K]

theorem isCyclic_map_outer_of_isPGroup_plus_four {X : Type} [Group X] [Finite X] {f : ℕ}
    (hf : Odd f) (hK : Nat.card K = 2 ^ f)
    (e : X ≃* matrixProjectiveDerived (coordinateQuadPlus 4 K)) :
    ∀ B : Subgroup (MulAut X), IsPGroup 2 B →
      IsCyclic (B.map (QuotientGroup.mk' (inner X))) := by
  have : CharP K 2 := LinearPilot.charP_two_of_card_eq_two_pow hK
  intro B hB
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hB' : IsPGroup 2 (B.map (QuotientGroup.mk' (inner X))) := hB.map _
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hB'
  have hdvd : 2 ^ k ∣ Nat.card (Outer X) := hk ▸ Subgroup.card_subgroup_dvd_card _
  have h2 := ordProj_two_card_outer_le_two_plus_four hf hK e
  have hle : 2 ^ k ≤ ordProj[2] (Nat.card (Outer X)) :=
    Nat.le_of_dvd (Nat.ordProj_pos _ _)
      ((Nat.prime_two.pow_dvd_iff_dvd_ordProj Nat.card_pos.ne').mp hdvd)
  exact SeitzQ2.isCyclic_of_card_le_two (by rw [hk]; omega)

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem habel_plus_of_odd_four (hset : SeitzSetting G L) {f : ℕ} (hf : Odd f)
    (hK : Nat.card K = 2 ^ f) (e : L ≃* matrixProjectiveDerived (coordinateQuadPlus 4 K)) {t : G}
    (ht : orderOf t = 2) (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t) :
    ∀ S : Sylow 2 G, (S : Subgroup G) ≤ centralizer ({t} : Set G) →
      ∀ y ∈ (S : Subgroup G), ∀ z ∈ (S : Subgroup G), y * z * y⁻¹ * z⁻¹ ∈ L := by
  have htC := LinearPilot.mem_centralizer_of_inf_eq_zpowers hKt
  exact commutator_mem_of_sylow_le_centralizer_of_isCyclic_outer_two htC ht
    (CFSG.EvenSmallLie.centralizer_le_normalizer_of_standard hset.standardSetting.standard htC ht)
    hKt (isCyclic_map_outer_of_isPGroup_plus_four hf hK e)

end Habel

end CFSG.SeitzReduction.OmegaPilot
