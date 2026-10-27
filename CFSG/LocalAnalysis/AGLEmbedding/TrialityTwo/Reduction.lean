module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointPlusFamilyOrbitModel
import CFSG.LocalAnalysis.ComponentInitial.OrthogonalModelOuterTwoPart
import CFSG.LocalAnalysis.AGLEmbedding.TrialityTwo.ReductionFixed

public noncomputable section

namespace CFSG.AGLEmbedding.TrialityTwo

open CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.Spin
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.OrthogonalOuter
open CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinearFiltration
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open CFSG.ComponentClassification.CatalogueBOrthogonalPointPlusFamilyOrbit
open CFSG.ComponentClassification.CatalogueBOrthogonalPointReindexCovariance
open CFSG.ComponentClassification.CatalogueBOrthogonalPointPlusBorel
open CFSG.ComponentClassification.CatalogueBOrthogonalSmallFamilyOrbit
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open scoped Pointwise

theorem relIndex_inner_matrixProjectiveImage_le_two {T : Type} [Group T]
    (h : StatedClassicalModel T .POmegaPlus 4 2 1) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2 ^ 1) (e : T ≃* StatedProj (StatedOmega (StatedQuadPlus 4 K))) :
    0 < (inner (matrixProjectiveDerived (coordinateQuadPlus 4 K))).relIndex
        (matrixProjectiveImage (coordinateQuadPlus 4 K)) ∧
      (inner (matrixProjectiveDerived (coordinateQuadPlus 4 K))).relIndex
        (matrixProjectiveImage (coordinateQuadPlus 4 K)) ≤ 2 := by
  have hp : Nat.Prime 2 := Nat.prime_two
  have hab := orthogonal_model_isometry_abelianization_order_bound T .POmegaPlus
    (.inr (.inl rfl)) 4 2 1 h K hK (quadPlus 4 K) (coe_quadPlus 4 K) e
  have hQ := exists_nonzero_value _ (coordinate_model_intrinsic_plus h K hK e).1
  have ha := relIndex_inner_dvd (coordinateQuadPlus 4 K)
  have hA : Nat.card (Abelianization (matrixIsometries (coordinateQuadPlus 4 K))) ≤ 2 := by
    rw [coordinateQuadPlus, card_abelianization_matrixIsometries_reindex]
    exact hab.2.2 rfl
  have hb := relIndex_isometryRange_dvd (coordinateQuadPlus 4 K) hQ
  have hunits : Nat.card Kˣ = 1 := by
    rw [Nat.card_units, hK]
    rfl
  have hsq : (powMonoidHom 2 : Kˣ →* Kˣ).range.index = 1 := by
    rw [IsCyclic.index_powMonoidHom_range, hunits]
    norm_num
  have hc := (relIndex_linearRange_dvd (coordinateQuadPlus 4 K)).trans
    ((Subgroup.card_subgroup_dvd_card (fieldProjection (coordinateQuadPlus 4 K)).range).trans
      (card_ringAut_and_isCyclic hp K hK).1.dvd)
  have hc' : (linearConjugationHom (coordinateQuadPlus 4 K)).range.relIndex
      (matrixProjectiveImage (coordinateQuadPlus 4 K)) = 1 := Nat.dvd_one.1 hc
  rw [hsq, Nat.dvd_one] at hb
  have h1 : CFSG.ComponentClassification.OuterAutomorphisms.inner
      (matrixProjectiveDerived (coordinateQuadPlus 4 K)) ≤
        (isometryConjugationHom (coordinateQuadPlus 4 K)).range := by
    rw [inner_eq_map_commutator (coordinateQuadPlus 4 K)]
    exact Subgroup.map_le_range _ _
  have h2 := isometryConjugationHom_range_le (coordinateQuadPlus 4 K)
  have h3 : (linearConjugationHom (coordinateQuadPlus 4 K)).range ≤
      matrixProjectiveImage (coordinateQuadPlus 4 K) := by
    rintro _ ⟨g, rfl⟩
    exact (mem_matrixProjectiveImage_iff (coordinateQuadPlus 4 K) _).mpr ⟨g.val, rfl⟩
  rw [← Subgroup.relIndex_mul_relIndex _ _ _ (h1.trans h2) h3,
    ← Subgroup.relIndex_mul_relIndex _ _ _ h1 h2, hb, hc', mul_one, mul_one]
  have hA0 := Nat.card_pos (α := Abelianization (matrixIsometries (coordinateQuadPlus 4 K)))
  exact ⟨Nat.pos_of_dvd_of_pos ha hA0, (Nat.le_of_dvd hA0 ha).trans hA⟩

theorem mem_of_pow_mem_of_pow_three_eq_one {G : Type*} [Group G] {H : Subgroup G} {a : G}
    (h3 : a ^ 3 = 1) {k : ℕ} (hk0 : 0 < k) (hk2 : k ≤ 2) (hk : a ^ k ∈ H) : a ∈ H := by
  rcases (show k = 1 ∨ k = 2 by omega) with rfl | rfl
  · simpa using hk
  · have h4 : a = (a ^ 2) ^ 2 := by
      rw [← pow_mul, show 2 * 2 = 3 + 1 by rfl, pow_succ, h3, one_mul]
    rw [h4]
    exact H.pow_mem hk 2

theorem mem_inner_of_smul_statedPointFamily_eq {T : Type} [Group T]
    (h : StatedClassicalModel T .POmegaPlus 4 2 1) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2 ^ 1) (e : T ≃* StatedProj (StatedOmega (StatedQuadPlus 4 K)))
    (α : MulAut (StatedProj (StatedOmega (StatedQuadPlus 4 K))))
    (hα : α • statedPointFamily (coe_quadPlus 4 K) = statedPointFamily (coe_quadPlus 4 K))
    (h3 : α ^ 3 = 1) : α ∈ inner (StatedProj (StatedOmega (StatedQuadPlus 4 K))) := by
  set φ := plusCoordinateEquiv 4 K
  have key := familyTransport_automorphism φ (statedPointFamily (coe_quadPlus 4 K)) α
  rw [hα, plusCoordinate_pointFamily] at key
  have hmem : MulAut.congr φ α ∈ projectivePointFamilyAut (coordinateQuadPlus 4 K) := by
    rw [mem_projectivePointFamilyAut_iff]
    exact key.symm
  rw [((orthogonal_geometry_model_stabilizer_preserving_image T .POmegaPlus
    (.inr (.inl rfl)) 4 2 1 h) K hK e).1] at hmem
  obtain ⟨hpos, hle⟩ := relIndex_inner_matrixProjectiveImage_le_two h hK e
  have hpow := Subgroup.pow_index_mem
    ((inner (matrixProjectiveDerived (coordinateQuadPlus 4 K))).subgroupOf
      (matrixProjectiveImage (coordinateQuadPlus 4 K))) ⟨MulAut.congr φ α, hmem⟩
  rw [Subgroup.mem_subgroupOf, Subgroup.coe_pow] at hpow
  have h3' : (MulAut.congr φ α) ^ 3 = 1 := by rw [← map_pow, h3, map_one]
  have hin := mem_of_pow_mem_of_pow_three_eq_one h3' hpos hle hpow
  rw [← CFSG.ComponentClassification.OuterAutomorphisms.inner_map_congr φ] at hin
  obtain ⟨β, hβ, hβα⟩ := hin
  rwa [(MulAut.congr φ).injective hβα] at hβ

theorem smul_statedPointFamily_cases {T : Type} [Group T]
    (h : StatedClassicalModel T .POmegaPlus 4 2 1) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2 ^ 1) (e : T ≃* StatedProj (StatedOmega (StatedQuadPlus 4 K)))
    (α : MulAut (StatedProj (StatedOmega (StatedQuadPlus 4 K))))
    (hα : α ∉ inner (StatedProj (StatedOmega (StatedQuadPlus 4 K)))) (h3 : α ^ 3 = 1) :
    (α • statedPointFamily (coe_quadPlus 4 K) =
        conjugacyFamily (statedProjectiveSubspaceStabilizer (StatedQuadPlus 4 K) (flag 4 K 4)) ∧
      (α ^ 2) • statedPointFamily (coe_quadPlus 4 K) =
        conjugacyFamily (statedProjectiveSubspaceStabilizer (StatedQuadPlus 4 K)
          (Xstar 4 K (by norm_num)))) ∨
    (α • statedPointFamily (coe_quadPlus 4 K) =
        conjugacyFamily (statedProjectiveSubspaceStabilizer (StatedQuadPlus 4 K)
          (Xstar 4 K (by norm_num))) ∧
      (α ^ 2) • statedPointFamily (coe_quadPlus 4 K) =
        conjugacyFamily (statedProjectiveSubspaceStabilizer (StatedQuadPlus 4 K)
          (flag 4 K 4))) := by
  set F₀ := statedPointFamily (coe_quadPlus 4 K)
  have hsub := stated_pointFamily_orbit_subset (K := K) (n := 4) rfl
  have h1 := hsub (MulAction.mem_orbit F₀ α)
  have h2 := hsub (MulAction.mem_orbit F₀ (α ^ 2))
  have hne1 : α • F₀ ≠ F₀ := fun hF => hα (mem_inner_of_smul_statedPointFamily_eq h hK e α hF h3)
  have hne2 : (α ^ 2) • F₀ ≠ F₀ := by
    intro hF
    have h6 : (α ^ 2) ^ 3 = 1 := by rw [← pow_mul, mul_comm, pow_mul, h3, one_pow]
    have hin := mem_inner_of_smul_statedPointFamily_eq h hK e (α ^ 2) hF h6
    refine hα ?_
    have h4 : α = (α ^ 2) ^ 2 := by
      rw [← pow_mul, show 2 * 2 = 3 + 1 by rfl, pow_succ, h3, one_mul]
    rw [h4]
    exact Subgroup.pow_mem _ hin 2
  have hne12 : α • F₀ ≠ (α ^ 2) • F₀ := by
    intro hF
    apply hne1
    rw [pow_two, mul_smul] at hF
    exact (smul_left_cancel α hF).symm
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h1 h2
  rcases h1 with h1 | h1 | h1
  · exact absurd h1 hne1
  · rcases h2 with h2 | h2 | h2
    · exact absurd h2 hne2
    · exact absurd (h1.trans h2.symm) hne12
    · exact Or.inl ⟨h1, h2⟩
  · rcases h2 with h2 | h2 | h2
    · exact absurd h2 hne2
    · exact Or.inr ⟨h1, h2⟩
    · exact absurd (h1.trans h2.symm) hne12

theorem mem_solidFamilies_iff_mem_smul {T : Type} [Group T]
    (h : StatedClassicalModel T .POmegaPlus 4 2 1) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2 ^ 1) (e : T ≃* StatedProj (StatedOmega (StatedQuadPlus 4 K)))
    (α : MulAut (StatedProj (StatedOmega (StatedQuadPlus 4 K))))
    (hα : α ∉ inner (StatedProj (StatedOmega (StatedQuadPlus 4 K)))) (h3 : α ^ 3 = 1)
    (Y : Subgroup (StatedProj (StatedOmega (StatedQuadPlus 4 K)))) :
    (Y ∈ conjugacyFamily (statedProjectiveSubspaceStabilizer (StatedQuadPlus 4 K) (flag 4 K 4)) ∨
        Y ∈ conjugacyFamily (statedProjectiveSubspaceStabilizer (StatedQuadPlus 4 K)
          (Xstar 4 K (by norm_num)))) ↔
      (Y ∈ α • statedPointFamily (coe_quadPlus 4 K) ∨
        Y ∈ (α ^ 2) • statedPointFamily (coe_quadPlus 4 K)) := by
  rcases smul_statedPointFamily_cases h hK e α hα h3 with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h1, h2]
  · rw [h1, h2, or_comm]

theorem exists_mem_solidFamilies_iff_of_apply_eq {T : Type} [Group T]
    (h : StatedClassicalModel T .POmegaPlus 4 2 1) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2 ^ 1) (e : T ≃* StatedProj (StatedOmega (StatedQuadPlus 4 K)))
    (α : MulAut (StatedProj (StatedOmega (StatedQuadPlus 4 K))))
    (hα : α ∉ inner (StatedProj (StatedOmega (StatedQuadPlus 4 K)))) (h3 : α ^ 3 = 1)
    {x : StatedProj (StatedOmega (StatedQuadPlus 4 K))} (hx : α x = x) :
    (∃ Y, (Y ∈ conjugacyFamily (statedProjectiveSubspaceStabilizer (StatedQuadPlus 4 K)
          (flag 4 K 4)) ∨
        Y ∈ conjugacyFamily (statedProjectiveSubspaceStabilizer (StatedQuadPlus 4 K)
          (Xstar 4 K (by norm_num)))) ∧ x ∈ Y) ↔
      ∃ Y ∈ statedPointFamily (coe_quadPlus 4 K), x ∈ Y := by
  have hx2 : (α ^ 2) x = x := by rw [pow_two, MulAut.mul_apply, hx, hx]
  simp_rw [mem_solidFamilies_iff_mem_smul h hK e α hα h3]
  constructor
  · rintro ⟨Y, hY | hY, hxY⟩
    · exact (exists_mem_smul_family_iff hx _).1 ⟨Y, hY, hxY⟩
    · exact (exists_mem_smul_family_iff hx2 _).1 ⟨Y, hY, hxY⟩
  · intro hex
    obtain ⟨Y, hY, hxY⟩ := (exists_mem_smul_family_iff hx _).2 hex
    exact ⟨Y, Or.inl hY, hxY⟩

end CFSG.AGLEmbedding.TrialityTwo
