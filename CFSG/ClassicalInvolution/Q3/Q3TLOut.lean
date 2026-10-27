module

public import CFSG.ClassicalInvolution.Q3.Q3TJExc
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalModelOuterTwoPart

public section

namespace CFSG.ClassicalInvolution.Q3.Q3T

open Matrix CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.Spin CFSG.ClassicalGroups.Orthogonal
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinearFiltration
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointPlusFamilyOrbit
open CFSG.ComponentClassification.CatalogueBOrthogonalPointReindexCovariance
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.OrthogonalOuter
open scoped Pointwise

theorem sq_mem_commutator_of_sq_eq_one {G : Type*} [Group G]
    (h : ∀ a : Abelianization G, a ^ 2 = 1) (g : G) : g ^ 2 ∈ commutator G := by
  rw [← Abelianization.ker_of, MonoidHom.mem_ker, map_pow]
  exact h _

theorem sq_mem_inner_of_mem_isometryRange {K : Type} [Field K] {d : ℕ}
    {Q : QuadraticForm K (Fin d → K)} (h : ∀ a : Abelianization (matrixIsometries Q), a ^ 2 = 1)
    {a : MulAut (matrixProjectiveDerived Q)} (ha : a ∈ (isometryConjugationHom Q).range) :
    a ^ 2 ∈ inner (matrixProjectiveDerived Q) := by
  obtain ⟨g, rfl⟩ := ha
  rw [← map_pow, inner_eq_map_commutator]
  exact Subgroup.mem_map_of_mem _ (sq_mem_commutator_of_sq_eq_one h g)

theorem mem_isometryRange_or {K : Type} [Field K] [Finite K] (hK : Nat.card K = 3) {d : ℕ}
    {Q : QuadraticForm K (Fin d → K)} (hQ : ∃ v, Q v ≠ 0) {a b : MulAut (matrixProjectiveDerived Q)}
    (ha : a ∈ matrixProjectiveImage Q) (hb : b ∈ matrixProjectiveImage Q) :
    a ∈ (isometryConjugationHom Q).range ∨ b ∈ (isometryConjugationHom Q).range ∨
      a * b ∈ (isometryConjugationHom Q).range := by
  have hsq : (powMonoidHom 2 : Kˣ →* Kˣ).range.index = 2 := by
    rw [IsCyclic.index_powMonoidHom_range, Nat.card_units, hK]
    norm_num
  have hring : Nat.card (K ≃+* K) = 1 := by
    have : Subsingleton (K ≃+* K) := ⟨fun a b =>
      (ringEquiv_eq_refl_of_card_three hK a).trans (ringEquiv_eq_refl_of_card_three hK b).symm⟩
    exact Nat.card_eq_one_iff_unique.mpr ⟨inferInstance, ⟨RingEquiv.refl K⟩⟩
  have hb' := relIndex_isometryRange_dvd Q hQ
  rw [hsq] at hb'
  have hc := (relIndex_linearRange_dvd Q).trans
    (Subgroup.card_subgroup_dvd_card (fieldProjection Q).range)
  rw [hring, Nat.dvd_one] at hc
  have h2 := isometryConjugationHom_range_le Q
  have h3 : (linearConjugationHom Q).range ≤ matrixProjectiveImage Q := by
    rintro _ ⟨g, rfl⟩
    exact (mem_matrixProjectiveImage_iff _ _).mpr ⟨g.val, rfl⟩
  have hdvd :
      ((isometryConjugationHom Q).range.subgroupOf (matrixProjectiveImage Q)).index ∣ 2 := by
    change (isometryConjugationHom Q).range.relIndex (matrixProjectiveImage Q) ∣ 2
    rw [← Subgroup.relIndex_mul_relIndex _ _ _ h2 h3]
    change _ * (linearConjugationHom Q).range.relIndex (matrixProjectiveConjugationHom Q).range ∣ 2
    rw [hc, mul_one]
    exact hb'
  rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h1
  · left
    have htop := Subgroup.index_eq_one.mp h1
    have hmem : (⟨a, ha⟩ : matrixProjectiveImage Q) ∈
        (isometryConjugationHom Q).range.subgroupOf (matrixProjectiveImage Q) := by
      rw [htop]
      exact Subgroup.mem_top _
    exact hmem
  · have key := Subgroup.mul_mem_iff_of_index_two h1 (a := ⟨a, ha⟩) (b := ⟨b, hb⟩)
    simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul] at key
    by_cases hA : a ∈ (isometryConjugationHom Q).range
    · exact Or.inl hA
    · by_cases hB : b ∈ (isometryConjugationHom Q).range
      · exact Or.inr (Or.inl hB)
      · exact Or.inr (Or.inr (key.mpr (iff_of_false hA hB)))

theorem sq_eq_one_abelianization_reindex {K : Type} [Field K] {ι : Type} [Fintype ι]
    [DecidableEq ι] {d p : ℕ} (e : ι ≃ Fin d) (Q₀ : QuadraticForm K (ι → K))
    (hab : IsometryAbelianizationBound p Q₀) :
    ∀ a : Abelianization (matrixIsometries (reindexQuadraticForm e Q₀)), a ^ 2 = 1 := by
  intro a
  have := hab.1
  apply (MulEquiv.abelianizationCongr (matrixIsometriesReindexEquiv e Q₀)).injective
  rw [map_pow, map_one]
  exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
    (CFSG.IsElementaryAbelian.exponent_dvd_p 2 _) _

theorem congr_mem_matrixProjectiveImage
    (β : MulAut (StatedProj (StatedOmega (StatedQuadPlus 4 (GaloisField 3 1)))))
    (hβ : β • statedPointFamily (coe_quadPlus 4 (GaloisField 3 1)) =
      statedPointFamily (coe_quadPlus 4 (GaloisField 3 1))) :
    MulAut.congr (plusCoordinateEquiv 4 (GaloisField 3 1)) β ∈
      matrixProjectiveImage (coordinateQuadPlus 4 (GaloisField 3 1)) := by
  have hK : Nat.card (GaloisField 3 1) = 3 ^ 1 := by rw [natCard_galoisField_three, pow_one]
  have hT : StatedClassicalModel (StatedProj (StatedOmega (StatedQuadPlus 4 (GaloisField 3 1))))
      .POmegaPlus 4 3 1 :=
    ⟨⟨Nat.prime_three, le_rfl, le_rfl⟩, GaloisField 3 1, inferInstance, inferInstance, hK,
      ⟨MulEquiv.refl _⟩⟩
  rw [← coordinate_plus_family_eq_matrixImage hT _ hK (MulEquiv.refl _),
    mem_projectivePointFamilyAut_iff]
  have key := familyTransport_automorphism (plusCoordinateEquiv 4 (GaloisField 3 1))
    (statedPointFamily (coe_quadPlus 4 (GaloisField 3 1))) β
  rw [hβ, plusCoordinate_pointFamily] at key
  exact key.symm

theorem sq_mem_inner_or_of_smul_pointFamily
    (β₁ β₂ : MulAut (StatedProj (StatedOmega (StatedQuadPlus 4 (GaloisField 3 1)))))
    (h₁ : β₁ • statedPointFamily (coe_quadPlus 4 (GaloisField 3 1)) =
      statedPointFamily (coe_quadPlus 4 (GaloisField 3 1)))
    (h₂ : β₂ • statedPointFamily (coe_quadPlus 4 (GaloisField 3 1)) =
      statedPointFamily (coe_quadPlus 4 (GaloisField 3 1))) :
    β₁ ^ 2 ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner _ ∨
      β₂ ^ 2 ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner _ ∨
      (β₁ * β₂) ^ 2 ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner _ := by
  have hK : Nat.card (GaloisField 3 1) = 3 ^ 1 := by rw [natCard_galoisField_three, pow_one]
  have hT : StatedClassicalModel (StatedProj (StatedOmega (StatedQuadPlus 4 (GaloisField 3 1))))
      .POmegaPlus 4 3 1 :=
    ⟨⟨Nat.prime_three, le_rfl, le_rfl⟩, GaloisField 3 1, inferInstance, inferInstance, hK,
      ⟨MulEquiv.refl _⟩⟩
  have hab := orthogonal_model_isometry_abelianization_order_bound _ .POmegaPlus
    (.inr (.inl rfl)) 4 3 1 hT (GaloisField 3 1) hK (quadPlus 4 (GaloisField 3 1))
    (coe_quadPlus 4 (GaloisField 3 1)) (MulEquiv.refl _)
  have hsq2 : ∀ a : Abelianization (matrixIsometries (coordinateQuadPlus 4 (GaloisField 3 1))),
      a ^ 2 = 1 :=
    sq_eq_one_abelianization_reindex (plusIndexEquiv 4) (quadPlus 4 (GaloisField 3 1)) hab
  have hQ := exists_nonzero_value _ (coordinate_model_intrinsic_plus hT _ hK (MulEquiv.refl _)).1
  have hpull : ∀ β : MulAut (StatedProj (StatedOmega (StatedQuadPlus 4 (GaloisField 3 1)))),
      MulAut.congr (plusCoordinateEquiv 4 (GaloisField 3 1)) β ∈
        (isometryConjugationHom (coordinateQuadPlus 4 (GaloisField 3 1))).range →
      β ^ 2 ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner _ := by
    intro β hβ
    obtain ⟨y, hy⟩ := sq_mem_inner_of_mem_isometryRange hsq2 hβ
    refine ⟨(plusCoordinateEquiv 4 (GaloisField 3 1)).symm y,
      (MulAut.congr (plusCoordinateEquiv 4 (GaloisField 3 1))).injective ?_⟩
    rw [CFSG.ComponentClassification.OuterAutomorphisms.congr_conj, MulEquiv.apply_symm_apply,
      map_pow, ← hy]
  rcases mem_isometryRange_or natCard_galoisField_three hQ (congr_mem_matrixProjectiveImage β₁ h₁)
      (congr_mem_matrixProjectiveImage β₂ h₂) with h | h | h
  · exact Or.inl (hpull β₁ h)
  · exact Or.inr (Or.inl (hpull β₂ h))
  · rw [← map_mul] at h
    exact Or.inr (Or.inr (hpull _ h))

end CFSG.ClassicalInvolution.Q3.Q3T
