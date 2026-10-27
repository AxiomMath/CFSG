module

public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalModelOuterTwoPart

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.DW

open CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.Spin
open CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinearFiltration
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.OrthogonalOuter
open CFSG.ComponentClassification.CatalogueBOrthogonalPointPlusFamilyOrbit
  (orthogonal_geometry_plus_point_family_orbit)

theorem isPGroup_of_card_dvd_two {H : Type*} [Group H] (h : Nat.card H ∣ 2) : IsPGroup 2 H := by
  rcases (Nat.dvd_prime Nat.prime_two).mp h with h1 | h1
  · exact IsPGroup.of_card (n := 0) (by rw [h1, pow_zero])
  · exact IsPGroup.of_card (n := 1) (by rw [h1, pow_one])

theorem isPGroup_outer_of_mulEquiv {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y)
    (h : IsPGroup 2 (Outer Y)) : IsPGroup 2 (Outer X) :=
  h.of_equiv (equivalence e).symm

theorem statedClassicalModel_of_lieModel {X : Type} [Group X] {t : StatedLieTag} {n p f : ℕ}
    (ht : t ∈ classicalTags) (h : LieModel X t n p f) : StatedClassicalModel X t n p f :=
  CFSG.Blueprint.LieModel.statedClassicalModel h ht

theorem card_outer_matrixProjectiveDerived_dvd_two {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2 ^ 1) {d : ℕ} (Q : QuadraticForm K (Fin d → K)) (hQ : ∃ v, Q v ≠ 0)
    (hab : Nat.card (Abelianization (matrixIsometries Q)) ≤ 2)
    (hE : matrixProjectiveImage Q = ⊤) :
    Nat.card (Outer (matrixProjectiveDerived Q)) ∣ 2 := by
  have hk : (matrixProjectiveImage Q).index = 1 := by rw [hE, Subgroup.index_top]
  rw [card_outer_eq Q, hk, mul_one]
  have ha : (CFSG.ComponentClassification.OuterAutomorphisms.inner
      (matrixProjectiveDerived Q)).relIndex (isometryConjugationHom Q).range ∣ 2 := by
    refine (relIndex_inner_dvd Q).trans ?_
    have hpos : 0 < Nat.card (Abelianization (matrixIsometries Q)) := Nat.card_pos
    rcases (show Nat.card (Abelianization (matrixIsometries Q)) = 1 ∨
        Nat.card (Abelianization (matrixIsometries Q)) = 2 by omega) with h | h
    · rw [h]
      exact one_dvd 2
    · rw [h]
  have hu : Subsingleton Kˣ := by
    have hcard : Nat.card Kˣ = 1 := by rw [Nat.card_units, hK]; rfl
    exact (Nat.card_eq_one_iff_unique.mp hcard).1
  have hb : (isometryConjugationHom Q).range.relIndex (linearConjugationHom Q).range ∣ 1 := by
    refine (relIndex_isometryRange_dvd Q hQ).trans ?_
    have h1 : (powMonoidHom 2 : Kˣ →* Kˣ).range = ⊤ :=
      eq_top_iff.mpr fun u _ => MonoidHom.mem_range.mpr ⟨1, Subsingleton.elim _ _⟩
    rw [h1, Subgroup.index_top]
  have hc : (linearConjugationHom Q).range.relIndex (matrixProjectiveImage Q) ∣ 1 :=
    ((relIndex_linearRange_dvd Q).trans
      (Subgroup.card_subgroup_dvd_card (fieldProjection Q).range)).trans
      (card_ringAut_and_isCyclic Nat.prime_two K hK).1.dvd
  simpa using Nat.mul_dvd_mul (Nat.mul_dvd_mul ha hb) hc

theorem isPGroup_outer_POmegaPlus {X : Type} [Group X] {n : ℕ} (hn : 5 ≤ n)
    (h : LieModel X .POmegaPlus n 2 1) : IsPGroup 2 (Outer X) := by
  have hT := statedClassicalModel_of_lieModel (by decide) h
  have h0 := hT
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := h0
  have hab := orthogonal_model_isometry_abelianization_order_bound X .POmegaPlus
    (.inr (.inl rfl)) n 2 1 hT K hK (quadPlus n K) (coe_quadPlus n K) e
  have hEA := ((orthogonal_geometry_model_stabilizer_preserving_image X .POmegaPlus
    (.inr (.inl rfl)) n 2 1 hT) K hK e).1
  have hE : matrixProjectiveImage (coordinateQuadPlus n K) = ⊤ := by
    rw [← hEA, (orthogonal_geometry_plus_point_family_orbit hT hK e).2.2.2.2.1 hn]
  have hab' : Nat.card (Abelianization (matrixIsometries (coordinateQuadPlus n K))) ≤ 2 := by
    rw [show coordinateQuadPlus n K = reindexQuadraticForm (plusIndexEquiv n) (quadPlus n K)
      from rfl, card_abelianization_matrixIsometries_reindex]
    exact hab.2.2 rfl
  exact isPGroup_outer_of_mulEquiv (coordinatePlusWitnessEquiv K e) (isPGroup_of_card_dvd_two
    (card_outer_matrixProjectiveDerived_dvd_two hK _
      (exists_nonzero_value _ (coordinate_model_intrinsic_plus hT K hK e).1) hab' hE))

theorem isPGroup_outer_POmegaMinus {X : Type} [Group X] {n : ℕ}
    (h : LieModel X .POmegaMinus n 2 1) : IsPGroup 2 (Outer X) := by
  have hT := statedClassicalModel_of_lieModel (by decide) h
  have h0 := hT
  obtain ⟨⟨-, -, hn⟩, K, _, _, hK, b, c, hirr, ⟨e⟩⟩ := h0
  have hn1 : 1 ≤ n := by omega
  have hab := orthogonal_model_isometry_abelianization_order_bound X .POmegaMinus
    (.inr (.inr rfl)) n 2 1 hT K hK b c hirr (quadMinus n K b c) (coe_quadMinus n K b c) e
  have hE : matrixProjectiveImage (coordinateQuadMinus n K hn1 b c) = ⊤ := by
    rw [← ((orthogonal_geometry_model_stabilizer_preserving_image X .POmegaMinus
      (.inr (.inr rfl)) n 2 1 hT) hn1 K hK b c hirr e).1]
    exact ((OrthogonalTail.orthogonal_geometry_tail_model_point_family_invariant X
      .POmegaMinus (.inr rfl) n 2 1 hT) hn1 K hK b c hirr).2
  have hab' :
      Nat.card (Abelianization (matrixIsometries (coordinateQuadMinus n K hn1 b c))) ≤ 2 := by
    rw [show coordinateQuadMinus n K hn1 b c =
      reindexQuadraticForm (minusIndexEquiv n hn1) (quadMinus n K b c) from rfl,
      card_abelianization_matrixIsometries_reindex]
    exact hab.2.2 rfl
  exact isPGroup_outer_of_mulEquiv (coordinateMinusWitnessEquiv K hn1 b c e)
    (isPGroup_of_card_dvd_two (card_outer_matrixProjectiveDerived_dvd_two hK _
      (exists_nonzero_value _ (coordinate_model_intrinsic_minus hT K hK b c hirr e).1) hab' hE))

end CFSG.LargeExtraspecial.DW
