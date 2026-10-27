module

public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalModelOuterTwoPart
public import CFSG.RankThree.PartTwo.KFacts.AutPSp4Odd
public import CFSG.RankThree.PartTwo.Sec4.Item47Diag
public import CFSG.GH74.Exceptional.UnitaryFourTwo
public import CFSG.RankThree.PartTwo.Census.Carrier.SpinTDOdd
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.UnitaryTauCeti

public section

namespace CFSG.AGLEmbedding

open CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)

section Orthogonal

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.OrthogonalOuter
open CFSG.LieType.Universal.Spin
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinearFiltration
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open CFSG.ComponentClassification.CatalogueBOrthogonalPointPlusFamilyOrbit
open scoped Pointwise

theorem exists_card_outer_eq_mul_of_omegaPlus_two {T : Type} [Group T] {m : ℕ}
    (h : StatedClassicalModel T .POmegaPlus m 2 1) :
    ∃ a k : ℕ, Nat.card (Outer T) = a * k ∧ 0 < a ∧ a ≤ 2 ∧ 0 < k ∧ k ≤ 3 := by
  have h0 := h
  obtain ⟨⟨hp, -, hm⟩, K, _, _, hK, ⟨e⟩⟩ := h0
  have hab := orthogonal_model_isometry_abelianization_order_bound T .POmegaPlus
    (.inr (.inl rfl)) m 2 1 h K hK (quadPlus m K) (coe_quadPlus m K) e
  have hEA := ((orthogonal_geometry_model_stabilizer_preserving_image T .POmegaPlus
    (.inr (.inl rfl)) m 2 1 h) K hK e).1
  have horbit := orthogonal_geometry_plus_point_family_orbit h hK e
  have hout : Nat.card (Outer T) =
      Nat.card (Outer (matrixProjectiveDerived (coordinateQuadPlus m K))) :=
    Nat.card_congr (CFSG.ComponentClassification.OuterAutomorphisms.equivalence
      (coordinatePlusWitnessEquiv K e)).toEquiv
  have hQ := exists_nonzero_value _ (coordinate_model_intrinsic_plus h K hK e).1
  have hidx : (matrixProjectiveImage (coordinateQuadPlus m K)).index ≤ 3 := by
    have hst : (projectivePointFamilyAut (coordinateQuadPlus m K)).index =
        (MulAction.orbit (MulAut (matrixProjectiveDerived (coordinateQuadPlus m K)))
          (projectivePointFamily (coordinateQuadPlus m K))).ncard :=
      MulAction.index_stabilizer _ _
    rcases (show m = 4 ∨ 5 ≤ m by omega) with rfl | h5
    · rw [← hEA, hst]
      exact (horbit.2.2.2.2.2 rfl).2
    · rw [← hEA, horbit.2.2.2.2.1 h5, Subgroup.index_top]
      norm_num
  have ha := relIndex_inner_dvd (coordinateQuadPlus m K)
  have hA : Nat.card (Abelianization (matrixIsometries (coordinateQuadPlus m K))) ≤ 2 := by
    rw [coordinateQuadPlus, card_abelianization_matrixIsometries_reindex]
    exact hab.2.2 rfl
  have hb := relIndex_isometryRange_dvd (coordinateQuadPlus m K) hQ
  have hunits : Nat.card Kˣ = 1 := by
    rw [Nat.card_units, hK]
    rfl
  have hsq : (powMonoidHom 2 : Kˣ →* Kˣ).range.index = 1 := by
    rw [IsCyclic.index_powMonoidHom_range, hunits]
    norm_num
  have hc := (relIndex_linearRange_dvd (coordinateQuadPlus m K)).trans
    ((Subgroup.card_subgroup_dvd_card (fieldProjection (coordinateQuadPlus m K)).range).trans
      (card_ringAut_and_isCyclic hp K hK).1.dvd)
  have hc' : (linearConjugationHom (coordinateQuadPlus m K)).range.relIndex
      (matrixProjectiveImage (coordinateQuadPlus m K)) = 1 := Nat.dvd_one.1 hc
  rw [hsq, Nat.dvd_one] at hb
  have hpos := Nat.card_pos (α := Outer (matrixProjectiveDerived (coordinateQuadPlus m K)))
  rw [card_outer_eq, hb, hc', mul_one, mul_one] at hpos
  refine ⟨_, _, by rw [hout, card_outer_eq, hb, hc', mul_one, mul_one],
    Nat.pos_of_mul_pos_right hpos, ?_, Nat.pos_of_mul_pos_left hpos, hidx⟩
  have hA0 := Nat.card_pos (α := Abelianization (matrixIsometries (coordinateQuadPlus m K)))
  exact (Nat.le_of_dvd hA0 ha).trans hA

theorem card_outer_le_two_of_omegaMinus_two {T : Type} [Group T] {m : ℕ}
    (h : StatedClassicalModel T .POmegaMinus m 2 1) :
    0 < Nat.card (Outer T) ∧ Nat.card (Outer T) ≤ 2 := by
  have h0 := h
  obtain ⟨⟨hp, -, hm⟩, K, _, _, hK, b, c, hirr, ⟨e⟩⟩ := h0
  have hm1 : 1 ≤ m := by omega
  have hab := orthogonal_model_isometry_abelianization_order_bound T .POmegaMinus
    (.inr (.inr rfl)) m 2 1 h K hK b c hirr (quadMinus m K b c) (coe_quadMinus m K b c) e
  have hE : matrixProjectiveImage (coordinateQuadMinus m K hm1 b c) = ⊤ := by
    rw [← ((orthogonal_geometry_model_stabilizer_preserving_image T .POmegaMinus
      (.inr (.inr rfl)) m 2 1 h) hm1 K hK b c hirr e).1]
    exact ((OrthogonalTail.orthogonal_geometry_tail_model_point_family_invariant T
      .POmegaMinus (.inr rfl) m 2 1 h) hm1 K hK b c hirr).2
  have hout : Nat.card (Outer T) =
      Nat.card (Outer (matrixProjectiveDerived (coordinateQuadMinus m K hm1 b c))) :=
    Nat.card_congr (CFSG.ComponentClassification.OuterAutomorphisms.equivalence
      (coordinateMinusWitnessEquiv K hm1 b c e)).toEquiv
  have hQ := exists_nonzero_value _ (coordinate_model_intrinsic_minus h K hK b c hirr e).1
  have ha := relIndex_inner_dvd (coordinateQuadMinus m K hm1 b c)
  have hA :
      Nat.card (Abelianization (matrixIsometries (coordinateQuadMinus m K hm1 b c))) ≤ 2 := by
    rw [coordinateQuadMinus, card_abelianization_matrixIsometries_reindex]
    exact hab.2.2 rfl
  have hb := relIndex_isometryRange_dvd (coordinateQuadMinus m K hm1 b c) hQ
  have hunits : Nat.card Kˣ = 1 := by
    rw [Nat.card_units, hK]
    rfl
  have hsq : (powMonoidHom 2 : Kˣ →* Kˣ).range.index = 1 := by
    rw [IsCyclic.index_powMonoidHom_range, hunits]
    norm_num
  have hc := (relIndex_linearRange_dvd (coordinateQuadMinus m K hm1 b c)).trans
    ((Subgroup.card_subgroup_dvd_card
      (fieldProjection (coordinateQuadMinus m K hm1 b c)).range).trans
        (card_ringAut_and_isCyclic hp K hK).1.dvd)
  have hc' : (linearConjugationHom (coordinateQuadMinus m K hm1 b c)).range.relIndex
      (matrixProjectiveImage (coordinateQuadMinus m K hm1 b c)) = 1 := Nat.dvd_one.1 hc
  rw [hout]
  refine ⟨Nat.card_pos, ?_⟩
  rw [card_outer_eq]
  rw [hsq, Nat.dvd_one] at hb
  rw [hb, hc', hE, Subgroup.index_top, mul_one, mul_one, mul_one]
  have hA0 :=
    Nat.card_pos (α := Abelianization (matrixIsometries (coordinateQuadMinus m K hm1 b c)))
  exact (Nat.le_of_dvd hA0 ha).trans hA

end Orthogonal

section Unitary

open CFSG.RankThree.PartTwo.KFacts CFSG.RankThree.PartTwo.Sec4
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher

theorem sq_eq_one_of_psu_four_two {T : Type} [Group T]
    (h : StatedClassicalModel T .PSU 4 2 1) (x : Outer T) : x ^ 2 = 1 := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ :=
    CFSG.GH74.Exceptional.statedClassicalModel_PSp_two_three_of_PSU_four_two h
  have hK3 : Nat.card K = 3 ^ 1 := by simpa using hK
  have hodd : ringChar K ≠ 2 := by
    rw [CFSG.ClassicalGroups.Orthogonal.ringChar_eq_of_card_eq Nat.prime_three le_rfl hK3]
    norm_num
  have hsub : Subsingleton (K ≃+* K) :=
    (Nat.card_eq_one_iff_unique.mp (card_ringAut_and_isCyclic Nat.prime_three K hK3).1).1
  set φ := CFSG.ComponentClassification.OuterAutomorphisms.equivalence e
  apply φ.injective
  rw [map_pow, map_one]
  obtain ⟨α, hα⟩ := QuotientGroup.mk_surjective (φ x)
  rw [← hα]
  obtain ⟨A, σ, rfl⟩ := psp4_odd_automorphism_normal_form hodd α
  rw [Subsingleton.elim σ 1, map_one, mul_one, ← QuotientGroup.mk_pow]
  exact (QuotientGroup.eq_one_iff _).mpr (isInnerAut_spConjAut_sq A)

theorem not_dvd_card_outer_of_psu_four_two {T : Type} [Group T]
    (h : StatedClassicalModel T .PSU 4 2 1) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    ¬ p ∣ Nat.card (Outer T) := by
  intro hdvd
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨-, K, _, _, -, ⟨e⟩⟩ := id h
  have : Finite T := Finite.of_equiv _ e.symm.toEquiv
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' p hdvd
  have h2 := orderOf_dvd_of_pow_eq_one (sq_eq_one_of_psu_four_two h x)
  rw [hx] at h2
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h2)

end Unitary

theorem kFactOutOrthTwoPrime_holds :
    ∀ d : TauCeti.ValidLieTypeIndex, (∃ m : ℕ, ∃ q : TauCeti.PrimePower, q.card = 2 ∧
        (d.1 = .D m q ∨ d.1 = .twistedD m q ∨ (m = 3 ∧ d.1 = .twistedA 3 q))) →
      ∀ p : ℕ, p.Prime → 5 ≤ p → ¬ p ∣ Nat.card (Outer (TauCeti.CFSGIndex.lie d).Group) := by
  rintro ⟨d, hv⟩ ⟨m, q, hq, hd⟩ p hp hp5
  have hq2 : q.p = 2 ∧ q.exponent = 1 := by
    rw [TauCeti.PrimePower.card_def] at hq
    exact Nat.prime_two.pow_eq_iff.mp hq
  rcases hd with rfl | rfl | ⟨rfl, rfl⟩
  · have hmod := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeD m q hv
      (MulEquiv.refl _)
    rw [hq2.1, hq2.2] at hmod
    obtain ⟨a, k, hak, ha0, ha2, hk0, hk3⟩ := exists_card_outer_eq_mul_of_omegaPlus_two hmod
    change ¬ p ∣ Nat.card (Outer (TauCeti.ValidLieTypeIndex.Group ⟨.D m q, hv⟩))
    rw [hak]
    intro hdvd
    rcases (Nat.Prime.dvd_mul hp).mp hdvd with h | h
    · have := Nat.le_of_dvd ha0 h
      omega
    · have := Nat.le_of_dvd hk0 h
      omega
  · have hmod := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeTwistedD m q hv
      (MulEquiv.refl _)
    rw [hq2.1, hq2.2] at hmod
    have h2 := card_outer_le_two_of_omegaMinus_two hmod
    change ¬ p ∣ Nat.card (Outer (TauCeti.ValidLieTypeIndex.Group ⟨.twistedD m q, hv⟩))
    intro hdvd
    have := Nat.le_of_dvd h2.1 hdvd
    omega
  · have hmod := CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA 3 q hv
      (MulEquiv.refl _)
    rw [hq2.1, hq2.2] at hmod
    exact not_dvd_card_outer_of_psu_four_two hmod hp (by omega)

end CFSG.AGLEmbedding
