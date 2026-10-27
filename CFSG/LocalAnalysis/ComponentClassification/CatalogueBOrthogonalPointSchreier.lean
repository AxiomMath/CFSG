module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointPlusSchreier
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointDataModelImage
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalTailModelFamily

public noncomputable section

namespace CFSG.ComponentClassification.CatalogueBOrthogonalPointSchreier

open CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.Spin
open CatalogueBOrthogonalSmallFamilyOrbit CatalogueBStabilizerFamily
open CatalogueBOrthogonalPointPlusFamilyOrbit
open CatalogueBOrthogonalPointAction (Points)
open CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail
  (orthogonal_geometry_tail_model_point_family_invariant)
open scoped Pointwise

variable {G : Type} [Group G]

theorem points_nonempty {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V]
    (Q : QuadraticForm K V) {T : Submodule K V} (hT : 0 < Module.finrank K T)
    (hTs : ∀ x ∈ T, Q x = 0) : Nonempty (Points Q) := by
  have hne : T ≠ ⊥ := by
    rintro rfl
    simp at hT
  obtain ⟨v, hvT, hv⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  exact ⟨⟨K ∙ v, finrank_span_singleton hv, fun x hx => hTs x
    ((Submodule.span_le.mpr (Set.singleton_subset_iff.mpr hvT)) hx)⟩⟩

theorem familyAut_witness_eq_top {K : Type} [Field K] {d : ℕ}
    (Q : QuadraticForm K (Fin d → K))
    (psi : G ≃* CatalogueBOrthogonalSemilinear.matrixProjectiveDerived Q)
    (htop : CatalogueBOrthogonalPointData.projectivePointFamilyAut Q = ⊤) :
    familyAut ((CatalogueBOrthogonalPointData.projectivePointAction Q).comp psi.toMonoidHom) =
      ⊤ := by
  refine eq_top_iff.mpr fun alpha _ => ?_
  change alpha • family ((CatalogueBOrthogonalPointData.projectivePointAction Q).comp
    psi.toMonoidHom) = _
  apply (familyTransport psi).injective
  rw [familyTransport_automorphism, pointFamily_comp_equiv_transport]
  have hmem : MulAut.congr psi alpha ∈
      CatalogueBOrthogonalPointData.projectivePointFamilyAut Q := by
    rw [htop]
    exact Subgroup.mem_top _
  exact hmem

theorem outer_thirdDerived_of_witness [Finite G] {K : Type} [Field K] {d : ℕ}
    (Q : QuadraticForm K (Fin d → K))
    (psi : G ≃* CatalogueBOrthogonalSemilinear.matrixProjectiveDerived Q)
    (hG : CatalogueBOrthogonalPointData.IntrinsicPointAction Q
      ((CatalogueBOrthogonalPointData.projectivePointAction Q).comp psi.toMonoidHom))
    (x : Points Q)
    (hd : derivedSeries (familyOuter
      ((CatalogueBOrthogonalPointData.projectivePointAction Q).comp psi.toMonoidHom)) 3 = ⊥)
    (htop : CatalogueBOrthogonalPointData.projectivePointFamilyAut Q = ⊤) :
    derivedSeries (OuterAutomorphisms.Outer G) 3 = ⊥ :=
  CatalogueBOrthogonalPointData.outer_derived_eq_bot_of_point_family_top _ x (hG.2.2 x).1 3 hd
    (familyAut_witness_eq_top Q psi htop)

theorem orthogonal_geometry_tail_classical_model_Schreier (t : StatedLieTag)
    (ht : t = .POmegaOdd ∨ t = .POmegaMinus) {n p f : ℕ}
    (h : StatedClassicalModel G t n p f) :
    derivedSeries (OuterAutomorphisms.Outer G) 3 = ⊥ := by
  rcases ht with rfl | rfl
  · obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := id h
    have : Finite G := Finite.of_equiv _ e.symm.toEquiv
    obtain ⟨-, -, ⟨T, hT3, hTs⟩, -⟩ :=
      CatalogueBOrthogonalPointData.coordinate_model_witness_odd h K hK e
    obtain ⟨x⟩ := points_nonempty _ (by omega : 0 < Module.finrank K T) hTs
    have hG := (CatalogueBOrthogonalPointData.coordinate_model_intrinsic_odd h K hK e).2.2
    have hd : derivedSeries (familyOuter
        ((CatalogueBOrthogonalPointData.projectivePointAction
          (CatalogueBOrthogonalPointData.coordinateQuadOdd n K)).comp
          (CatalogueBOrthogonalPointData.coordinateOddWitnessEquiv K e).toMonoidHom)) 3 = ⊥ := by
      have he := map_derivedSeries_eq
        (f := (CatalogueBOrthogonalPointData.coordinate_odd_familyOuter_witness_equiv h K hK
          e).symm.toMonoidHom)
        (CatalogueBOrthogonalPointData.coordinate_odd_familyOuter_witness_equiv h K hK
          e).symm.surjective 3
      rw [CatalogueBOrthogonalPointData.coordinate_odd_familyOuter_thirdDerived h K hK e,
        Subgroup.map_bot] at he
      exact he.symm
    have htop := (orthogonal_geometry_tail_model_point_family_invariant G .POmegaOdd (.inl rfl)
      n p f h K hK).2
    exact outer_thirdDerived_of_witness _ _ hG x hd htop
  · obtain ⟨-, K, _, _, hK, b, c, hirr, ⟨e⟩⟩ := id h
    have : Finite G := Finite.of_equiv _ e.symm.toEquiv
    have hn : 1 ≤ n := by have := h.1.2.2; omega
    obtain ⟨-, -, ⟨T, hT3, hTs⟩, -⟩ :=
      CatalogueBOrthogonalPointData.coordinate_model_witness_minus h K hK b c hirr e
    obtain ⟨x⟩ := points_nonempty _ (by omega : 0 < Module.finrank K T) hTs
    have hG := (CatalogueBOrthogonalPointData.coordinate_model_intrinsic_minus h K hK b c hirr
      e).2.2
    have hd : derivedSeries (familyOuter
        ((CatalogueBOrthogonalPointData.projectivePointAction
          (CatalogueBOrthogonalPointData.coordinateQuadMinus n K hn b c)).comp
          (CatalogueBOrthogonalPointData.coordinateMinusWitnessEquiv K hn b c e).toMonoidHom))
        3 = ⊥ := by
      have he := map_derivedSeries_eq
        (f := (CatalogueBOrthogonalPointData.coordinate_minus_familyOuter_witness_equiv h K hK
          b c hirr e).symm.toMonoidHom)
        (CatalogueBOrthogonalPointData.coordinate_minus_familyOuter_witness_equiv h K hK
          b c hirr e).symm.surjective 3
      rw [CatalogueBOrthogonalPointData.coordinate_minus_familyOuter_thirdDerived h hn K hK b c
        hirr e, Subgroup.map_bot] at he
      exact he.symm
    have htop := (orthogonal_geometry_tail_model_point_family_invariant G .POmegaMinus
      (.inr rfl) n p f h hn K hK b c hirr).2
    exact outer_thirdDerived_of_witness _ _ hG x hd htop

theorem orthogonal_geometry_classical_model_Schreier (t : StatedLieTag)
    (ht : t = .POmegaOdd ∨ t = .POmegaPlus ∨ t = .POmegaMinus) {n p f : ℕ}
    (h : StatedClassicalModel G t n p f) :
    derivedSeries (OuterAutomorphisms.Outer G) 5 = ⊥ ∧
      (¬ (t = .POmegaPlus ∧ n = 4) → derivedSeries (OuterAutomorphisms.Outer G) 3 = ⊥) ∧
      Group.IsSolvable (OuterAutomorphisms.Outer G) := by
  have h3 : ¬ (t = .POmegaPlus ∧ n = 4) → derivedSeries (OuterAutomorphisms.Outer G) 3 = ⊥ := by
    intro hne
    rcases ht with rfl | rfl | rfl
    · exact orthogonal_geometry_tail_classical_model_Schreier .POmegaOdd (.inl rfl) h
    · have hn : 4 ≤ n := h.1.2.2
      exact (orthogonal_geometry_plus_classical_model_Schreier h).1
        (by by_contra hlt; exact hne ⟨rfl, by omega⟩)
    · exact orthogonal_geometry_tail_classical_model_Schreier .POmegaMinus (.inr rfl) h
  have h5 : derivedSeries (OuterAutomorphisms.Outer G) 5 = ⊥ := by
    by_cases hpl : t = .POmegaPlus ∧ n = 4
    · obtain ⟨rfl, hn4⟩ := hpl
      exact (orthogonal_geometry_plus_classical_model_Schreier h).2.1 hn4
    · exact eq_bot_iff.mpr ((derivedSeries_antitone (G := OuterAutomorphisms.Outer G)
        (by omega : 3 ≤ 5)).trans (h3 hpl).le)
  exact ⟨h5, h3, ⟨⟨5, h5⟩⟩⟩

end CFSG.ComponentClassification.CatalogueBOrthogonalPointSchreier
