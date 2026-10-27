module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHigherLinearFieldProjectiveComponents

public section

namespace CFSG.ComponentClassification.CatalogueBHigherLinearField

noncomputable section

open Matrix CatalogueBHigherLinearAction

universe u

@[expose] def fixedPSLToFixedPGL (n : ℕ) (K : Type u) [Field K] (sigma : K ≃+* K) :
    fixedPSL n K sigma →* fixedPGL (Fin n) K sigma :=
  (fixedT n K sigma).subtype.comp (fixedPSLEquivT n K sigma).toMonoidHom

theorem fixedPSLToFixedPGL_val (n : ℕ) (K : Type u) [Field K] (sigma : K ≃+* K)
    (x : fixedPSL n K sigma) :
    (fixedPSLToFixedPGL n K sigma x).val = ProjectiveSpecialLinearGroup.toPGL x.val := rfl

theorem fixedPSLToFixedPGL_injective (n : ℕ) (K : Type u) [Field K] (sigma : K ≃+* K) :
    Function.Injective (fixedPSLToFixedPGL n K sigma) :=
  (fixedT n K sigma).subtype_injective.comp (fixedPSLEquivT n K sigma).injective

theorem pComponent_fixedPSLToFixedPGL (n : ℕ) (K : Type u) [Field K] [Finite K]
    (sigma : K ≃+* K) (p : ℕ) [Fact p.Prime] (L : Subgroup (fixedPSL n K sigma))
    (hL : CFSG.IsPComponent p L) :
    CFSG.IsPComponent p (L.map (fixedPSLToFixedPGL n K sigma)) := by
  have h := pComponent_fixed_extend n K sigma p L hL
  rw [Subgroup.map_map] at h
  exact h

abbrev fixedComponentSubfieldImage (n : ℕ) [NeZero n] (K : Type u) [Field K]
    (sigma : K ≃+* K) (L : Subgroup (fixedPSL n K sigma)) :
    Subgroup (ProjGenLinGroup (Fin n) (fixedField K sigma)) :=
  (L.map (fixedPSLToFixedPGL n K sigma)).map
    (subfieldPGLEquivFixed (Fin n) K sigma).symm.toMonoidHom

theorem pComponent_fixedComponentSubfieldImage
    (n : ℕ) [NeZero n] (K : Type u) [Field K] [Finite K]
    (sigma : K ≃+* K) (p : ℕ) [Fact p.Prime] (L : Subgroup (fixedPSL n K sigma))
    (hL : CFSG.IsPComponent p L) :
    CFSG.IsPComponent p (fixedComponentSubfieldImage n K sigma L) :=
  CatalogueBAlternating.pComponent_map_equiv p
    (subfieldPGLEquivFixed (Fin n) K sigma).symm
    (L.map (fixedPSLToFixedPGL n K sigma))
    (pComponent_fixedPSLToFixedPGL n K sigma p L hL)

@[expose] def fixedComponentEquivSubfieldImage
    (n : ℕ) [NeZero n] (K : Type u) [Field K] (sigma : K ≃+* K)
    (L : Subgroup (fixedPSL n K sigma)) :
    L ≃* fixedComponentSubfieldImage n K sigma L :=
  (L.equivMapOfInjective (fixedPSLToFixedPGL n K sigma)
    (fixedPSLToFixedPGL_injective n K sigma)).trans
      ((subfieldPGLEquivFixed (Fin n) K sigma).symm.subgroupMap
        (L.map (fixedPSLToFixedPGL n K sigma)))

theorem fixedComponentEquivSubfieldImage_toPGL
    (n : ℕ) [NeZero n] (K : Type u) [Field K] (sigma : K ≃+* K)
    (L : Subgroup (fixedPSL n K sigma)) (x : L) :
    subfieldPGLMap (Fin n) K (fixedField K sigma)
      (fixedComponentEquivSubfieldImage n K sigma L x).val =
        ProjectiveSpecialLinearGroup.toPGL x.val.val := by
  let e := subfieldPGLEquivFixed (Fin n) K sigma
  change subfieldPGLMap (Fin n) K (fixedField K sigma)
    (e.symm (fixedPSLToFixedPGL n K sigma x.val)) = _
  rw [← subfieldPGLEquivFixed_val]
  exact congrArg Subtype.val (e.apply_symm_apply (fixedPSLToFixedPGL n K sigma x.val))

theorem field_fixed_pComponent_quasisimple
    (n : ℕ) [NeZero n] (K : Type u) [Field K] [Finite K] (hn : 1 ≤ n)
    (sigma : K ≃+* K) (p : ℕ) [Fact p.Prime]
    (L : Subgroup (fixedPSL n K sigma)) (hL : CFSG.IsPComponent p L) :
    CFSG.IsQuasisimple L := by
  have hM := pComponent_fixedComponentSubfieldImage n K sigma p L hL
  have hquasi := (projective_pComponent_classification n (fixedField K sigma) hn p
    (fixedComponentSubfieldImage n K sigma L) hM).2.2.2.2
  exact CatalogueBAlternating.quasisimple_iff_native.mpr
    (Components.quasisimple_of_equiv (fixedComponentEquivSubfieldImage n K sigma L)
      (CatalogueBAlternating.quasisimple_iff_native.mp hquasi))

@[expose] def fieldFixedPComponentEquivPSL
    (n : ℕ) [NeZero n] (K : Type u) [Field K] [Finite K] (hn : 1 ≤ n)
    (sigma : K ≃+* K) (p : ℕ) [Fact p.Prime]
    (L : Subgroup (fixedPSL n K sigma)) (hL : CFSG.IsPComponent p L) :
    L ≃* ProjectiveSpecialLinearGroup (Fin n) (fixedField K sigma) :=
  (fixedComponentEquivSubfieldImage n K sigma L).trans
    (projectivePComponentEquivPSL n (fixedField K sigma) hn p
      (fixedComponentSubfieldImage n K sigma L)
      (pComponent_fixedComponentSubfieldImage n K sigma p L hL))

theorem fieldFixedPComponentEquivPSL_toPGL
    (n : ℕ) [NeZero n] (K : Type u) [Field K] [Finite K] (hn : 1 ≤ n)
    (sigma : K ≃+* K) (p : ℕ) [Fact p.Prime]
    (L : Subgroup (fixedPSL n K sigma)) (hL : CFSG.IsPComponent p L) (x : L) :
    subfieldPGLMap (Fin n) K (fixedField K sigma)
      (ProjectiveSpecialLinearGroup.toPGL (fieldFixedPComponentEquivPSL n K hn sigma p L hL x)) =
        ProjectiveSpecialLinearGroup.toPGL x.val.val := by
  change subfieldPGLMap (Fin n) K (fixedField K sigma)
    (ProjectiveSpecialLinearGroup.toPGL (projectivePComponentEquivPSL n (fixedField K sigma) hn p
      (fixedComponentSubfieldImage n K sigma L)
      (pComponent_fixedComponentSubfieldImage n K sigma p L hL)
      (fixedComponentEquivSubfieldImage n K sigma L x))) = _
  rw [projectivePComponentEquivPSL_toPGL]
  exact fixedComponentEquivSubfieldImage_toPGL n K sigma L x

theorem field_fixed_small_no_pComponent (K : Type u) [Field K] [Finite K]
    (sigma : K ≃+* K)
    (hsmall : Nat.card (fixedField K sigma) = 2 ∨ Nat.card (fixedField K sigma) = 3)
    (p : ℕ) [Fact p.Prime] (L : Subgroup (fixedPSL 2 K sigma)) :
    ¬ CFSG.IsPComponent p L := by
  intro hL
  exact projective_small_no_pComponent (fixedField K sigma) hsmall p
    (fixedComponentSubfieldImage 2 K sigma L)
    (pComponent_fixedComponentSubfieldImage 2 K sigma p L hL)

theorem linear_field_involution_fixed_p_components
    (n : ℕ) (hn : 2 ≤ n) (K : Type u) [Field K] [Finite K]
    (sigma : K ≃+* K) (hsigma : sigma ^ 2 = 1) (hne : sigma ≠ 1) :
    Nat.card K = Nat.card (fixedField K sigma) ^ 2 ∧
      (∀ (p : ℕ), p.Prime → ∀ L : Subgroup (fixedPSL n K sigma),
        CFSG.IsPComponent p L → CFSG.IsQuasisimple L) ∧
      (n = 2 ∧ (Nat.card (fixedField K sigma) = 2 ∨ Nat.card (fixedField K sigma) = 3) →
        ∀ (p : ℕ), p.Prime → ∀ L : Subgroup (fixedPSL n K sigma), ¬ CFSG.IsPComponent p L) ∧
      (¬ (n = 2 ∧ (Nat.card (fixedField K sigma) = 2 ∨ Nat.card (fixedField K sigma) = 3)) →
        ∀ (p : ℕ), p.Prime → ∀ L : Subgroup (fixedPSL n K sigma),
          CFSG.IsPComponent p L →
            Nonempty (L ≃* ProjectiveSpecialLinearGroup (Fin n) (fixedField K sigma))) := by
  let : NeZero n := ⟨by omega⟩
  refine ⟨fixedField_card_square K sigma hsigma hne, ?_, ?_, ?_⟩
  · intro p hp L hL
    let : Fact p.Prime := ⟨hp⟩
    exact field_fixed_pComponent_quasisimple n K (by omega) sigma p L hL
  · rintro ⟨rfl, hsmall⟩ p hp L
    let : Fact p.Prime := ⟨hp⟩
    exact field_fixed_small_no_pComponent K sigma hsmall p L
  · intro _ p hp L hL
    let : Fact p.Prime := ⟨hp⟩
    exact ⟨fieldFixedPComponentEquivPSL n K (by omega) sigma p L hL⟩

end

end CFSG.ComponentClassification.CatalogueBHigherLinearField
