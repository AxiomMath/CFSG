module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBLinearTwoFixedSquares
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierLinearTwoCoordinateSemilinear
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierLinearTwoProjectiveFormulas
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBLinearTwoFixedProjective

public section

namespace CFSG.ComponentClassification.CatalogueBLinearTwoFixed

noncomputable section

open Matrix CFSG.GorensteinWalter CFSG.ComponentClassification.CatalogueSchreierLinearTwo

universe u

@[expose] def subfieldCoordinateMap (K : Type u) [Field K] [Finite K] (S : Subfield K) :
    coordinateD S →* coordinateD K :=
  (pglEquivCoordinateD K).toMonoidHom.comp
    ((subfieldPGLMap K S).comp (pglEquivCoordinateD S).symm.toMonoidHom)

theorem subfieldCoordinateMap_injective (K : Type u) [Field K] [Finite K] (S : Subfield K) :
    Function.Injective (subfieldCoordinateMap K S) :=
  (pglEquivCoordinateD K).injective.comp
    ((subfieldPGLMap_injective K S).comp (pglEquivCoordinateD S).symm.injective)

theorem subfieldCoordinateMap_pgl (K : Type u) [Field K] [Finite K] (S : Subfield K)
    (g : PGL2 S) :
    ((subfieldCoordinateMap K S (pglEquivCoordinateD S g) : coordinateD K) :
      Equiv.Perm (Omega K)) = coordinatePGLAction K (subfieldPGLMap K S g) := by
  change coordinatePGLAction K
    (subfieldPGLMap K S ((pglEquivCoordinateD S).symm (pglEquivCoordinateD S g))) = _
  rw [MulEquiv.symm_apply_apply]

theorem subfieldCoordinateMap_GL (K : Type u) [Field K] [Finite K] (S : Subfield K)
    (A : GL (Fin 2) S) :
    ((subfieldCoordinateMap K S (pglEquivCoordinateD S (Matrix.ProjGenLinGroup.mk A)) :
      coordinateD K) : Equiv.Perm (Omega K)) =
      coordinateGLAction K (Matrix.GeneralLinearGroup.map S.subtype A) := by
  rw [subfieldCoordinateMap_pgl]
  rfl

@[expose] def subfieldCoordinateImage (K : Type u) [Field K] [Finite K] (S : Subfield K) :
    Subgroup (Equiv.Perm (Omega K)) :=
  ((coordinateD K).subtype.comp (subfieldCoordinateMap K S)).range

theorem mem_subfieldCoordinateImage_iff (K : Type u) [Field K] [Finite K]
    (S : Subfield K) (g : Equiv.Perm (Omega K)) :
    g ∈ subfieldCoordinateImage K S ↔
      ∃ A : GL (Fin 2) S,
        coordinateGLAction K (Matrix.GeneralLinearGroup.map S.subtype A) = g := by
  constructor
  · rintro ⟨d, hd⟩
    obtain ⟨a, rfl⟩ := (pglEquivCoordinateD S).surjective d
    obtain ⟨A, rfl⟩ := Matrix.ProjGenLinGroup.mk_surjective a
    exact ⟨A, (subfieldCoordinateMap_GL K S A).symm.trans hd⟩
  · rintro ⟨A, rfl⟩
    exact ⟨pglEquivCoordinateD S (Matrix.ProjGenLinGroup.mk A),
      subfieldCoordinateMap_GL K S A⟩

theorem coordinatePGLAction_field_conjugation (K : Type u) [Field K] [Finite K]
    (sigma : K ≃+* K) (g : PGL2 K) :
    coordinatePGLAction K (pgl2FieldAut K sigma g) =
      fieldExtension K sigma * coordinatePGLAction K g * (fieldExtension K sigma)⁻¹ := by
  have h := congrArg (coordinateSemilinearAction K)
    (SemidirectProduct.inl_aut (φ := pgl2FieldAut K) sigma g)
  simpa only [map_mul, map_inv, coordinateSemilinearAction_inl,
    coordinateSemilinearAction_inr] using h

theorem coordinatePGLAction_mem_field_centralizer_iff (K : Type u) [Field K] [Finite K]
    (sigma : K ≃+* K) (g : PGL2 K) :
    coordinatePGLAction K g ∈ Subgroup.centralizer {fieldExtension K sigma} ↔
      pgl2FieldAut K sigma g = g := by
  rw [Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    apply coordinatePGLAction_injective K
    rw [coordinatePGLAction_field_conjugation, ← h]
    group
  · intro h
    have hc := coordinatePGLAction_field_conjugation K sigma g
    rw [h] at hc
    have hm := congrArg (fun a : Equiv.Perm (Omega K) => a * fieldExtension K sigma) hc
    simpa only [mul_assoc, inv_mul_cancel, mul_one] using hm

theorem subfieldCoordinateImage_eq_D_centralizer (K : Type u) [Field K] [Finite K]
    (sigma : K ≃+* K) (hsigma : orderOf sigma = 2) :
    subfieldCoordinateImage K (fixedField K sigma) =
      coordinateD K ⊓ Subgroup.centralizer {fieldExtension K sigma} := by
  apply le_antisymm
  · intro g hg
    obtain ⟨A, rfl⟩ := (mem_subfieldCoordinateImage_iff K (fixedField K sigma) g).mp hg
    refine ⟨?_, ?_⟩
    · rw [← coordinatePGLAction_range_eq_D]
      exact ⟨_, rfl⟩
    · apply (coordinatePGLAction_mem_field_centralizer_iff K sigma _).mpr
      apply (pgl_fixed_iff_mem_subfield_range K sigma hsigma _).mpr
      exact ⟨Matrix.ProjGenLinGroup.mk A, rfl⟩
  · rintro g ⟨hgD, hgc⟩
    rw [← coordinatePGLAction_range_eq_D] at hgD
    obtain ⟨a, rfl⟩ := hgD
    have ha := (coordinatePGLAction_mem_field_centralizer_iff K sigma a).mp hgc
    obtain ⟨b, hb⟩ := (pgl_fixed_iff_mem_subfield_range K sigma hsigma a).mp ha
    obtain ⟨B, rfl⟩ := Matrix.ProjGenLinGroup.mk_surjective b
    apply (mem_subfieldCoordinateImage_iff K (fixedField K sigma) _).mpr
    exact ⟨B, congrArg (coordinatePGLAction K) hb⟩

theorem subfieldCoordinateImage_le_G (K : Type u) [Field K] [Finite K]
    (hodd : ringChar K ≠ 2) (sigma : K ≃+* K) (hsigma : orderOf sigma = 2) :
    subfieldCoordinateImage K (fixedField K sigma) ≤ coordinateG K := by
  intro g hg
  obtain ⟨A, rfl⟩ := (mem_subfieldCoordinateImage_iff K (fixedField K sigma) g).mp hg
  obtain ⟨b, hb⟩ := fixedField_projectivity_mem_PSL K hodd sigma hsigma A
  change coordinatePGLAction K
    (Matrix.ProjGenLinGroup.mk (Matrix.GeneralLinearGroup.map (fixedField K sigma).subtype A)) ∈ _
  rw [← hb, coordinatePGLAction_toPGL, ← coordinatePSLAction_range_eq_G]
  exact ⟨b, rfl⟩

theorem subfieldCoordinateImage_eq_G_centralizer (K : Type u) [Field K] [Finite K]
    (hodd : ringChar K ≠ 2) (sigma : K ≃+* K) (hsigma : orderOf sigma = 2) :
    subfieldCoordinateImage K (fixedField K sigma) =
      coordinateG K ⊓ Subgroup.centralizer {fieldExtension K sigma} := by
  have hD := subfieldCoordinateImage_eq_D_centralizer K sigma hsigma
  apply le_antisymm
  · intro g hg
    exact ⟨subfieldCoordinateImage_le_G K hodd sigma hsigma hg, (hD.le hg).2⟩
  · rintro g ⟨hg, hc⟩
    apply hD.ge
    exact ⟨coordinateG_le_D K hg, hc⟩

@[expose] def subfieldCoordinateEquivImage (K : Type u) [Field K] [Finite K]
    (S : Subfield K) : coordinateD S ≃* subfieldCoordinateImage K S :=
  MulEquiv.ofBijective
    ((coordinateD K).subtype.comp (subfieldCoordinateMap K S)).rangeRestrict
    ⟨by
      intro x y h
      apply subfieldCoordinateMap_injective K S
      apply Subtype.ext
      exact congrArg
        (fun a : subfieldCoordinateImage K S => (a : Equiv.Perm (Omega K))) h,
      ((coordinateD K).subtype.comp (subfieldCoordinateMap K S)).rangeRestrict_surjective⟩

theorem subfieldCoordinateEquivImage_coe (K : Type u) [Field K] [Finite K]
    (S : Subfield K) (g : coordinateD S) :
    ((subfieldCoordinateEquivImage K S g : subfieldCoordinateImage K S) :
      Equiv.Perm (Omega K)) = (subfieldCoordinateMap K S g : Equiv.Perm (Omega K)) := rfl

@[expose] def subfieldCoordinateEquivDCentralizer (K : Type u) [Field K] [Finite K]
    (sigma : K ≃+* K) (hsigma : orderOf sigma = 2) :
    coordinateD (fixedField K sigma) ≃*
      ↥(coordinateD K ⊓ Subgroup.centralizer {fieldExtension K sigma}) :=
  (subfieldCoordinateEquivImage K (fixedField K sigma)).trans
    (MulEquiv.subgroupCongr (subfieldCoordinateImage_eq_D_centralizer K sigma hsigma))

@[expose] def subfieldCoordinateEquivGCentralizer (K : Type u) [Field K] [Finite K]
    (hodd : ringChar K ≠ 2) (sigma : K ≃+* K) (hsigma : orderOf sigma = 2) :
    coordinateD (fixedField K sigma) ≃*
      ↥(coordinateG K ⊓ Subgroup.centralizer {fieldExtension K sigma}) :=
  (subfieldCoordinateEquivImage K (fixedField K sigma)).trans
    (MulEquiv.subgroupCongr (subfieldCoordinateImage_eq_G_centralizer K hodd sigma hsigma))

theorem subfieldCoordinateEquivGCentralizer_coe (K : Type u) [Field K] [Finite K]
    (hodd : ringChar K ≠ 2) (sigma : K ≃+* K) (hsigma : orderOf sigma = 2)
    (g : coordinateD (fixedField K sigma)) :
    ((subfieldCoordinateEquivGCentralizer K hodd sigma hsigma g :
      ↥(coordinateG K ⊓ Subgroup.centralizer {fieldExtension K sigma})) :
      Equiv.Perm (Omega K)) =
        (subfieldCoordinateMap K (fixedField K sigma) g : Equiv.Perm (Omega K)) := rfl

theorem quadratic_field_fixed_projective_group (K : Type u) [Field K] [Finite K]
    (hodd : ringChar K ≠ 2) (sigma : K ≃+* K) (hsigma : orderOf sigma = 2) :
    Nat.card K = Nat.card (fixedField K sigma) ^ 2 ∧
      Function.Injective (subfieldCoordinateMap K (fixedField K sigma)) ∧
      (∀ A : GL (Fin 2) (fixedField K sigma),
        ((subfieldCoordinateMap K (fixedField K sigma)
          (pglEquivCoordinateD (fixedField K sigma) (Matrix.ProjGenLinGroup.mk A)) :
          coordinateD K) : Equiv.Perm (Omega K)) =
          coordinateGLAction K (Matrix.GeneralLinearGroup.map (fixedField K sigma).subtype A)) ∧
      subfieldCoordinateImage K (fixedField K sigma) =
        coordinateD K ⊓ Subgroup.centralizer {fieldExtension K sigma} ∧
      subfieldCoordinateImage K (fixedField K sigma) =
        coordinateG K ⊓ Subgroup.centralizer {fieldExtension K sigma} ∧
      subfieldCoordinateImage K (fixedField K sigma) ≤ coordinateG K ∧
      Nonempty (coordinateD (fixedField K sigma) ≃*
        ↥(coordinateG K ⊓ Subgroup.centralizer {fieldExtension K sigma})) := by
  exact ⟨card_eq_fixedField_card_sq K sigma hsigma,
    subfieldCoordinateMap_injective K (fixedField K sigma),
    subfieldCoordinateMap_GL K (fixedField K sigma),
    subfieldCoordinateImage_eq_D_centralizer K sigma hsigma,
    subfieldCoordinateImage_eq_G_centralizer K hodd sigma hsigma,
    subfieldCoordinateImage_le_G K hodd sigma hsigma,
    ⟨subfieldCoordinateEquivGCentralizer K hodd sigma hsigma⟩⟩

end

end CFSG.ComponentClassification.CatalogueBLinearTwoFixed
