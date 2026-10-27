module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierLinearTwoCoordinateSemilinear

public section

namespace CFSG.ComponentClassification.CatalogueSchreierLinearTwo

noncomputable section

open CFSG.GorensteinWalter

universe u

theorem coordinateG_normal_in_E (K : Type u) [Field K] [Finite K] :
    ((coordinateG K).subgroupOf (coordinateE K)).Normal := by
  rw [← semilinearPSLRange_map]
  exact (semilinearPSLRange_normal K).map
    (semilinearEquivCoordinateE K).toMonoidHom (semilinearEquivCoordinateE K).surjective

instance coordinateGNormalInE (K : Type u) [Field K] [Finite K] :
    ((coordinateG K).subgroupOf (coordinateE K)).Normal := coordinateG_normal_in_E K

theorem coordinateD_normal_in_E (K : Type u) [Field K] [Finite K] :
    ((coordinateD K).subgroupOf (coordinateE K)).Normal := by
  rw [← semilinearPGLRange_map]
  exact (pGammaL2PGLRange_normal K).map
    (semilinearEquivCoordinateE K).toMonoidHom (semilinearEquivCoordinateE K).surjective

instance coordinateDNormalInE (K : Type u) [Field K] [Finite K] :
    ((coordinateD K).subgroupOf (coordinateE K)).Normal := coordinateD_normal_in_E K

theorem coordinateE_le_normalizer_G (K : Type u) [Field K] [Finite K] :
    coordinateE K ≤ Subgroup.normalizer (coordinateG K : Set (Equiv.Perm (Omega K))) :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer
    ((coordinateG_le_D K).trans (coordinateD_le_E K))).mp (coordinateG_normal_in_E K)

theorem coordinateG_normal_in_D (K : Type u) [Field K] [Finite K] :
    ((coordinateG K).subgroupOf (coordinateD K)).Normal :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer (coordinateG_le_D K)).mpr
    ((coordinateD_le_E K).trans (coordinateE_le_normalizer_G K))

instance coordinateGNormalInD (K : Type u) [Field K] [Finite K] :
    ((coordinateG K).subgroupOf (coordinateD K)).Normal := coordinateG_normal_in_D K

instance pglPSLRangeNormal (K : Type u) [Field K] :
    (Matrix.ProjectiveSpecialLinearGroup.toPGL
      (n := Fin 2) (R := K)).range.Normal := pglPSLRange_normal K

abbrev CoordinateQuotientEG (K : Type u) [Field K] [Finite K] :=
  coordinateE K ⧸ (coordinateG K).subgroupOf (coordinateE K)

abbrev CoordinateQuotientED (K : Type u) [Field K] [Finite K] :=
  coordinateE K ⧸ (coordinateD K).subgroupOf (coordinateE K)

abbrev CoordinateQuotientDG (K : Type u) [Field K] [Finite K] :=
  coordinateD K ⧸ (coordinateG K).subgroupOf (coordinateD K)

@[expose] def semilinearQuotientEquivCoordinateEG (K : Type u) [Field K] [Finite K] :
    SemilinearQuotient K ≃* CoordinateQuotientEG K :=
  QuotientGroup.congr (pGammaL2PSLRange K)
    ((coordinateG K).subgroupOf (coordinateE K))
    (semilinearEquivCoordinateE K) (semilinearPSLRange_map K)

@[expose] def semilinearPGLQuotientEquivField (K : Type u) [Field K] :
    (PGammaL2 K ⧸ pGammaL2PGLRange K) ≃* (K ≃+* K) :=
  (QuotientGroup.quotientMulEquivOfEq
    (show pGammaL2PGLRange K =
      (SemidirectProduct.rightHom : PGammaL2 K →* (K ≃+* K)).ker from
      SemidirectProduct.range_inl_eq_ker_rightHom)).trans
    (QuotientGroup.quotientKerEquivOfSurjective SemidirectProduct.rightHom
      (fun sigma => ⟨SemidirectProduct.inr sigma, by simp⟩))

@[expose] def coordinateEDQuotientEquivField (K : Type u) [Field K] [Finite K] :
    CoordinateQuotientED K ≃* (K ≃+* K) :=
  (QuotientGroup.congr (pGammaL2PGLRange K)
    ((coordinateD K).subgroupOf (coordinateE K))
    (semilinearEquivCoordinateE K) (semilinearPGLRange_map K)).symm.trans
    (semilinearPGLQuotientEquivField K)

theorem coordinateED_isCyclic (K : Type u) [Field K] [Finite K] :
    IsCyclic (CoordinateQuotientED K) :=
  (coordinateEDQuotientEquivField K).isCyclic.mpr (fieldAut_isCyclic K)

theorem pglPSLRange_map_coordinateD (K : Type u) [Field K] [Finite K] :
    (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := K)).range.map
      (pglEquivCoordinateD K).toMonoidHom =
        (coordinateG K).subgroupOf (coordinateD K) := by
  apply Subgroup.map_injective (coordinateD K).subtype_injective
  rw [Subgroup.map_map, Subgroup.subgroupOf_map_subtype]
  rw [show (coordinateD K).subtype.comp (pglEquivCoordinateD K).toMonoidHom =
    coordinatePGLAction K from rfl]
  rw [← MonoidHom.range_comp]
  have hcomp : (coordinatePGLAction K).comp
      Matrix.ProjectiveSpecialLinearGroup.toPGL = coordinatePSLAction K := by
    apply MonoidHom.ext
    intro g
    exact coordinatePGLAction_toPGL K g
  rw [hcomp, coordinatePSLAction_range_eq_G, inf_eq_left.mpr (coordinateG_le_D K)]

@[expose] def pglQuotientEquivCoordinateDG (K : Type u) [Field K] [Finite K] :
    (PGL2 K ⧸ (Matrix.ProjectiveSpecialLinearGroup.toPGL
      (n := Fin 2) (R := K)).range) ≃* CoordinateQuotientDG K :=
  QuotientGroup.congr _ _ (pglEquivCoordinateD K) (pglPSLRange_map_coordinateD K)

theorem pglPSLQuotient_commutator_eq_bot (K : Type u) [Field K] [Finite K] :
    commutator (PGL2 K ⧸ (Matrix.ProjectiveSpecialLinearGroup.toPGL
      (n := Fin 2) (R := K)).range) = ⊥ := by
  let q := QuotientGroup.mk' (Matrix.ProjectiveSpecialLinearGroup.toPGL
    (n := Fin 2) (R := K)).range
  have h : (commutator (PGL2 K)).map q = ⊥ := by
    apply ((commutator (PGL2 K)).map_eq_bot_iff).mpr
    simpa only [q, QuotientGroup.ker_mk'] using pgl2_commutator_le_psl2_range K
  rw [map_commutator_eq, MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective _)] at h
  exact h

theorem coordinateDG_commutator_eq_bot (K : Type u) [Field K] [Finite K] :
    commutator (CoordinateQuotientDG K) = ⊥ := by
  have h := congrArg
    (fun H => H.map (pglQuotientEquivCoordinateDG K).toMonoidHom)
    (pglPSLQuotient_commutator_eq_bot K)
  have hrange : (pglQuotientEquivCoordinateDG K).toMonoidHom.range = ⊤ :=
    MonoidHom.range_eq_top.mpr (pglQuotientEquivCoordinateDG K).surjective
  rw [map_commutator_eq, hrange, Subgroup.map_bot] at h
  exact h

theorem coordinateDG_isMulCommutative (K : Type u) [Field K] [Finite K] :
    IsMulCommutative (CoordinateQuotientDG K) :=
  (commutator_eq_bot_iff _).mp (coordinateDG_commutator_eq_bot K)

theorem coordinateEG_secondDerived_eq_bot (K : Type u) [Field K] [Finite K] :
    derivedSeries (CoordinateQuotientEG K) 2 = ⊥ :=
  secondDerived_eq_bot_of_surjective (semilinearQuotientEquivCoordinateEG K).toMonoidHom
    (semilinearQuotientEquivCoordinateEG K).surjective
    (semilinearQuotient_secondDerived_eq_bot K)

theorem coordinateEG_solvable (K : Type u) [Field K] [Finite K] :
    Group.IsSolvable (CoordinateQuotientEG K) :=
  ⟨⟨2, coordinateEG_secondDerived_eq_bot K⟩⟩

end

end CFSG.ComponentClassification.CatalogueSchreierLinearTwo
