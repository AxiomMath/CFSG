module

public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalTailModelCoordinates
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalTailRealization
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointPlusNormalizerRealizationModels

public noncomputable section

namespace CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail

open QuadraticMap CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.Spin
  CFSG.ClassicalGroups.Orthogonal
open CFSG.ComponentClassification
open CatalogueBOrthogonalPointAction (Points PointPerp)
open CatalogueBOrthogonalPointData CatalogueBOrthogonalPointIsometry
open CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit (PolarOrtho)
open CatalogueBOrthogonalPointPlusNormalizerRealization
  (orthogonal_geometry_plus_normalizer_realization)

section Coordinate

variable {K : Type} [Field K] {A : Type} [AddCommGroup A] [Module K A] {r : ℕ}
  {qA : QuadraticForm K A} {d : ℕ} {Qc : QuadraticForm K (Fin d → K)}

@[expose] def coordinateSemiSim (iso : (quadTail r qA).IsometryEquiv Qc)
    (T : SemiSim (quadTail r qA) (quadTail r qA)) :
    (Fin d → K) ≃ₛₗ[T.σ.toRingHom] (Fin d → K) where
  toFun v := iso.toLinearEquiv (T.e (iso.toLinearEquiv.symm v))
  invFun v := iso.toLinearEquiv (T.e.symm (iso.toLinearEquiv.symm v))
  map_add' v w := by simp only [map_add, T.map_add']
  map_smul' c v := by
    simp only [map_smul, T.map_smul']
    rfl
  left_inv v := by
    simp only [LinearEquiv.symm_apply_apply, Equiv.symm_apply_apply, LinearEquiv.apply_symm_apply]
  right_inv v := by
    simp only [LinearEquiv.symm_apply_apply, Equiv.apply_symm_apply, LinearEquiv.apply_symm_apply]

theorem coordinateSemiSim_apply (iso : (quadTail r qA).IsometryEquiv Qc)
    (T : SemiSim (quadTail r qA) (quadTail r qA)) (v : Fin d → K) :
    coordinateSemiSim iso T v = iso (T.e (iso.symm v)) :=
  rfl

theorem coordinateSemiSim_similarity (iso : (quadTail r qA).IsometryEquiv Qc)
    (T : SemiSim (quadTail r qA) (quadTail r qA)) (v : Fin d → K) :
    Qc (coordinateSemiSim iso T v) = ((Units.mk0 T.μ T.μ_ne_zero : Kˣ) : K) * T.σ (Qc v) := by
  rw [coordinateSemiSim_apply, iso.map_app, T.map_quad', iso.symm.map_app, Units.val_mk0]

theorem coordinate_point_image_of_tail (iso : (quadTail r qA).IsometryEquiv Qc)
    (T : SemiSim (quadTail r qA) (quadTail r qA)) (phi : Equiv.Perm (Points Qc))
    (hT : ∀ L : Points (quadTail r qA),
      ((pointIsometryEquiv iso).symm (phi (pointIsometryEquiv iso L))).val = T.mapSub L.val)
    (L : Points Qc) : (phi L).val = L.val.map (coordinateSemiSim iso T).toLinearMap := by
  have h := hT ((pointIsometryEquiv iso).symm L)
  rw [Equiv.apply_symm_apply, pointIsometryEquiv_symm_submodule,
    pointIsometryEquiv_symm_submodule] at h
  ext y
  have hy := Submodule.ext_iff.1 h (iso.symm y)
  change iso.symm y ∈ (phi L).val.map iso.symm.toLinearMap ↔
    T.e.symm (iso.symm y) ∈ L.val.map iso.symm.toLinearMap at hy
  rw [Submodule.mem_map_equiv, Submodule.mem_map_equiv] at hy
  change iso (iso.symm y) ∈ (phi L).val ↔ iso (T.e.symm (iso.symm y)) ∈ L.val at hy
  rw [iso.apply_symm_apply] at hy
  rw [hy, Submodule.mem_map_equiv]
  rfl

variable [FiniteDimensional K A]

theorem coordinate_polar_perm_mem_similarityPointImage_of_tail (hr : 3 ≤ r)
    (hani : qA.Anisotropic) (hreg : (polarBilin qA).Nondegenerate)
    (iso : (quadTail r qA).IsometryEquiv Qc) (phi : Equiv.Perm (Points Qc))
    (hphi : ∀ L M, PointPerp (phi L) (phi M) ↔ PointPerp L M) :
    phi ∈ similarityPointImage Qc := by
  let eP := pointIsometryEquiv iso
  let psi : Points (quadTail r qA) ≃ Points (quadTail r qA) := (eP.trans phi).trans eP.symm
  have hpsi : ∀ L M : Points (quadTail r qA),
      PolarOrtho (quadTail r qA) L.val M.val ↔
        PolarOrtho (quadTail r qA) (psi L).val (psi M).val := by
    intro L M
    change PointPerp L M ↔ PointPerp (eP.symm (phi (eP L))) (eP.symm (phi (eP M)))
    exact (pointPerp_isometry_iff iso L M).symm.trans
      ((hphi (eP L) (eP M)).symm.trans
        (pointPerp_isometry_symm_iff iso (phi (eP L)) (phi (eP M))).symm)
  obtain ⟨T, hT⟩ := exists_semiSim_of_polarOrtho hr hani hreg psi hpsi
  exact CatalogueBOrthogonalPointSemilinearRealization.pointPerm_mem_similarityPointImage Qc T.σ
    (coordinateSemiSim iso T) (Units.mk0 T.μ T.μ_ne_zero) (coordinateSemiSim_similarity iso T) phi
    (coordinate_point_image_of_tail iso T phi fun L => hT L)

theorem coordinate_normalizer_eq_of_tail [Finite K] (hr : 3 ≤ r) (hani : qA.Anisotropic)
    (hreg : (polarBilin qA).Nondegenerate) (iso : (quadTail r qA).IsometryEquiv Qc)
    (hQ : Qc.polarBilin.Nondegenerate)
    (hT : ∃ T : Submodule K (Fin d → K), Module.finrank K T = 3 ∧ ∀ x ∈ T, Qc x = 0)
    (ha : CatalogueBOrthogonalPointAction.ActionProperties Qc (projectivePointAction Qc)) :
    projectivePointNormalizer Qc = similarityPointImage Qc := by
  apply le_antisymm
  · intro phi hphi
    have hperp := CatalogueBOrthogonalPointModelNormalizer.action_normalizer_orthogonality Qc
      (projectivePointAction Qc) hQ hT ha phi hphi
    exact coordinate_polar_perm_mem_similarityPointImage_of_tail hr hani hreg iso phi hperp.1
  · exact similarityPointImage_le_normalizer Qc

end Coordinate

theorem orthogonal_geometry_model_normalizer_realization (H : Type) [Group H]
    (t : StatedLieTag) (ht : t = .POmegaOdd ∨ t = .POmegaPlus ∨ t = .POmegaMinus) (n p f : ℕ)
    (h : StatedClassicalModel H t n p f) :
    match t with
    | .POmegaOdd => ∀ (K : Type) [Field K] [Finite K], Nat.card K = p ^ f →
        ∀ e : H ≃* StatedProj (StatedOmega (StatedQuadOdd n K)),
          projectivePointNormalizer (coordinateQuadOdd n K) =
              similarityPointImage (coordinateQuadOdd n K) ∧
            Subgroup.normalizer
                (((projectivePointAction (coordinateQuadOdd n K)).comp
                  (coordinateOddWitnessEquiv K e).toMonoidHom).range :
                    Set (Equiv.Perm (Points (coordinateQuadOdd n K)))) =
              similarityPointImage (coordinateQuadOdd n K)
    | .POmegaPlus => ∀ (K : Type) [Field K] [Finite K], Nat.card K = p ^ f →
        ∀ e : H ≃* StatedProj (StatedOmega (StatedQuadPlus n K)),
          projectivePointNormalizer (coordinateQuadPlus n K) =
              similarityPointImage (coordinateQuadPlus n K) ∧
            Subgroup.normalizer
                (((projectivePointAction (coordinateQuadPlus n K)).comp
                  (coordinatePlusWitnessEquiv K e).toMonoidHom).range :
                    Set (Equiv.Perm (Points (coordinateQuadPlus n K)))) =
              similarityPointImage (coordinateQuadPlus n K)
    | .POmegaMinus => ∀ (hn : 1 ≤ n) (K : Type) [Field K] [Finite K], Nat.card K = p ^ f →
        ∀ b c : K, (∀ s : K, s ^ 2 + b * s + c ≠ 0) →
        ∀ e : H ≃* StatedProj (StatedOmega (StatedQuadMinus n K b c)),
          projectivePointNormalizer (coordinateQuadMinus n K hn b c) =
              similarityPointImage (coordinateQuadMinus n K hn b c) ∧
            Subgroup.normalizer
                (((projectivePointAction (coordinateQuadMinus n K hn b c)).comp
                  (coordinateMinusWitnessEquiv K hn b c e).toMonoidHom).range :
                    Set (Equiv.Perm (Points (coordinateQuadMinus n K hn b c)))) =
              similarityPointImage (coordinateQuadMinus n K hn b c)
    | _ => False := by
  rcases ht with rfl | rfl | rfl
  · obtain ⟨hp, hf, hn, hp2⟩ := h.1
    intro K _ _ hK e
    have hchar := ringChar_eq_of_card_eq hp hf hK
    have h2 : (2 : K) ≠ 0 := by
      rw [Ne, two_eq_zero_iff_ringChar_eq_two (hchar ▸ hp), hchar]
      exact hp2
    have hreg := regular_coordinateQuadOdd n K h2 hn
    have heq := coordinate_normalizer_eq_of_tail hn anisotropic_oddTailForm
      (nondegenerate_oddTailForm h2) ((oddTailIsometry n K).trans (coordinateOddIsometry n K))
      hreg.1 hreg.2 (coordinate_odd_point_action_properties n K h2 hn)
    refine ⟨heq, ?_⟩
    rw [CatalogueBOrthogonalPointModelNormalizer.action_normalizer_comp_equiv]
    exact heq
  · intro K _ _ hK e
    exact orthogonal_geometry_plus_normalizer_realization h K hK e
  · obtain ⟨-, -, hn⟩ := h.1
    intro hn1 K _ _ hK b c hirr e
    have hreg := regular_coordinateQuadMinus n K b c hn hirr
    have heq := coordinate_normalizer_eq_of_tail (by omega : 3 ≤ n - 1)
      (anisotropic_minusTailForm hirr) (nondegenerate_minusTailForm hirr)
      ((minusTailIsometry n K b c).trans (coordinateMinusIsometry n K hn1 b c))
      hreg.1 hreg.2 (coordinate_minus_point_action_properties n K b c hn hirr)
    refine ⟨heq, ?_⟩
    rw [CatalogueBOrthogonalPointModelNormalizer.action_normalizer_comp_equiv]
    exact heq

end CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail
