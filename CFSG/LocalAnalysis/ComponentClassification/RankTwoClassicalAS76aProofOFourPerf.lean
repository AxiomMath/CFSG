module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofOFour
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFourSplitNormal

public section

namespace CFSG.ComponentClassification.RankTwoClassical

open Matrix CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.CatalogueBOrthogonalFourSplit
open scoped commutatorElement

section Determinant

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem exists_unit_sq_charTwo (δ : Kˣ) : ∃ c : Kˣ, c ^ 2 = δ := by
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨r, hr⟩ := FiniteField.isSquare_of_char_two (ringChar.eq K 2) (δ : K)
  have hr0 : r ≠ 0 := by
    rintro rfl
    simp at hr
  exact ⟨Units.mk0 r hr0, Units.ext (by simp [hr, sq])⟩

theorem rho_mem_specialImage_charTwo (z : equalDeterminants K) : rho z ∈ specialImage K := by
  obtain ⟨c, hc⟩ := exists_unit_sq_charTwo (commonDeterminant z)⁻¹
  have hdet : ∀ c : Kˣ, commonDeterminant (scalarPair c) = c ^ 2 := fun c => by
    apply Units.ext
    simp [commonDeterminant, scalarPair, Matrix.GeneralLinearGroup.det, sq]
  have h1 : commonDeterminant (z * scalarPair c) = 1 := by
    rw [map_mul, hdet, hc, mul_inv_cancel]
  have h2 := rho_mem_specialImage_of_commonDeterminant _ h1
  rwa [map_mul, rho_scalarPair, mul_one] at h2

theorem mem_specialImage_or_mul_tau_charTwo (g : DeterminantIsometries K) :
    g ∈ specialImage K ∨ g * tau ∈ specialImage K := by
  obtain ⟨z, rfl | rfl⟩ := determinant_isometry_exhaustion g
  · exact Or.inl (rho_mem_specialImage_charTwo z)
  · right
    rw [mul_assoc, tau_mul_tau, mul_one]
    exact rho_mem_specialImage_charTwo z

theorem commutator_mem_specialImage_charTwo (g h : DeterminantIsometries K) :
    ⁅g, h⁆ ∈ specialImage K := by
  have hN : (specialImage K).Normal := inferInstance
  rcases mem_specialImage_or_mul_tau_charTwo g with hg | hg
  · have e : ⁅g, h⁆ = g * (h * g⁻¹ * h⁻¹) := by group
    rw [e]
    exact (specialImage K).mul_mem hg (hN.conj_mem g⁻¹ ((specialImage K).inv_mem hg) h)
  rcases mem_specialImage_or_mul_tau_charTwo h with hh | hh
  · have e : ⁅g, h⁆ = (g * h * g⁻¹) * h⁻¹ := by group
    rw [e]
    exact (specialImage K).mul_mem (hN.conj_mem h hh g) ((specialImage K).inv_mem hh)
  · have e : ⁅g, h⁆ = (g * tau) * (tau⁻¹ * ((h * tau) * (g * tau)⁻¹) * tau⁻¹⁻¹) *
        (h * tau)⁻¹ := by group
    rw [e]
    exact (specialImage K).mul_mem ((specialImage K).mul_mem hg
      (hN.conj_mem _ ((specialImage K).mul_mem hh ((specialImage K).inv_mem hg)) tau⁻¹))
      ((specialImage K).inv_mem hh)

end Determinant

section Perfect

variable {K : Type} [Field K]

variable (K) in
@[expose] noncomputable def oPhi :
    GL (Fin 2 ⊕ Fin 2) K ≃* (Matrix (Fin 2) (Fin 2) K ≃ₗ[K] Matrix (Fin 2) (Fin 2) K) :=
  Matrix.GeneralLinearGroup.toLin.trans
    ((LinearMap.GeneralLinearGroup.congrLinearEquiv (oMat K)).trans
      (LinearMap.GeneralLinearGroup.generalLinearEquiv K _))

theorem oPhi_apply (A : GL (Fin 2 ⊕ Fin 2) K) (X : Matrix (Fin 2) (Fin 2) K) :
    oPhi K A X = oMat K ((A : Matrix _ _ K) *ᵥ (oMat K).symm X) := rfl

theorem map_statedOmega_oPhi :
    (StatedOmega (StatedQuadPlus 2 K)).map (oPhi K).toMonoidHom =
      ⁅DeterminantIsometries K, DeterminantIsometries K⁆ := by
  have hset : {A : GL (Fin 2 ⊕ Fin 2) K | ∀ v, StatedQuadPlus 2 K ((A : Matrix _ _ K) *ᵥ v) =
      StatedQuadPlus 2 K v} =
      (((DeterminantIsometries K).comap (oPhi K).toMonoidHom : Subgroup _) : Set _) := by
    ext A
    simp only [Set.mem_ofPred_eq, SetLike.mem_coe, Subgroup.mem_comap,
      TauCeti.QuadraticMap.mem_orthogonalGroup_iff, MulEquiv.coe_toMonoidHom]
    constructor
    · intro h X
      have hX : X.det = StatedQuadPlus 2 K ((oMat K).symm X) := by
        rw [← det_oMat, LinearEquiv.apply_symm_apply]
      rw [determinantForm_apply, determinantForm_apply, oPhi_apply, det_oMat, h, hX]
    · intro h v
      have h1 := h (oMat K v)
      rw [determinantForm_apply, determinantForm_apply, oPhi_apply, LinearEquiv.symm_apply_apply,
        det_oMat, det_oMat] at h1
      exact h1
  unfold StatedOmega
  rw [hset, Subgroup.closure_eq, Subgroup.map_commutator,
    Subgroup.map_comap_eq_self_of_surjective (oPhi K).surjective]

variable [Finite K] [CharP K 2]

theorem commutator_statedOmega_quadPlus_two (h4 : 4 ≤ Nat.card K) :
    commutator (StatedOmega (StatedQuadPlus 2 K)) = ⊤ := by
  have hSL : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin 2) K) :=
    CFSG.ClassicalModels.specialLinear_isPerfect_two_of_four_le_card K h4
  have hprod : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin 2) K ×
      Matrix.SpecialLinearGroup (Fin 2) K) := by
    rw [Group.isPerfect_def, commutator_def, ← Subgroup.top_prod_top,
      Subgroup.commutator_prod_prod, ← commutator_def, hSL.commutator_eq_top]
  set ρ := (DeterminantIsometries K).subtype.comp (specialRho (K := K))
  have hperf : Group.IsPerfect ρ.range := Group.IsPerfect.range ρ
  have hrange : ⁅DeterminantIsometries K, DeterminantIsometries K⁆ = ρ.range := by
    apply le_antisymm
    · rw [Subgroup.commutator_le]
      intro g hg h hh
      obtain ⟨z, hz⟩ := commutator_mem_specialImage_charTwo ⟨g, hg⟩ ⟨h, hh⟩
      exact ⟨z, congrArg Subtype.val hz⟩
    · calc ρ.range = ⁅ρ.range, ρ.range⁆ := Subgroup.commutator_eq_self.symm
        _ ≤ ⁅DeterminantIsometries K, DeterminantIsometries K⁆ := by
          have hle : ρ.range ≤ DeterminantIsometries K := by
            rintro _ ⟨z, rfl⟩
            exact (specialRho z).2
          exact Subgroup.commutator_mono hle hle
  let e : StatedOmega (StatedQuadPlus 2 K) ≃* ρ.range :=
    ((oPhi K).subgroupMap (StatedOmega (StatedQuadPlus 2 K))).trans
      (MulEquiv.subgroupCongr (by rw [← hrange, ← map_statedOmega_oPhi]; rfl))
  have h2 : commutator (StatedOmega (StatedQuadPlus 2 K)) =
      (commutator ρ.range).map e.symm.toMonoidHom := by
    rw [commutator_def, commutator_def, Subgroup.map_commutator,
      Subgroup.map_top_of_surjective _ e.symm.surjective]
  rw [h2, hperf.commutator_eq_top, Subgroup.map_top_of_surjective _ e.symm.surjective]

end Perfect

end CFSG.ComponentClassification.RankTwoClassical
