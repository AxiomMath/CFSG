module

public import CFSG.RankThree.PartOne.KC.LinearCommutantSemi

public section

namespace CFSG.LinearAlgebra

open Matrix
open CFSG.RankThree.PartOne.KCLinComm
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

variable {n : ℕ} {K : Type} [Field K]

theorem det_semilinGLAct (g : SemiGL (Fin n) K) (X : GL (Fin n) K) :
    Matrix.GeneralLinearGroup.det (semilinGLAct n K g X) =
      Units.map g.right.toMonoidHom (Matrix.GeneralLinearGroup.det X) := by
  obtain ⟨A, σ⟩ := g
  rw [semilinGLAct_mk]
  apply Units.ext
  rw [Units.coe_map, Matrix.GeneralLinearGroup.val_det_apply,
    Matrix.GeneralLinearGroup.val_det_apply]
  exact det_semilin_conj A σ X

theorem map_inf_det_ker_semilinGLAct (J : Subgroup (GL (Fin n) K)) (g : SemiGL (Fin n) K) :
    (J ⊓ (Matrix.GeneralLinearGroup.det : GL (Fin n) K →* Kˣ).ker).map
        (semilinGLAct n K g).toMonoidHom =
      J.map (semilinGLAct n K g).toMonoidHom ⊓
        (Matrix.GeneralLinearGroup.det : GL (Fin n) K →* Kˣ).ker := by
  ext x
  constructor
  · intro hx
    rw [Subgroup.mem_map] at hx
    obtain ⟨a, ha, rfl⟩ := hx
    rw [Subgroup.mem_inf] at ha
    rw [Subgroup.mem_inf]
    constructor
    · exact Subgroup.mem_map_of_mem _ ha.1
    · rw [MonoidHom.mem_ker] at ha ⊢
      change Matrix.GeneralLinearGroup.det (semilinGLAct n K g a) = 1
      rw [det_semilinGLAct, ha.2, map_one]
  · intro hx
    rw [Subgroup.mem_inf] at hx
    obtain ⟨hxJ, hxK⟩ := hx
    rw [Subgroup.mem_map] at hxJ
    obtain ⟨a, haJ, rfl⟩ := hxJ
    rw [Subgroup.mem_map]
    refine ⟨(semilinGLAct n K g)⁻¹ ((semilinGLAct n K g) a), ?_, ?_⟩
    · rw [Subgroup.mem_inf]
      constructor
      · rw [MulAut.inv_apply_self]
        exact haJ
      · rw [MonoidHom.mem_ker] at hxK ⊢
        change Matrix.GeneralLinearGroup.det (semilinGLAct n K g a) = 1 at hxK
        rw [← map_inv (semilinGLAct n K) g]
        change Matrix.GeneralLinearGroup.det
          (semilinGLAct n K g⁻¹ ((semilinGLAct n K g) a)) = 1
        rw [det_semilinGLAct, hxK, map_one]
    · change (semilinGLAct n K g) ((semilinGLAct n K g)⁻¹ ((semilinGLAct n K g) a)) =
        (semilinGLAct n K g) a
      rw [MulAut.apply_inv_self]

theorem map_inf_det_ker_semilinGLAct_of_normalizes
    {A : Type*} [Group A] (ρ : A →* SemiGL (Fin n) K)
    (J : Subgroup (GL (Fin n) K))
    (hJ : ∀ a : A, J.map (semilinGLAct n K (ρ a)).toMonoidHom = J) :
    ∀ a : A,
      (J ⊓ (Matrix.GeneralLinearGroup.det : GL (Fin n) K →* Kˣ).ker).map
          (semilinGLAct n K (ρ a)).toMonoidHom =
        J ⊓ (Matrix.GeneralLinearGroup.det : GL (Fin n) K →* Kˣ).ker := by
  intro a
  rw [map_inf_det_ker_semilinGLAct, hJ a]

end CFSG.LinearAlgebra
