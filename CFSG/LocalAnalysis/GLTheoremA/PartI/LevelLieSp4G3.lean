module

public import CFSG.LocalAnalysis.GLTheoremA.PartI.LevelLieSp4G1

public section

namespace CFSG.LocalAnalysis.GLTheoremA.LevelLieSp4G

open Polynomial CFSG.Open CFSG.Open.StatedAPI CFSG.LocalAnalysis.GLTheoremA.LevelLieSp4E
open CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCOrthogonal
open CFSG.RankThree.Classical CFSG.LocalAnalysis.ComponentInitial
open scoped commutatorElement
open Matrix

theorem h0_ne_X_sub_one (K : Type) [Field K] : h0 K ≠ X - 1 := by
  intro h
  have h1 : (X - 1 : K[X]).natDegree = 1 := by compute_degree!
  have h2 := congrArg natDegree h
  rw [natDegree_h0, h1] at h2
  omega

theorem det_commutatorElement_eq_one {E V : Type} [Field E] [AddCommGroup V] [Module E V]
    (x y : LinearMap.GeneralLinearGroup E V) :
    LinearMap.det ((⁅x, y⁆ : LinearMap.GeneralLinearGroup E V) : V →ₗ[E] V) = 1 := by
  have h : Units.map (LinearMap.det : (V →ₗ[E] V) →* E) ⁅x, y⁆ = 1 := by
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact mul_comm _ _
  have h2 := congrArg Units.val h
  rwa [Units.coe_map, Units.val_one] at h2

noncomputable def slRingEquiv {K₁ K₂ : Type} [Field K₁] [Field K₂] (ψ : K₁ ≃+* K₂) :
    Matrix.SpecialLinearGroup (Fin 2) K₁ ≃* Matrix.SpecialLinearGroup (Fin 2) K₂ where
  toFun := Matrix.SpecialLinearGroup.map (ψ : K₁ →+* K₂)
  invFun := Matrix.SpecialLinearGroup.map (ψ.symm : K₂ →+* K₁)
  left_inv A := Subtype.ext (Matrix.ext fun i j => by simp)
  right_inv B := Subtype.ext (Matrix.ext fun i j => by simp)
  map_mul' := (Matrix.SpecialLinearGroup.map (ψ : K₁ →+* K₂)).map_mul

noncomputable def slStatedEquiv (K : Type) [Field K] :
    Matrix.SpecialLinearGroup (Fin 2) K ≃* StatedSL 2 K :=
  (MonoidHom.ofInjective (Matrix.SpecialLinearGroup.toGL_injective (n := Fin 2) (R := K))).trans
    (MulEquiv.subgroupCongr (statedSL_eq_range_toGL 2 K).symm)

end CFSG.LocalAnalysis.GLTheoremA.LevelLieSp4G
