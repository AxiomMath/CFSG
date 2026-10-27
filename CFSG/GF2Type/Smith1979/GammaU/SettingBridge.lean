module

public import CFSG.GF2Type.Smith1979.GammaU.Bridge
public import CFSG.LargeExtraspecial.S3Basic

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1979.GammaU

open Module CFSG.LargeExtraspecial

theorem exists_isometry_theta0_of_setting {G : Type*} [Group G] [Finite G] (S : Setting G)
    (hw : S.width = 6) {θ : S.O} (h3 : θ ^ 3 = 1)
    (hfix : ∀ v, (θ : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v → v = 0) :
    ∃ φ : S.Qt ≃ₗ[ZMod 2] V12, (∀ v, q0 (φ v) = S.q v) ∧
      ∀ v, φ ((θ : S.Qt ≃ₗ[ZMod 2] S.Qt) v) = theta0 (φ v) := by
  have h3' : ∀ v, (θ : S.Qt ≃ₗ[ZMod 2] S.Qt) ((θ : S.Qt ≃ₗ[ZMod 2] S.Qt)
      ((θ : S.Qt ≃ₗ[ZMod 2] S.Qt) v)) = v := fun v => by
    have h := congrArg (fun g : S.O => (g : S.Qt ≃ₗ[ZMod 2] S.Qt) v) h3
    simpa [pow_succ, LinearEquiv.mul_apply] using h
  exact exists_isometry_theta0 (θ := ((θ : S.Qt ≃ₗ[ZMod 2] S.Qt) : S.Qt →ₗ[ZMod 2] S.Qt))
    S.q_nondegenerate (by rw [S.finrank_Qt_eq_two_mul_width, hw])
    (fun v => TauCeti.QuadraticMap.mem_orthogonalGroup_iff.1 θ.2 v) h3' hfix

end CFSG.GF2Type.Smith1979.GammaU
