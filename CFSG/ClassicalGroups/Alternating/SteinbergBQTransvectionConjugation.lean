module

public import CFSG.ClassicalGroups.Alternating.Transvections

public section

namespace CFSG.ClassicalGroups.Alternating

open LinearMap (BilinForm)

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {B : BilinForm K V}

namespace SteinbergBQ

theorem symplecticTransvection_conj (hB : B.IsAlt) {g : LinearMap.GeneralLinearGroup K V}
    (hg : ∀ x y, B ((g : V →ₗ[K] V) x) ((g : V →ₗ[K] V) y) = B x y) (a : V) (c : K) :
    g * symplecticTransvection B hB a c * g⁻¹ =
      symplecticTransvection B hB ((g : V →ₗ[K] V) a) c := by
  refine Units.ext (LinearMap.ext fun x => ?_)
  have hx : (g : V →ₗ[K] V) (((g⁻¹ : LinearMap.GeneralLinearGroup K V) : V →ₗ[K] V) x) = x := by
    rw [← Module.End.mul_apply, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Module.End.one_apply]
  have hB' : B (((g⁻¹ : LinearMap.GeneralLinearGroup K V) : V →ₗ[K] V) x) a =
      B x ((g : V →ₗ[K] V) a) := by
    rw [← hg, hx]
  rw [Units.val_mul, Units.val_mul, Module.End.mul_apply, Module.End.mul_apply,
    symplecticTransvection_apply, symplecticTransvection_apply, map_add, map_smul, hx, hB']

theorem symplecticTransvection_smul (hB : B.IsAlt) (μ : K) (a : V) (c : K) :
    symplecticTransvection B hB (μ • a) c = symplecticTransvection B hB a (μ ^ 2 * c) := by
  refine Units.ext (LinearMap.ext fun x => ?_)
  rw [symplecticTransvection_apply, symplecticTransvection_apply, map_smul, smul_eq_mul,
    smul_smul]
  congr 1
  ring_nf

end SteinbergBQ

end CFSG.ClassicalGroups.Alternating
