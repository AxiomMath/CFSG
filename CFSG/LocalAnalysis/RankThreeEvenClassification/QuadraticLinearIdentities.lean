module

public import CFSG.Assembly.Defs
public import CFSG.LocalAnalysis.RankThreeEvenClassification.LocalCore

public section

namespace CFSG.RankThreeEvenClassification.Helpers

universe u v

theorem quadratic_linear_square_apply {field : Type u} {space : Type v}
    [Field field] [AddCommGroup space] [Module field space]
    (automorphism : space ≃ₗ[field] space)
    (hquadratic : ((automorphism : Module.End field space) - LinearMap.id) ^ 2 = 0)
    (member : space) : automorphism (automorphism member) = automorphism member + automorphism member - member := by
  have heq := DFunLike.congr_fun hquadratic member
  rw [pow_two, Module.End.mul_apply] at heq
  simp only [LinearMap.sub_apply, LinearMap.id_apply, LinearMap.zero_apply, map_sub] at heq
  have hfirst := sub_eq_zero.mp heq
  have hsecond := (sub_eq_iff_eq_add).mp hfirst
  change automorphism (automorphism member) = automorphism member - member + automorphism member at hsecond
  exact hsecond.trans (by abel)

theorem quadratic_linear_inverse_apply {field : Type u} {space : Type v}
    [Field field] [AddCommGroup space] [Module field space]
    (automorphism : space ≃ₗ[field] space)
    (hquadratic : ((automorphism : Module.End field space) - LinearMap.id) ^ 2 = 0)
    (member : space) : automorphism.symm member = member + member - automorphism member := by
  apply automorphism.injective
  rw [automorphism.apply_symm_apply, map_sub, map_add,
    quadratic_linear_square_apply automorphism hquadratic member]
  abel

theorem quadratic_linear_power_apply {field : Type u} {space : Type v}
    [Field field] [AddCommGroup space] [Module field space]
    (automorphism : space ≃ₗ[field] space)
    (hquadratic : ((automorphism : Module.End field space) - LinearMap.id) ^ 2 = 0)
    (exponent : ℕ) (member : space) :
    (automorphism ^ exponent) member = member + exponent • (automorphism member - member) := by
  induction exponent with
  | zero => simp
  | succ exponent ih =>
    rw [pow_succ', LinearEquiv.mul_apply, ih, map_add, map_nsmul, map_sub,
      quadratic_linear_square_apply automorphism hquadratic member, succ_nsmul]
    have hdifference : automorphism member + automorphism member - member - automorphism member =
        automorphism member - member := by abel
    rw [hdifference]
    abel

theorem quadratic_linear_pow_prime_eq_one {field : Type u} {space : Type v}
    [Field field] [AddCommGroup space] [Module field space]
    (prime : ℕ) [CharP field prime] (automorphism : space ≃ₗ[field] space)
    (hquadratic : ((automorphism : Module.End field space) - LinearMap.id) ^ 2 = 0) :
    automorphism ^ prime = 1 := by
  apply LinearEquiv.ext
  intro member
  rw [quadratic_linear_power_apply automorphism hquadratic prime member]
  have hzero : prime • (automorphism member - member) = 0 := by
    rw [← Nat.cast_smul_eq_nsmul field, CharP.cast_eq_zero field prime, zero_smul]
  rw [hzero, add_zero]
  rfl

theorem quadratic_linear_conjugate {field : Type u} {space : Type v}
    [Field field] [AddCommGroup space] [Module field space]
    (automorphism conjugator : space ≃ₗ[field] space)
    (hquadratic : ((automorphism : Module.End field space) - LinearMap.id) ^ 2 = 0) :
    (((conjugator⁻¹ * automorphism * conjugator) : Module.End field space) - LinearMap.id) ^ 2 = 0 := by
  apply LinearMap.ext
  intro member
  rw [pow_two, Module.End.mul_apply]
  simp only [LinearMap.sub_apply, LinearMap.id_apply, LinearMap.zero_apply]
  apply sub_eq_zero.mpr
  change conjugator.symm (automorphism (conjugator
      (conjugator.symm (automorphism (conjugator member)) - member))) =
    conjugator.symm (automorphism (conjugator member)) - member
  apply conjugator.injective
  rw [conjugator.apply_symm_apply, map_sub, conjugator.apply_symm_apply, map_sub,
    quadratic_linear_square_apply automorphism hquadratic]
  abel

end CFSG.RankThreeEvenClassification.Helpers
