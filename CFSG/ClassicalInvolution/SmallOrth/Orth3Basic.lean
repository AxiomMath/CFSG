module

public import CFSG.ClassicalInvolution.SmallOrth.Scalar
public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.ClassicalGroups.Orthogonal.Small

open QuadraticMap

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

theorem exists_smul_eq_of_commute_eichler (h2 : (2 : K) ≠ 0) (hQ : (polarBilin Q).Nondegenerate)
    (hA : HasAnisoPerp Q) {ν : V ≃ₗ[K] V}
    (hcomm : ∀ u w, Q u = 0 → polar Q u w = 0 → ν * eichler Q u w = eichler Q u w * ν)
    {v : V} (hv : Q v = 0) (hv0 : v ≠ 0) : ∃ c : K, ν v = c • v := by
  obtain ⟨P, rfl⟩ := exists_hypPair hQ hv hv0
  obtain ⟨a, ha, hc⟩ := hA P
  have hea : polar Q P.e a = 0 := (HypPair.mem_perp.mp ha).1
  have hfa : polar Q P.f a = 0 := (HypPair.mem_perp.mp ha).2
  have h2c : 2 * Q a ≠ 0 := mul_ne_zero h2 hc
  set g := eichler Q P.e a with hg
  have hgx : ∀ x, g x = x + polar Q x P.e • a - (polar Q x a + Q a * polar Q x P.e) • P.e :=
    fun x => eichler_apply P.Q_e hea x
  have hνg : ∀ x, ν (g x) = g (ν x) := fun x => by
    have := congrArg (fun m => m x) (hcomm P.e a P.Q_e hea)
    exact this
  have hga : g a = a - (2 * Q a) • P.e := by
    rw [hgx, polar_comm Q a P.e, hea, polar_self_eq_two_mul]
    module
  have he : P.e = (-(2 * Q a)⁻¹) • (g a - a) := by
    rw [hga, show a - (2 * Q a) • P.e - a = (-(2 * Q a)) • P.e by module, smul_smul]
    have : -(2 * Q a)⁻¹ * -(2 * Q a) = 1 := by field_simp
    rw [this, one_smul]
  have hνe : ν P.e = (-(2 * Q a)⁻¹) • (g (ν a) - ν a) := by
    conv_lhs => rw [he]
    rw [map_smul, map_sub, hνg]
  have hge : g P.e = P.e := eichler_apply_self _ _
  have hfix : g (ν P.e) = ν P.e := by rw [← hνg, hge]
  obtain ⟨α, β, hνe'⟩ : ∃ α β : K, ν P.e = α • a + β • P.e := by
    refine ⟨-(2 * Q a)⁻¹ * polar Q (ν a) P.e,
      -(2 * Q a)⁻¹ * (-(polar Q (ν a) a + Q a * polar Q (ν a) P.e)), ?_⟩
    rw [hνe, hgx]
    module
  have hpe : polar Q (ν P.e) P.e = 0 := by
    rw [hνe', polar_add_left, polar_smul_left_eq, polar_smul_left_eq, polar_comm Q a P.e, hea,
      P.polar_ee]
    ring
  have hpa : polar Q (ν P.e) a = α * (2 * Q a) := by
    rw [hνe', polar_add_left, polar_smul_left_eq, polar_smul_left_eq, polar_self_eq_two_mul,
      hea]
    ring
  have h3 : polar Q (ν P.e) a • P.e = 0 := by
    have h1 := hfix
    rw [hgx, hpe] at h1
    simpa using h1
  have h4 : α * (2 * Q a) = 0 := by
    rw [← hpa]
    exact (smul_eq_zero.mp h3).resolve_right P.e_ne_zero
  have hα0 : α = 0 := (mul_eq_zero.mp h4).resolve_right h2c
  exact ⟨β, by rw [hνe', hα0, zero_smul, zero_add]⟩

theorem mem_scalars_of_commute_eichler (h2 : (2 : K) ≠ 0) (hQ : (polarBilin Q).Nondegenerate)
    (hA : HasAnisoPerp Q) (P : HypPair Q) {ν : V ≃ₗ[K] V}
    (hν : ν ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hcomm : ∀ u w, Q u = 0 → polar Q u w = 0 → ν * eichler Q u w = eichler Q u w * ν) :
    ν ∈ scalars K V := by
  obtain ⟨a, ha, hc⟩ := hA P
  exact mem_scalars_of_forall_singular_small P ha hc hν fun v hv0 hv =>
    exists_smul_eq_of_commute_eichler h2 hQ hA hcomm hv hv0

theorem mul_self_eq_one_of_mem_scalars {ν : V ≃ₗ[K] V}
    (hν : ν ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hs : ν ∈ scalars K V) {a : V}
    (ha : Q a ≠ 0) : ν * ν = 1 := by
  obtain ⟨c, hc⟩ := mem_scalars.mp hs
  have hc2 : c ^ 2 = 1 := by
    have h1 := map_of_mem hν a
    rw [hc a, map_smul_eq_sq] at h1
    have h3 : (c ^ 2 - 1) * Q a = 0 := by rw [sub_mul, h1, one_mul, sub_self]
    exact sub_eq_zero.mp ((mul_eq_zero.mp h3).resolve_right ha)
  refine LinearEquiv.ext fun x => ?_
  rw [LinearEquiv.mul_apply, hc, hc, smul_smul, ← pow_two, hc2, one_smul]
  rfl

theorem mul_self_eq_one_of_commute_eichler (h2 : (2 : K) ≠ 0)
    (hQ : (polarBilin Q).Nondegenerate) (hA : HasAnisoPerp Q) (P : HypPair Q) {ν : V ≃ₗ[K] V}
    (hν : ν ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hcomm : ∀ u w, Q u = 0 → polar Q u w = 0 → ν * eichler Q u w = eichler Q u w * ν) :
    ν * ν = 1 := by
  obtain ⟨a, -, ha⟩ := hA P
  exact mul_self_eq_one_of_mem_scalars hν (mem_scalars_of_commute_eichler h2 hQ hA P hν hcomm) ha

end CFSG.ClassicalGroups.Orthogonal.Small
