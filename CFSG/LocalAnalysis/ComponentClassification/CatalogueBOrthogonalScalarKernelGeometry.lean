module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarKernelBasic

public section

namespace CFSG.ComponentClassification.CatalogueBOrthogonalScalarKernel

open QuadraticMap CFSG.ClassicalGroups.Orthogonal

variable {K : Type*} {V : Type*} [Field K] [AddCommGroup V] [Module K V]
variable {Q : QuadraticForm K V} {σ : K ≃+* K}

private theorem coefficients_eq {P R : HypPair Q} (h : P.Orth R)
    (T : V ≃ₛₗ[σ.toRingHom] V) (hfix : FixesSingularVectors Q T)
    {a b : K} (ha : T P.e = a • P.e) (hb : T R.e = b • R.e) : a = b := by
  have hQsum : Q (P.e + R.e) = 0 := by
    rw [QuadraticMap.map_add Q, P.Q_e, R.Q_e, h.ee]
    ring
  have hsumf : polar Q (P.e + R.e) P.f = 1 := by
    rw [polar_add_left, P.polar_ef, polar_comm Q R.e P.f, h.fe]
    ring
  have hsum0 : P.e + R.e ≠ 0 := by
    intro h0
    rw [h0, polar_zero_left] at hsumf
    exact zero_ne_one hsumf
  obtain ⟨c, hc⟩ := hfix _ hsum0 hQsum
  have hca := congrArg (fun z => polar Q z P.f) hc
  rw [map_add, ha, hb, polar_add_left, polar_smul_left_eq, polar_smul_left_eq,
    polar_smul_left_eq, P.polar_ef, polar_comm Q R.e P.f, h.fe, hsumf] at hca
  have hcb := congrArg (fun z => polar Q z R.f) hc
  rw [map_add, ha, hb, polar_add_left, polar_smul_left_eq, polar_smul_left_eq,
    polar_smul_left_eq, h.ef, R.polar_ef, polar_add_left, h.ef, R.polar_ef] at hcb
  linear_combination hca - hcb

theorem pair_coefficients {P R : HypPair Q} (h : P.Orth R)
    (T : V ≃ₛₗ[σ.toRingHom] V) (hfix : FixesSingularVectors Q T) :
    ∃ a : K, a ≠ 0 ∧ T P.e = a • P.e ∧ T P.f = a • P.f ∧
      T R.e = a • R.e ∧ T R.f = a • R.f := by
  obtain ⟨a, ha⟩ := hfix P.e P.e_ne_zero P.Q_e
  obtain ⟨b, hb⟩ := hfix P.f P.f_ne_zero P.Q_f
  obtain ⟨c, hc⟩ := hfix R.e R.e_ne_zero R.Q_e
  obtain ⟨d, hd⟩ := hfix R.f R.f_ne_zero R.Q_f
  have hac : a = c := coefficients_eq h T hfix ha hc
  let Rs : HypPair Q := ⟨R.f, R.e, R.Q_f, R.Q_e, R.polar_fe⟩
  let Ps : HypPair Q := ⟨P.f, P.e, P.Q_f, P.Q_e, P.polar_fe⟩
  have had : a = d :=
    coefficients_eq (P := P) (R := Rs) ⟨h.ef, h.ee, h.ff, h.fe⟩ T hfix ha hd
  have hbc : b = c :=
    coefficients_eq (P := Ps) (R := R) ⟨h.fe, h.ff, h.ee, h.ef⟩ T hfix hb hc
  refine ⟨a, coefficient_ne_zero T P.e_ne_zero ha, ha, ?_, ?_, ?_⟩
  · simpa [hbc, ← hac] using hb
  · simpa [← hac] using hc
  · simpa [← had] using hd

theorem automorphism_eq_refl_of_two_pairs {P R : HypPair Q} (h : P.Orth R)
    (T : V ≃ₛₗ[σ.toRingHom] V) (hfix : FixesSingularVectors Q T) :
    σ = RingEquiv.refl K := by
  obtain ⟨a, ha0, ha, -, hc, -⟩ := pair_coefficients h T hfix
  apply RingEquiv.ext
  intro c
  have hQsum : Q (P.e + c • R.e) = 0 := by
    rw [QuadraticMap.map_add Q, map_smul_eq_sq, polar_smul_right_eq, P.Q_e, R.Q_e, h.ee]
    ring
  have hsumf : polar Q (P.e + c • R.e) P.f = 1 := by
    rw [polar_add_left, polar_smul_left_eq, P.polar_ef, polar_comm Q R.e P.f, h.fe]
    ring
  have hsum0 : P.e + c • R.e ≠ 0 := by
    intro h0
    rw [h0, polar_zero_left] at hsumf
    exact zero_ne_one hsumf
  obtain ⟨b, hb⟩ := hfix _ hsum0 hQsum
  have hba := congrArg (fun z => polar Q z P.f) hb
  rw [map_add, T.map_smulₛₗ, ha, hc, smul_smul, polar_add_left, polar_smul_left_eq,
    polar_smul_left_eq, polar_smul_left_eq, P.polar_ef, polar_comm Q R.e P.f, h.fe,
    hsumf] at hba
  have hab : a = b := by linear_combination hba
  have hsig := congrArg (fun z => polar Q z R.f) hb
  rw [map_add, T.map_smulₛₗ, ha, hc, smul_smul, polar_add_left, polar_smul_left_eq,
    polar_smul_left_eq, polar_smul_left_eq, h.ef, R.polar_ef, polar_add_left,
    polar_smul_left_eq, h.ef, R.polar_ef] at hsig
  have hmul : σ c * a = c * a := by
    change a * 0 + σ c * a * 1 = b * (0 + c * 1) at hsig
    rw [← hab] at hsig
    linear_combination hsig
  exact mul_right_cancel₀ ha0 hmul

theorem multiplier_eq_sq_of_pair (T : V ≃ₛₗ[σ.toRingHom] V) (μ : Kˣ)
    (hT : ∀ v, Q (T v) = (μ : K) * σ (Q v)) (P : HypPair Q)
    {a : K} (he : T P.e = a • P.e) (hf : T P.f = a • P.f) :
    (μ : K) = a ^ 2 := by
  have hp := polar_similarity T μ hT P.e P.f
  rw [he, hf, polar_smul_left_eq, polar_smul_right_eq, P.polar_ef, map_one] at hp
  linear_combination -hp

end CFSG.ComponentClassification.CatalogueBOrthogonalScalarKernel
