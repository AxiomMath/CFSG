module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.E6ThreeSc

public section

namespace CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.E6Heis

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.HardMathSupport.Timmesfeld.Steinberg
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.Blueprint.Chevalley.RootCertificate


@[expose] def repD : Fin Tag.E6.rank → ZMod 3 := ![1, 1, 1, 0, 0, 0]

@[expose] def repA : Fin Tag.E6.rank → ZMod 3 := ![0, 0, 0, 1, 0, 0]

private theorem vec3_e6ThreeStab6 : vec3 (τ := .E6) e6ThreeStab6.vec = repD := by
  decide +kernel

private theorem vec3_e6ThreeStab7 : vec3 (τ := .E6) e6ThreeStab7.vec = repA := by
  decide +kernel

private theorem triPairing_e6Shift_eq_zero_of_passing
    {S : StabCert3} (hS : S ∈ e6ThreeStabs)
    (hpass : S.passing e6Certificate = [List.range Tag.E6.rank])
    {w : WeylGroup Tag.E6} (hw : w ∈ charStabilizer (triChar (vec3 (τ := .E6) S.vec))) :
    triPairing (vec3 (τ := .E6) S.vec) (e6Shift w) = 0 := by
  obtain ⟨u, hu, hwu⟩ := exists_mul_mem_kernelPosStabilizer hw
  obtain ⟨t, ht, hrep⟩ := StabCert3.exists_passing_of_mem e6Certificate_check
    (e6ThreeScCheck_spec.2 S hS).1 hwu
  rw [hpass, List.mem_singleton] at ht
  subst ht
  have h1 : w * u = 1 := represents_unique hrep (represents_one e6Certificate_check)
  have h2 := triPairing_e6Shift_mul hw u
  rw [h1, e6Shift_one, triPairing_zero, triPairing_e6Shift_of_mem_kernelWeylGroup hu,
    zero_add] at h2
  exact h2.symm

private theorem triPairing_e6Shift_eq_zero_of_lt_six {ρ : ℕ}
    (hρ : ρ < 6) {w : WeylGroup Tag.E6}
    (hw : w ∈ charStabilizer (triChar (vec3 (τ := .E6) (e6ThreeReps.getD ρ [])))) :
    triPairing (vec3 (τ := .E6) (e6ThreeReps.getD ρ [])) (e6Shift w) = 0 := by
  interval_cases ρ
  · exact triPairing_e6Shift_eq_zero_of_passing (S := e6ThreeStab0) (by simp [e6ThreeStabs])
      (by decide +kernel) hw
  · exact triPairing_e6Shift_eq_zero_of_passing (S := e6ThreeStab1) (by simp [e6ThreeStabs])
      (by decide +kernel) hw
  · exact triPairing_e6Shift_eq_zero_of_passing (S := e6ThreeStab2) (by simp [e6ThreeStabs])
      (by decide +kernel) hw
  · exact triPairing_e6Shift_eq_zero_of_passing (S := e6ThreeStab3) (by simp [e6ThreeStabs])
      (by decide +kernel) hw
  · exact triPairing_e6Shift_eq_zero_of_passing (S := e6ThreeStab4) (by simp [e6ThreeStabs])
      (by decide +kernel) hw
  · exact triPairing_e6Shift_eq_zero_of_passing (S := e6ThreeStab5) (by simp [e6ThreeStabs])
      (by decide +kernel) hw

theorem exists_rep (b : Fin Tag.E6.rank → ZMod 3)
    {w : WeylGroup Tag.E6} (hw : w ∈ charStabilizer (triChar b))
    (hsh : triPairing b (e6Shift w) ≠ 0) :
    ∃ (t : WeylGroup Tag.E6) (b' : Fin Tag.E6.rank → ZMod 3), (b' = repD ∨ b' = repA) ∧
      (∀ v, triPairing b (t • v) = triPairing b' v) ∧
      t⁻¹ * w * t ∈ charStabilizer (triChar b') ∧
      triPairing b' (e6Shift (t⁻¹ * w * t)) ≠ 0 := by
  obtain ⟨ρ, hρ, t, ht⟩ := exists_isCharConj_of_orbitCheck3 e6ThreeScCheck_spec.1 (triChar b)
  have hpair : ∀ v, triPairing b v =
      triPairing (vec3 (τ := .E6) (e6ThreeReps.getD ρ [])) (t⁻¹ • v) := fun v => by
    have h := ht v
    rw [triChar_apply, triChar_apply] at h
    exact Z3.ofAdd_eq_ofAdd_iff.1 h
  have hw₀ : t⁻¹ * w * t ∈ charStabilizer (triChar (vec3 (τ := .E6) (e6ThreeReps.getD ρ []))) :=
    (charStabilizer_iff_of_isCharConj ht).1 hw
  have hsh₀ : triPairing (vec3 (τ := .E6) (e6ThreeReps.getD ρ [])) (e6Shift (t⁻¹ * w * t)) =
      triPairing b (e6Shift w) := by
    have hinv : t⁻¹ • e6Shift t + e6Shift t⁻¹ = 0 := by
      rw [← e6Shift_mul, inv_mul_cancel, e6Shift_one]
    have e1 : e6Shift (t⁻¹ * w * t) = t⁻¹ • (w • e6Shift t) + t⁻¹ • e6Shift w + e6Shift t⁻¹ := by
      rw [mul_assoc, e6Shift_mul, e6Shift_mul, smul_add]
    have e2 : triPairing (vec3 (τ := .E6) (e6ThreeReps.getD ρ [])) (t⁻¹ • e6Shift t) +
        triPairing (vec3 (τ := .E6) (e6ThreeReps.getD ρ [])) (e6Shift t⁻¹) = 0 := by
      rw [← triPairing_add, hinv, triPairing_zero]
    rw [e1, triPairing_add, triPairing_add, ← hpair, ← hpair, triPairing_smul_of_mem hw,
      hpair (e6Shift t)]
    linear_combination e2
  refine ⟨t, vec3 (τ := .E6) (e6ThreeReps.getD ρ []), ?_, fun v => by rw [hpair, inv_smul_smul],
    hw₀, hsh₀ ▸ hsh⟩
  have hρ8 : ρ < 8 := hρ
  rcases (by omega : ρ < 6 ∨ ρ = 6 ∨ ρ = 7) with h6 | rfl | rfl
  · exact absurd (hsh₀.symm.trans (triPairing_e6Shift_eq_zero_of_lt_six h6 hw₀)) hsh
  · exact Or.inl vec3_e6ThreeStab6
  · exact Or.inr vec3_e6ThreeStab7

end CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.E6Heis
