module

public import CFSG.HardMathSupport.Dickson.Sec6.I923Fam.TriD4Aux.Basic
public import CFSG.HardMathSupport.Lang.E6Descent.OuterFixed27D4AmbientFixed
public import CFSG.HardMathSupport.Dickson.Sec6.I923Fam.D4Aux.Model

public section

namespace CFSG.HardMathSupport.Dickson.Sec6.I923.D4Aux

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.Assembly.LowTwoRank
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma514CoverNs
  CFSG.ComponentClassification.CatLeaf
open CFSG.HardMathSupport.Dickson.Sec6.I923
open CFSG.HardMathSupport.Lang.E6Descent (twistedEntrywiseAut)

set_option linter.unusedSectionVars false

section GraphField


theorem noL2Layer_twistedEntrywiseAut_D4_one {ℓ d : ℕ} (hℓ : ℓ.Prime) (hd : 1 ≤ d)
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = (ℓ ^ d) ^ 3) (r : ℕ)
    (hr : r = 1 ∨ r = 2) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ ((ℓ ^ d) ^ r)) :
    NoL2Layer (twistedEntrywiseAut TwistTag.D4 1 σ) := by
  classical
  haveI := finite_adjointD4 K
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  haveI : CharP K ℓ := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
    hℓ (k := d * 3) (by omega) (by rw [hK, pow_mul])
  haveI : CharP (AlgebraicClosure K) ℓ :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective ℓ
  obtain ⟨-, -, htw, hs, hnab⟩ := triality_both_field_orientations_simple_full_ambient_fixed_group
    ℓ d hℓ hd K hK (AlgebraicClosure K) r hr σ.toRingHom hσ
    (iterateFrobenius (AlgebraicClosure K) ℓ d) (fun c => iterateFrobenius_def _ _ _)
  have hcard := (triality_both_orientations_exact_finite_order ℓ d hℓ hd K hK r hr σ.toRingHom hσ).1
  haveI := hs
  let e : ↥(fixSubgroup (twistedEntrywiseAut TwistTag.D4 1 σ)) ≃*
      graphFixedRootGroup TwistTag.D4 K σ.toRingHom :=
    (CFSG.HardMathSupport.Lang.E6Descent.fixedSubgroupTwistedEntrywiseAutOneEquiv
      TwistTag.D4 σ).trans (MulEquiv.subgroupCongr htw)
  haveI : IsSimpleGroup ↥(fixSubgroup (twistedEntrywiseAut TwistTag.D4 1 σ)) := e.isSimpleGroup
  obtain ⟨a, b, hab⟩ := hnab
  have hnab' : ∃ x y : ↥(fixSubgroup (twistedEntrywiseAut TwistTag.D4 1 σ)), x * y ≠ y * x :=
    ⟨e.symm a, e.symm b, fun h => hab (by
      have := congrArg e h
      rwa [map_mul, map_mul, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply] at this)⟩
  refine noL2_of_simple_fixed _ inferInstance hnab' fun r' hr' hT => ?_
  have hT' := l2fld_isTypeL2_of_mulEquiv e hT
  have hadm : StatedLieAdmissible .trialityD4 0 ℓ d := ⟨hℓ, hd, rfl⟩
  refine TriD4Aux.not_typeL2_of_order hadm (by decide) (by simp) ?_
    (center_eq_bot_of_simple ⟨a, b, hab⟩) hr' hT'
  rw [hcard]
  simp only [lieOrderDivisor, lieOrderNumerator, mul_one]
  ring

theorem noL2Layer_twistedEntrywiseAut_D4 {ℓ d : ℕ} (hℓ : ℓ.Prime) (hd : 1 ≤ d)
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = (ℓ ^ d) ^ 3) (T : K ≃+* K)
    (hT : ∀ c, T c = c ^ (ℓ ^ d)) (j : ℤ) (hj : j = 1 ∨ j = 2) :
    NoL2Layer (twistedEntrywiseAut TwistTag.D4 j T) := by
  rcases hj with rfl | rfl
  · exact noL2Layer_twistedEntrywiseAut_D4_one hℓ hd hK 1 (Or.inl rfl) T (by simpa using hT)
  · have hT3 := ringEquiv_cube_apply_eq hK hT
    have hTinv : ∀ c, T⁻¹ c = c ^ ((ℓ ^ d) ^ 2) := by
      intro c
      have h1 : T⁻¹ (T (T (T c))) = T (T c) := RingEquiv.symm_apply_apply T _
      rw [hT3] at h1
      rw [h1, hT, hT, ← pow_mul, sq]
    exact noL2Layer_of_fixSubgroup_eq
      (CFSG.HardMathSupport.Lang.E6Descent.fixedSubgroup_twistedEntrywiseAut_D4_two T)
      (noL2Layer_twistedEntrywiseAut_D4_one hℓ hd hK 2 (Or.inr rfl) T⁻¹ hTinv)

end GraphField

end CFSG.HardMathSupport.Dickson.Sec6.I923.D4Aux
