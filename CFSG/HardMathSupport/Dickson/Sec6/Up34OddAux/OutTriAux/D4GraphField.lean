module

public import CFSG.HardMathSupport.Dickson.Sec6.I923Fam.D4Aux.Model
public import CFSG.HardMathSupport.Dickson.Sec6.Up34OddAux.Layer
public import CFSG.HardMathSupport.Lang.E6Descent.OuterFixed27D4AmbientFixed

public section

namespace CFSG.HardMathSupport.Dickson.Sec6.OutTri

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.Assembly.LowTwoRank
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma514CoverNs
  CFSG.ComponentClassification.CatLeaf CFSG.HardMathSupport.Solomon.UniquenessMaximal
open CFSG.HardMathSupport.Dickson.Sec6 CFSG.HardMathSupport.Dickson.Sec6.I923
open CFSG.HardMathSupport.Lang.E6Descent (twistedEntrywiseAut)

set_option linter.unusedSectionVars false

theorem three_le_pow_of_odd_prime {ℓ f : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (hf : 1 ≤ f) :
    3 ≤ ℓ ^ f := by
  have h3 : 3 ≤ ℓ := by
    have := hℓ.two_le
    omega
  calc 3 ≤ ℓ := h3
    _ = ℓ ^ 1 := (pow_one ℓ).symm
    _ ≤ ℓ ^ f := Nat.pow_le_pow_right hℓ.pos hf

theorem lt_card_triD4 {q : ℕ} (hq : 3 ≤ q) :
    20160 < q ^ 12 * (q ^ 2 - 1) * (q ^ 6 - 1) * (q ^ 8 + q ^ 4 + 1) := by
  have h12 : 531441 ≤ q ^ 12 :=
    calc 531441 = 3 ^ 12 := by norm_num
      _ ≤ q ^ 12 := Nat.pow_le_pow_left hq 12
  have h2 : 9 ≤ q ^ 2 :=
    calc 9 = 3 ^ 2 := by norm_num
      _ ≤ q ^ 2 := Nat.pow_le_pow_left hq 2
  have h6 : 729 ≤ q ^ 6 :=
    calc 729 = 3 ^ 6 := by norm_num
      _ ≤ q ^ 6 := Nat.pow_le_pow_left hq 6
  have h := Nat.mul_le_mul
    (Nat.mul_le_mul (Nat.mul_le_mul h12 (show 1 ≤ q ^ 2 - 1 by omega))
      (show 1 ≤ q ^ 6 - 1 by omega)) (show 1 ≤ q ^ 8 + q ^ 4 + 1 by omega)
  omega

section GraphField


theorem noL34Layer_twistedEntrywiseAut_D4_one {ℓ d : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2)
    (hd : 1 ≤ d) {K : Type} [Field K] [Finite K] (hK : Nat.card K = (ℓ ^ d) ^ 3) (r : ℕ)
    (hr : r = 1 ∨ r = 2) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ ((ℓ ^ d) ^ r)) :
    NoL34Layer (twistedEntrywiseAut TwistTag.D4 1 σ) := by
  classical
  haveI := D4Aux.finite_adjointD4 K
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
  refine noL34Layer_of_fixed_equiv _ (MulEquiv.refl _) inferInstance hnab' fun hT => ?_
  have h1 := card_eq_of_isLThreeFour (IsLThreeFour.of_mulEquiv e hT)
  rw [hcard] at h1
  have h2 := lt_card_triD4 (three_le_pow_of_odd_prime hℓ hℓ2 hd)
  omega

theorem noL34Layer_twistedEntrywiseAut_D4 {ℓ d : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (hd : 1 ≤ d)
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = (ℓ ^ d) ^ 3) (T : K ≃+* K)
    (hT : ∀ c, T c = c ^ (ℓ ^ d)) (j : ℤ) (hj : j = 1 ∨ j = 2) :
    NoL34Layer (twistedEntrywiseAut TwistTag.D4 j T) := by
  rcases hj with rfl | rfl
  · exact noL34Layer_twistedEntrywiseAut_D4_one hℓ hℓ2 hd hK 1 (Or.inl rfl) T (by simpa using hT)
  · have hT3 := ringEquiv_cube_apply_eq hK hT
    have hTinv : ∀ c, T⁻¹ c = c ^ ((ℓ ^ d) ^ 2) := by
      intro c
      have h1 : T⁻¹ (T (T (T c))) = T (T c) := RingEquiv.symm_apply_apply T _
      rw [hT3] at h1
      rw [h1, hT, hT, ← pow_mul, sq]
    exact noL34Layer_of_fix_eq
      (CFSG.HardMathSupport.Lang.E6Descent.fixedSubgroup_twistedEntrywiseAut_D4_two T)
      (noL34Layer_twistedEntrywiseAut_D4_one hℓ hℓ2 hd hK 2 (Or.inr rfl) T⁻¹ hTinv)

end GraphField

end CFSG.HardMathSupport.Dickson.Sec6.OutTri
