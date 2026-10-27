module

public import CFSG.HardMathSupport.Lang.E6Descent.OuterFixed27D4AmbientFixed
public import CFSG.LieType.Chevalley.TrialityFullAmbientFixedGroup
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.D4TrialityAux.Basic
public import CFSG.HardMathSupport.Lang.D4Three.BridgeRange
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition

public section

namespace CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.LieType.Chevalley CFSG.HardMathSupport.Lang.D4Three CFSG.HardMathSupport.Lang.E6Descent
  CFSG.ComponentClassification.FixedCommutingProduct

section GraphFieldA


variable {K : Type} [Field K] [Finite K]

theorem isSimpleGroup_fixedSubgroup_twistedEntrywise_one {ℓ e : ℕ} [Fact ℓ.Prime] [CharP K ℓ]
    (he : 1 ≤ e) (hK : Nat.card K = ℓ ^ (e * 3)) (σ : K ≃+* K) (r : ℕ) (hr : r = 1 ∨ r = 2)
    (hσ : ∀ c, σ c = c ^ ((ℓ ^ e) ^ r)) :
    IsSimpleGroup (fixedSubgroup (twistedEntrywiseAut TwistTag.D4 1 σ)) := by
  classical
  haveI : CharP (AlgebraicClosure K) ℓ :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective ℓ
  obtain ⟨-, -, hfixeq, hsimple, -⟩ :=
    triality_both_field_orientations_simple_full_ambient_fixed_group ℓ e Fact.out he K
      (by rw [hK, pow_mul]) (AlgebraicClosure K) r hr σ.toRingHom hσ
      (iterateFrobenius (AlgebraicClosure K) ℓ e) (fun c => by simp [iterateFrobenius_def])
  let eΓ : fixedSubgroup (twistedEntrywiseAut TwistTag.D4 1 σ) ≃*
      graphFixedRootGroup TwistTag.D4 K σ.toRingHom :=
    (fixedSubgroupTwistedEntrywiseAutOneEquiv TwistTag.D4 σ).trans
      (MulEquiv.subgroupCongr hfixeq)
  haveI := hsimple
  exact eΓ.isSimpleGroup

theorem noNormalCop_fixSub_twistedEntrywise {ℓ e : ℕ} [Fact ℓ.Prime] [CharP K ℓ] (hℓ3 : ℓ ≠ 3)
    (he : 1 ≤ e) (hK : Nat.card K = ℓ ^ (e * 3)) (T : K ≃+* K) (hT : ∀ c, T c = c ^ (ℓ ^ e))
    (j : ℤ) (hj : j % 3 = 1 ∨ j % 3 = 2) :
    NoNormalCop 3 (CFSG.HardMathSupport.Timmesfeld.CrossChar.fixSub
      (twistedEntrywiseAut TwistTag.D4 j T)) := by
  classical
  have hℓ : ℓ.Prime := Fact.out
  have h3 : ¬ 3 ∣ ℓ ^ e := fun h =>
    hℓ3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hℓ).1
      (Nat.prime_three.dvd_of_dvd_pow h)).symm
  have hK' : Nat.card K = (ℓ ^ e) ^ 3 := by rw [hK, pow_mul]
  have hper : twistedEntrywiseAut TwistTag.D4 j T = twistedEntrywiseAut TwistTag.D4 (j % 3) T := by
    have h := twistedEntrywiseAut_add_mul_order TwistTag.D4 (j % 3) (j / 3) T
    rw [show j % 3 + j / 3 * ((TwistTag.D4.order : ℕ) : ℤ) = j by
      change j % 3 + j / 3 * 3 = j
      omega] at h
    exact h
  have hdvd : 27 ∣ Nat.card (fixedSubgroup (twistedEntrywiseAut TwistTag.D4 (j % 3) T)) :=
    twentySeven_dvd_card_fixedSubgroup_twistedEntrywiseAut_D4 hℓ he h3 K hK' T hT (j % 3) hj
  have hfix : CFSG.HardMathSupport.Timmesfeld.CrossChar.fixSub
      (twistedEntrywiseAut TwistTag.D4 j T) =
        fixedSubgroup (twistedEntrywiseAut TwistTag.D4 (j % 3) T) := by
    rw [hper]
    exact Subgroup.ext fun _ => Iff.rfl
  rw [hfix]
  have hq3 : ∀ c : K, c ^ ((ℓ ^ e) ^ 3) = c := fun c => by
    have : Fintype K := Fintype.ofFinite K
    rw [← hK', Nat.card_eq_fintype_card, FiniteField.pow_card]
  have hT3 : T ^ 3 = 1 := by
    refine RingEquiv.ext fun c => ?_
    change T (T (T c)) = c
    rw [hT, hT, hT, ← pow_mul, ← pow_mul, show ℓ ^ e * (ℓ ^ e * ℓ ^ e) = (ℓ ^ e) ^ 3 by ring, hq3]
  have hinv : ∀ c, T⁻¹ c = c ^ ((ℓ ^ e) ^ 2) := by
    have h1 : T⁻¹ = T ^ 2 := inv_eq_of_mul_eq_one_right (by rw [← pow_succ']; exact hT3)
    intro c
    rw [h1, pow_two]
    change T (T c) = _
    rw [hT, hT, ← pow_mul, sq]
  have h3dvd : 3 ∣ Nat.card (fixedSubgroup (twistedEntrywiseAut TwistTag.D4 (j % 3) T)) :=
    (by norm_num : (3 : ℕ) ∣ 27).trans hdvd
  rcases hj with h | h
  · rw [h] at h3dvd ⊢
    have hs := isSimpleGroup_fixedSubgroup_twistedEntrywise_one he hK T 1 (Or.inl rfl)
      (fun c => by rw [hT, pow_one])
    exact noNormalCop_of_simple (by norm_num) hs h3dvd
  · rw [h] at h3dvd ⊢
    rw [fixedSubgroup_twistedEntrywiseAut_D4_two T] at h3dvd ⊢
    have hs := isSimpleGroup_fixedSubgroup_twistedEntrywise_one he hK T⁻¹ 2 (Or.inr rfl) hinv
    exact noNormalCop_of_simple (by norm_num) hs h3dvd

end GraphFieldA

end CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross
