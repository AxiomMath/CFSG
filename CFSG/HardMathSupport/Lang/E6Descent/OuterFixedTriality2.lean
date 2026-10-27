module

public import CFSG.HardMathSupport.Lang.E6Descent.OuterFixedTriality2Classes
public import CFSG.HardMathSupport.Lang.Coordinator.OuterFixedOrderPSU
public import CFSG.LieType.Chevalley.OddExceptionalOuterTwoRank
public import CFSG.RankThree.PartTwo.Sec21.LangTwisted2ProofD4

public noncomputable section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Lang.E6Descent

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec8
  CFSG.RankThree.PartTwo.KFacts
open CFSG.Assembly.LowTwoRank (StatedLieTag StatedLieAdmissible)
open CFSG.ComponentClassification.CatLeaf (lieOrderNumerator)
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

@[expose] def EvenSecondBoundAt (f : ℕ) : Prop :=
  ∀ (F : Type) [Field F] [Finite F] (σ : F ≃+* F), Nat.card F = (2 ^ f) ^ 3 →
    (∀ c, σ c = c ^ 2 ^ f) →
    ∀ y : graphFixedRootGroup TwistTag.D4 F σ.toRingHom, fieldActor σ σ y = y → y ^ 3 = 1 →
      y ≠ 1 →
      Nat.card (fixedSubgroup (MulAut.conj y * fieldActor σ σ)) ∣ CFSG.Open.ordG2 (2 ^ f)

@[expose] def EvenSecondBound : Prop :=
  ∀ f : ℕ, Even f → EvenSecondBoundAt f

section

theorem y0_fixed_cube {K : Type} [Field K] [Finite K] (σ : K ≃+* K) (h2 : (2 : K) = 0) :
    fieldActor (t := TwistTag.D4) σ σ (d4TrialityY0Elt K σ) = d4TrialityY0Elt K σ ∧
      d4TrialityY0Elt K σ ^ 3 = 1 := by
  refine ⟨Subtype.ext ?_, Subtype.ext ?_⟩
  · rw [coe_fieldActor]
    exact LangTwistedProof.entrywise_d4TrialityY0 σ.toRingHom
  · exact LangTwistedProof.d4TrialityY0_pow_three h2

theorem card_fixedSubgroup_dvd_ordG2_of_order_three {n : ℕ} (hn : 1 ≤ n)
    (hev : Even n → EvenSecondBoundAt n) {K : Type} [Field K] [Finite K] {σ : K ≃+* K}
    (hK : Nat.card K = (2 ^ n) ^ 3) (hσ : ∀ c, σ c = c ^ 2 ^ n)
    {α : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)} (hα3 : α ^ 3 = 1)
    (hαin : α ∉ inner (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) :
    Nat.card (fixedSubgroup α) ∣ CFSG.Open.ordG2 (2 ^ n) := by
  obtain ⟨y, hy, hcard⟩ := exists_card_fixedSubgroup_eq_class hn hK hσ hα3 hαin
  rw [hcard]
  have hone : ∀ z : graphFixedRootGroup TwistTag.D4 K σ.toRingHom, z = 1 →
      Nat.card (fixedSubgroup (MulAut.conj z * fieldActor σ σ)) ∣ CFSG.Open.ordG2 (2 ^ n) :=
    fun z hz => by
      rw [hz, map_one, one_mul, card_fixedSubgroup_sigma0 hn hK hσ]
  rcases hy with rfl | rfl
  · exact hone _ rfl
  · by_cases h1 : d4TrialityY0Elt K σ = 1
    · exact hone _ h1
    have hK3 : Nat.card K = 2 ^ (3 * n) := by rw [hK, ← pow_mul, mul_comm]
    have : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two (by omega) hK3
    have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
    rcases Nat.even_or_odd n with he | ho
    · obtain ⟨hfix, hcube⟩ := y0_fixed_cube σ h2
      exact hev he K σ hK hσ _ hfix hcube h1
    · obtain ⟨F, hF, hFf, hFc, ⟨e⟩⟩ := kF82D4SecondCentY0_holds n ho K σ hK hσ
      have := card_dvd_ordG2_of_isoPGUThree hn ⟨F, hF, hFf, hFc, ⟨e⟩⟩
      rwa [autFix_eq_fixedSubgroup] at this

theorem outerFixedOrder_trialityD4_three_even_aux {f : ℕ}
    (hev : Even f → EvenSecondBoundAt f)
    (K : Type) [Group K] [Finite K] (hf : 1 ≤ f)
    (hmodel : CFSG.Blueprint.TwistedChevalleyModel K .D4 (2 ^ f))
    (α : MulAut K) (hα3 : α ^ 3 = 1) (hαin : α ∉ inner K) :
    Nat.card (fixedSubgroup α) ∣ lieOrderNumerator .G2 0 (2 ^ f) := by
  obtain ⟨K', _, _, σ, hcard, hσ, ⟨e⟩⟩ :=
    exists_mulEquiv_graphFixedRootGroup_card .D4 Nat.prime_two hf hmodel
  have hcard' : Nat.card K' = (2 ^ f) ^ 3 := hcard
  have hβ3 : MulAut.congr e α ^ 3 = 1 := by rw [← map_pow, hα3, map_one]
  have hβout : MulAut.congr e α ∉ inner (graphFixedRootGroup TwistTag.D4 K' σ.toRingHom) :=
    fun hin => hαin ((CFSG.HardMathSupport.Lang.Coordinator.congr_mem_inner_iff e α).mp hin)
  rw [← CFSG.HardMathSupport.Lang.Coordinator.card_fixedSubgroup_congr e α]
  exact card_fixedSubgroup_dvd_ordG2_of_order_three hf hev hcard' hσ hβ3 hβout

theorem outerFixedOrder_trialityD4_three_even_of_evenSecond (hE : EvenSecondBound) :
    ∀ (K : Type) [Group K] [Finite K] (n f : ℕ), StatedLieAdmissible .trialityD4 n 2 f →
      CFSG.Blueprint.LieModel K .trialityD4 n 2 f →
      ∀ α : MulAut K, α ^ 3 = 1 → α ∉ inner K →
        Nat.card (fixedSubgroup α) ∣ lieOrderNumerator .G2 0 (2 ^ f) := by
  intro K _ _ n f hadm hmodel α hα3 hαin
  rcases hmodel with ⟨ht, -⟩ | ⟨-, -, hM⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩
  · exact absurd ht (by decide)
  · exact outerFixedOrder_trialityD4_three_even_aux (hE f) K hadm.2.1 hM.2 α hα3 hαin
  · exact absurd ht (by decide)
  · exact absurd ht (by decide)

end

end CFSG.HardMathSupport.Lang.E6Descent
