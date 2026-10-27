module

public import CFSG.RankThree.PartTwo.Census.Carrier.SpinBOdd
public import CFSG.RankThree.PartTwo.Census.Carrier.SpinTDOdd
public import CFSG.LieType.Steinberg.CentralExt.POmegaMinusMultiplier
public import CFSG.LieType.Steinberg.CentralExt.SpinMinusFour
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.CenterHopf

public section

namespace CFSG.HardMathSupport.Meierfrankenfeld.LieOdd

open CFSG.Assembly.LowTwoRank TauCeti

theorem center_eq_bot_of_dvd_two_pow {L : Type} [Group L] [Finite L] (hperf : Group.IsPerfect L)
    (hodd : Odd (Nat.card (Subgroup.center L))) {S : Type} [Group S]
    (e : L ⧸ Subgroup.center L ≃* S) {k : ℕ}
    (hM : Nat.card (CFSG.Open.griessHopfMultiplier S) ∣ 2 ^ k) : Subgroup.center L = ⊥ := by
  have hdvd := (CFSG.AGLEmbedding.card_center_dvd_card_griessHopfMultiplier hperf e).trans hM
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
  have h1 : Nat.card (Subgroup.center L) = 1 := by
    rcases Nat.eq_zero_or_pos j with rfl | hj0
    · simpa using hj
    · rw [hj] at hodd
      exact absurd hodd (Nat.not_odd_iff_even.2 (Nat.even_pow.2 ⟨even_two, hj0.ne'⟩))
  exact Subgroup.eq_bot_of_card_eq _ h1

theorem card_multiplicative_zmod_prod (a b : ℕ) :
    Nat.card (Multiplicative (ZMod a) × Multiplicative (ZMod b)) = a * b := by
  rw [Nat.card_prod, Nat.card_congr Multiplicative.toAdd, Nat.card_congr Multiplicative.toAdd,
    Nat.card_zmod, Nat.card_zmod]

theorem two_ne_zero_of_card {K : Type} [Field K] [Finite K] {p e : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hK : Nat.card K = p ^ e) : (2 : K) ≠ 0 := by
  have : Fact p.Prime := ⟨hp⟩
  have : Fintype K := Fintype.ofFinite K
  have : CharP K p := charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card]; exact hK)
  exact CFSG.ClassicalGroups.Orthogonal.two_ne_zero_of_charP p hp2

theorem five_le_of_odd_prime_pow {p e : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (he : 1 ≤ e)
    (h3 : p ^ e ≠ 3) : 5 ≤ p ^ e := by
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  have hodd : Odd (p ^ e) := (hp.eq_two_or_odd'.resolve_left hp2).pow
  have h3' : 3 ≤ p ^ e := hp3.trans (Nat.le_self_pow (by omega) p)
  have h4 : p ^ e ≠ 4 := by
    intro h4
    rw [h4] at hodd
    exact absurd hodd (by decide)
  omega

theorem exists_pomega_model_of_lie_B {L : Type} [Group L] [Finite L] (hperf : Group.IsPerfect L)
    (hodd : Odd (Nat.card (Subgroup.center L))) {r : ℕ} {q : PrimePower}
    (hv : (LieTypeIndex.B r q).Valid) (hp2 : q.p ≠ 2) (hr : 3 ≤ r)
    (h73 : ¬ (r = 3 ∧ q.card = 3))
    (e : L ⧸ Subgroup.center L ≃* (CFSGIndex.lie ⟨.B r q, hv⟩).Group) :
    Subgroup.center L = ⊥ ∧ ∃ (K : Type) (_ : Field K) (_ : Finite K),
      Nat.card K = q.p ^ q.exponent ∧
        Nonempty (L ≃* StatedProj (StatedOmega (StatedQuadOdd r K))) := by
  have := CFSG.QuasithinUnique.SQTK.finite_validIndex_fixedField
    (⟨.B r q, hv⟩ : ValidLieTypeIndex)
  set K := ↥(ValidLieTypeIndex.fixedField ⟨.B r q, hv⟩)
  have hK : Nat.card K = q.p ^ q.exponent := by
    rw [ValidLieTypeIndex.card_fixedField]
    simp [ValidLieTypeIndex.fieldOrder, PrimePower.card_def]
  let e' : L ⧸ Subgroup.center L ≃* StatedProj (StatedOmega (StatedQuadOdd r K)) :=
    e.trans (CFSG.RankThree.PartTwo.Census.Carrier.SpinB.typeBGroupEquivStatedProj_odd r q hv
      hp2 hr)
  have h2 : (2 : K) ≠ 0 := two_ne_zero_of_card q.prime_p hp2 hK
  have hM : Nonempty (CFSG.Open.griessHopfMultiplier
      (StatedProj (StatedOmega (StatedQuadOdd r K))) ≃* Multiplicative (ZMod 2)) := by
    by_cases h3 : q.p ^ q.exponent = 3
    · have hr4 : 4 ≤ r := by
        by_contra h
        exact h73 ⟨by omega, by simpa [PrimePower.card_def] using h3⟩
      exact (CFSG.LieType.Steinberg.CentralExt.SpinOddClosed.pomegaOdd_three_hopfMultiplier
        (by rw [hK, h3]) hr4).2
    · have h5 := five_le_of_odd_prime_pow q.prime_p hp2 q.exponent_pos h3
      exact (CFSG.LieType.Steinberg.CentralExt.SpinOddClosed.pomegaOdd_hopfMultiplier h2 hr
        (by rw [hK]; exact h5)).2
  obtain ⟨φ⟩ := hM
  have hbot := center_eq_bot_of_dvd_two_pow hperf hodd e' (k := 1) (by
    rw [Nat.card_congr φ.toEquiv, Nat.card_congr Multiplicative.toAdd, Nat.card_zmod, pow_one])
  refine ⟨hbot, K, inferInstance, inferInstance, hK, ⟨?_⟩⟩
  exact (QuotientGroup.quotientBot.symm.trans
    (QuotientGroup.quotientMulEquivOfEq hbot.symm)).trans e'

theorem exists_pomega_model_of_lie_D {L : Type} [Group L] [Finite L] (hperf : Group.IsPerfect L)
    (hodd : Odd (Nat.card (Subgroup.center L))) {r : ℕ} {q : PrimePower}
    (hv : (LieTypeIndex.D r q).Valid) (hp2 : q.p ≠ 2)
    (e : L ⧸ Subgroup.center L ≃* (CFSGIndex.lie ⟨.D r q, hv⟩).Group) :
    Subgroup.center L = ⊥ ∧ ∃ (K : Type) (_ : Field K) (_ : Finite K),
      Nat.card K = q.p ^ q.exponent ∧
        Nonempty (L ≃* StatedProj (StatedOmega (StatedQuadPlus r K))) := by
  have hr : 4 ≤ r := (LieTypeIndex.inStandardRange_iff _).mp ((LieTypeIndex.valid_iff _).mp hv).1
  have := CFSG.QuasithinUnique.SQTK.finite_validIndex_fixedField
    (⟨.D r q, hv⟩ : ValidLieTypeIndex)
  set K := ↥(ValidLieTypeIndex.fixedField ⟨.D r q, hv⟩)
  have hK : Nat.card K = q.p ^ q.exponent := by
    rw [ValidLieTypeIndex.card_fixedField]
    simp [ValidLieTypeIndex.fieldOrder, PrimePower.card_def]
  let e' : L ⧸ Subgroup.center L ≃* StatedProj (StatedOmega (StatedQuadPlus r K)) :=
    e.trans (CFSG.RankThree.PartTwo.Census.Carrier.SpinD.typeDGroupEquivStatedProj_of_valid r q hv)
  have hM : Nonempty (CFSG.Open.griessHopfMultiplier
      (StatedProj (StatedOmega (StatedQuadPlus r K))) ≃*
        CFSG.Blueprint.Multiplier.generic .POmegaPlus r q.p q.exponent) := by
    by_cases h3 : q.p ^ q.exponent = 3
    · exact (CFSG.LieType.Steinberg.CentralExt.SpinPlusClosed.pomegaPlus_three_hopfMultiplier hr
        hK (by rw [hK, h3])).2
    · have h5 := five_le_of_odd_prime_pow q.prime_p hp2 q.exponent_pos h3
      exact (CFSG.LieType.Steinberg.CentralExt.SpinPlusClosed.pomegaPlus_hopfMultiplier
        (by omega) hK (by omega)).2
  obtain ⟨φ⟩ := hM
  have hord : (CFSG.Blueprint.Multiplier.genericOrders .POmegaPlus r q.p q.exponent).1 ∣ 4 ∧
      (CFSG.Blueprint.Multiplier.genericOrders .POmegaPlus r q.p q.exponent).2 ∣ 4 := by
    by_cases h1 : Even (q.p ^ q.exponent) <;> by_cases h2 : Even r <;>
      simp [CFSG.Blueprint.Multiplier.genericOrders, h1, h2, Nat.gcd_dvd_left]
  have hbot := center_eq_bot_of_dvd_two_pow hperf hodd e' (k := 4) (by
    rw [Nat.card_congr φ.toEquiv, card_multiplicative_zmod_prod]
    exact (Nat.mul_dvd_mul hord.1 hord.2).trans (by norm_num))
  refine ⟨hbot, K, inferInstance, inferInstance, hK, ⟨?_⟩⟩
  exact (QuotientGroup.quotientBot.symm.trans
    (QuotientGroup.quotientMulEquivOfEq hbot.symm)).trans e'

theorem center_eq_bot_of_pomegaMinus {L : Type} [Group L] [Finite L] (hperf : Group.IsPerfect L)
    (hodd : Odd (Nat.card (Subgroup.center L))) {K : Type} [Field K] [Finite K] {p f r : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f) (hK : Nat.card K = p ^ f) (hr : 4 ≤ r) {b c : K}
    (hbc : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (e : L ⧸ Subgroup.center L ≃* StatedProj (StatedOmega (StatedQuadMinus r K b c))) :
    Subgroup.center L = ⊥ := by
  have hM : Nonempty (CFSG.Open.griessHopfMultiplier
      (StatedProj (StatedOmega (StatedQuadMinus r K b c))) ≃*
        Multiplicative (ZMod (Nat.gcd 4 ((p ^ f) ^ r + 1)))) := by
    by_cases h3 : p ^ f = 3
    · exact (CFSG.LieType.Steinberg.CentralExt.SpinMinusClosed.pomegaMinus_three_hopfMultiplier'
        hr hbc hK (by rw [hK, h3])).2
    · have h5 := five_le_of_odd_prime_pow hp hp2 hf h3
      exact (CFSG.LieType.Steinberg.CentralExt.SpinMinusClosed.pomegaMinus_hopfMultiplier
        hr hbc hK (by rw [hK]; omega)).2
  obtain ⟨φ⟩ := hM
  exact center_eq_bot_of_dvd_two_pow hperf hodd e (k := 2) (by
    rw [Nat.card_congr φ.toEquiv, Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]
    exact (Nat.gcd_dvd_left _ _).trans (by norm_num))

theorem exists_pomega_model_of_lie_twistedD {L : Type} [Group L] [Finite L]
    (hperf : Group.IsPerfect L) (hodd : Odd (Nat.card (Subgroup.center L))) {r : ℕ}
    {q : PrimePower} (hv : (LieTypeIndex.twistedD r q).Valid) (hp2 : q.p ≠ 2)
    (e : L ⧸ Subgroup.center L ≃* (CFSGIndex.lie ⟨.twistedD r q, hv⟩).Group) :
    Subgroup.center L = ⊥ ∧ ∃ (K : Type) (_ : Field K) (_ : Finite K) (b c : K),
      (∀ s : K, s ^ 2 + b * s + c ≠ 0) ∧ Nat.card K = q.p ^ q.exponent ∧
        Nonempty (L ≃* StatedProj (StatedOmega (StatedQuadMinus r K b c))) := by
  have hr : 4 ≤ r := (LieTypeIndex.inStandardRange_iff _).mp ((LieTypeIndex.valid_iff _).mp hv).1
  have := CFSG.QuasithinUnique.SQTK.finite_validIndex_fixedField
    (⟨.twistedD r q, hv⟩ : ValidLieTypeIndex)
  have hK : Nat.card ↥(ValidLieTypeIndex.fixedField ⟨.twistedD r q, hv⟩) =
      q.p ^ q.exponent := by
    rw [ValidLieTypeIndex.card_fixedField]
    simp [ValidLieTypeIndex.fieldOrder, PrimePower.card_def]
  obtain ⟨b, c, hbc, ⟨ψ⟩⟩ :=
    CFSG.RankThree.PartTwo.Census.Carrier.SpinD.exists_typeTwistedDGroupEquivStatedProj_of_valid
      r q hv
  have hbot := center_eq_bot_of_pomegaMinus hperf hodd q.prime_p hp2 q.exponent_pos hK hr hbc
    (e.trans ψ)
  refine ⟨hbot, _, inferInstance, inferInstance, b, c, hbc, hK, ⟨?_⟩⟩
  exact (QuotientGroup.quotientBot.symm.trans
    (QuotientGroup.quotientMulEquivOfEq hbot.symm)).trans (e.trans ψ)

end CFSG.HardMathSupport.Meierfrankenfeld.LieOdd
