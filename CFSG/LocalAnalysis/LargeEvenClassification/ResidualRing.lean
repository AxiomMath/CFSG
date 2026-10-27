module

public import CFSG.LocalAnalysis.LargeEvenClassification.FrattiniExact

public section

namespace CFSG.LargeEvenClassification.Helpers

@[expose] def ResidualRing (_twist : ZMod 4) := (ZMod 4 × ZMod 4) × (ZMod 4 × ZMod 4)

@[expose] def residualAdd {twist : ZMod 4} (first second : ResidualRing twist) : ResidualRing twist :=
  ((first.1.1 + second.1.1, first.1.2 + second.1.2),
    (first.2.1 + second.2.1, first.2.2 + second.2.2))

instance residualRingAdd (twist : ZMod 4) : Add (ResidualRing twist) := ⟨residualAdd⟩

instance residualRingZero (twist : ZMod 4) : Zero (ResidualRing twist) := ⟨((0, 0), (0, 0))⟩

instance residualRingNeg (twist : ZMod 4) : Neg (ResidualRing twist) :=
  inferInstanceAs (Neg ((ZMod 4 × ZMod 4) × (ZMod 4 × ZMod 4)))

instance residualRingOne (twist : ZMod 4) : One (ResidualRing twist) := ⟨((1, 0), (0, 1))⟩

@[expose] def residualMultiply (twist : ZMod 4) (first second : ResidualRing twist) : ResidualRing twist :=
  ((first.1.1 * second.1.1 + twist * first.1.2 * second.2.1,
    first.1.1 * second.1.2 + first.1.2 * second.2.2),
    (first.2.1 * second.1.1 + first.2.2 * second.2.1,
      twist * first.2.1 * second.1.2 + first.2.2 * second.2.2))

instance residualRingMul (twist : ZMod 4) : Mul (ResidualRing twist) := ⟨residualMultiply twist⟩

instance residualRingRing (twist : ZMod 4) : Ring (ResidualRing twist) :=
  Ring.ofMinimalAxioms
    (by
      intro first second third
      change residualAdd (residualAdd first second) third = residualAdd first (residualAdd second third)
      apply Prod.ext <;> apply Prod.ext <;> simp only [residualAdd, add_assoc])
    (by
      intro element
      change residualAdd ((0, 0), (0, 0)) element = element
      apply Prod.ext <;> apply Prod.ext <;> simp only [residualAdd, zero_add])
    (by
      intro element
      change residualAdd ((-element.1.1, -element.1.2), (-element.2.1, -element.2.2)) element =
        ((0, 0), (0, 0))
      apply Prod.ext <;> apply Prod.ext <;> simp only [residualAdd, neg_add_cancel])
    (by
      rintro ⟨⟨firstA, firstB⟩, ⟨firstC, firstD⟩⟩ ⟨⟨secondA, secondB⟩, ⟨secondC, secondD⟩⟩
        ⟨⟨thirdA, thirdB⟩, ⟨thirdC, thirdD⟩⟩
      change residualMultiply twist (residualMultiply twist _ _) _ =
        residualMultiply twist _ (residualMultiply twist _ _)
      apply Prod.ext <;> apply Prod.ext <;> simp only [residualMultiply] <;> ring)
    (by
      rintro ⟨⟨firstA, firstB⟩, ⟨firstC, firstD⟩⟩
      change residualMultiply twist ((1, 0), (0, 1)) ((firstA, firstB), (firstC, firstD)) = _
      simp only [residualMultiply, one_mul, zero_mul, mul_zero, add_zero, zero_add]
      rfl)
    (by
      rintro ⟨⟨firstA, firstB⟩, ⟨firstC, firstD⟩⟩
      change residualMultiply twist ((firstA, firstB), (firstC, firstD)) ((1, 0), (0, 1)) = _
      simp only [residualMultiply, mul_one, mul_zero, add_zero, zero_add]
      rfl)
    (by
      rintro ⟨⟨firstA, firstB⟩, ⟨firstC, firstD⟩⟩ ⟨⟨secondA, secondB⟩, ⟨secondC, secondD⟩⟩
        ⟨⟨thirdA, thirdB⟩, ⟨thirdC, thirdD⟩⟩
      change residualMultiply twist _ (residualAdd _ _) =
        residualAdd (residualMultiply twist _ _) (residualMultiply twist _ _)
      apply Prod.ext <;> apply Prod.ext <;> dsimp only [residualMultiply, residualAdd] <;> ring)
    (by
      rintro ⟨⟨firstA, firstB⟩, ⟨firstC, firstD⟩⟩ ⟨⟨secondA, secondB⟩, ⟨secondC, secondD⟩⟩
        ⟨⟨thirdA, thirdB⟩, ⟨thirdC, thirdD⟩⟩
      change residualMultiply twist (residualAdd _ _) _ =
        residualAdd (residualMultiply twist _ _) (residualMultiply twist _ _)
      apply Prod.ext <;> apply Prod.ext <;> dsimp only [residualMultiply, residualAdd] <;> ring)

instance residualRingFintype (twist : ZMod 4) : Fintype (ResidualRing twist) :=
  inferInstanceAs (Fintype ((ZMod 4 × ZMod 4) × (ZMod 4 × ZMod 4)))

instance residualRingDecidableEq (twist : ZMod 4) : DecidableEq (ResidualRing twist) :=
  inferInstanceAs (DecidableEq ((ZMod 4 × ZMod 4) × (ZMod 4 × ZMod 4)))

@[expose] def residualDeterminant {twist : ZMod 4} (element : ResidualRing twist) : ZMod 4 :=
  element.1.1 * element.2.2 - twist * element.1.2 * element.2.1

theorem residualDeterminant_mul {twist : ZMod 4} (first second : ResidualRing twist) :
    residualDeterminant (first * second) = residualDeterminant first * residualDeterminant second := by
  rcases first with ⟨⟨firstA, firstB⟩, ⟨firstC, firstD⟩⟩
  rcases second with ⟨⟨secondA, secondB⟩, ⟨secondC, secondD⟩⟩
  change residualDeterminant (residualMultiply twist _ _) = _
  dsimp only [residualDeterminant, residualMultiply]
  ring

theorem residual_unit_determinant {twist : ZMod 4} (unit : (ResidualRing twist)ˣ) :
    residualDeterminant unit.val = 1 ∨ residualDeterminant unit.val = 3 := by
  have hproduct : residualDeterminant unit.val * residualDeterminant (unit⁻¹).val = 1 := by
    rw [← residualDeterminant_mul, Units.mul_inv]
    change (1 : ZMod 4) * 1 - twist * 0 * 0 = 1
    simp
  have hcases : ∀ first second : ZMod 4, first * second = 1 → first = 1 ∨ first = 3 := by decide
  exact hcases _ _ hproduct

abbrev ResidualUnitCandidates (twist : ZMod 4) := {element : ResidualRing twist //
  residualDeterminant element = 1 ∨ residualDeterminant element = 3}

@[expose] def residualUnitCandidate {twist : ZMod 4} (unit : (ResidualRing twist)ˣ) :
    ResidualUnitCandidates twist := ⟨unit.val, residual_unit_determinant unit⟩

theorem residualUnitCandidate_injective {twist : ZMod 4} :
    Function.Injective (residualUnitCandidate (twist := twist)) := by
  intro first second heq
  exact Units.ext (congrArg Subtype.val heq)

theorem residual_unit_card_even {twist : ZMod 4} (htwist : twist = 0 ∨ twist = 2) :
    Nat.card (ResidualRing twist)ˣ ≤ 64 := by
  have hcard := Nat.card_le_card_of_injective residualUnitCandidate
    (residualUnitCandidate_injective (twist := twist))
  have hcount : Nat.card (ResidualUnitCandidates twist) = 64 := by
    rcases htwist with rfl | rfl <;> rw [Nat.card_eq_fintype_card] <;> decide
  exact hcount ▸ hcard

@[expose] def residualInverse {twist : ZMod 4} (element : ResidualRing twist) : ResidualRing twist :=
  ((residualDeterminant element * element.2.2, -residualDeterminant element * element.1.2),
    (-residualDeterminant element * element.2.1, residualDeterminant element * element.1.1))

set_option maxRecDepth 10000 in
theorem residualUnitCandidate_surjective {twist : ZMod 4} :
    Function.Surjective (residualUnitCandidate (twist := twist)) := by
  intro candidate
  have hinverse : candidate.val * residualInverse candidate.val = 1 ∧
      residualInverse candidate.val * candidate.val = 1 := by
    have hcertificate : ∀ (coefficient : ZMod 4) (element : ResidualRing coefficient),
        (residualDeterminant element = 1 ∨ residualDeterminant element = 3) →
          element * residualInverse element = 1 ∧ residualInverse element * element = 1 := by
      decide
    exact hcertificate twist candidate.val candidate.property
  refine ⟨⟨candidate.val, residualInverse candidate.val, hinverse.1, hinverse.2⟩, ?_⟩
  apply Subtype.ext
  rfl

theorem residual_unit_card_one : Nat.card (ResidualRing 1)ˣ ≤ 96 := by
  have hcard := Nat.card_le_card_of_injective residualUnitCandidate
    (residualUnitCandidate_injective (twist := 1))
  have hcount : Nat.card (ResidualUnitCandidates 1) = 96 := by
    rw [Nat.card_eq_fintype_card]
    decide
  exact hcount ▸ hcard

theorem residual_unit_card_eq_even {twist : ZMod 4} (htwist : twist = 0 ∨ twist = 2) :
    Nat.card (ResidualRing twist)ˣ = 64 := by
  rw [Nat.card_congr (Equiv.ofBijective residualUnitCandidate
    ⟨residualUnitCandidate_injective, residualUnitCandidate_surjective⟩)]
  rcases htwist with rfl | rfl <;> rw [Nat.card_eq_fintype_card] <;> decide

theorem residual_unit_card_eq_one : Nat.card (ResidualRing 1)ˣ = 96 := by
  rw [Nat.card_congr (Equiv.ofBijective residualUnitCandidate
    ⟨residualUnitCandidate_injective, residualUnitCandidate_surjective⟩), Nat.card_eq_fintype_card]
  decide

abbrev ResidualInvolutionCandidates (twist : ZMod 4) := {element : ResidualRing twist //
  (residualDeterminant element = 1 ∨ residualDeterminant element = 3) ∧ element ^ 2 = 1}

theorem residual_involution_candidates_small {twist : ZMod 4} (htwist : twist = 0 ∨ twist = 2) :
    Nat.card (ResidualInvolutionCandidates twist) < 64 := by
  rcases htwist with rfl | rfl <;> rw [Nat.card_eq_fintype_card] <;> decide

universe groupUniverse

theorem two_group_card_lt_64_generator_rank {Ambient : Type groupUniverse} [Group Ambient]
    [Finite Ambient] (hpgroup : IsPGroup 2 Ambient) (hcard : Nat.card Ambient < 64) :
    pGeneratorRank 2 Ambient ≤ 5 := by
  obtain ⟨rank, hrankCard⟩ := hpgroup.exists_card_eq
  have hrank : rank ≤ 5 := by
    by_contra hlarge
    have hpower : 2 ^ 6 ≤ 2 ^ rank := Nat.pow_le_pow_right (by decide) (by omega)
    rw [← hrankCard] at hpower
    norm_num at hpower
    omega
  have hquotientCard := Nat.card_le_card_of_surjective (QuotientGroup.mk' (frattini Ambient))
    (QuotientGroup.mk'_surjective (frattini Ambient))
  unfold pGeneratorRank
  exact (Nat.log_mono_right hquotientCard).trans (by
    rw [hrankCard, Nat.log_pow (by decide : 1 < 2)]
    exact hrank)

theorem two_group_card_le_64_nontrivial_frattini_rank {Ambient : Type groupUniverse}
    [Group Ambient] [Finite Ambient] (hpgroup : IsPGroup 2 Ambient)
    (hcard : Nat.card Ambient ≤ 64) (hfrattini : frattini Ambient ≠ ⊥) :
    pGeneratorRank 2 Ambient ≤ 5 := by
  have hfrattiniCard : 2 ≤ Nat.card (frattini Ambient) := by
    have hpositive : 0 < Nat.card (frattini Ambient) := Nat.card_pos
    have hne : Nat.card (frattini Ambient) ≠ 1 := by
      intro hone
      exact hfrattini (Subgroup.card_eq_one.mp hone)
    omega
  have hformula := Subgroup.card_eq_card_quotient_mul_card_subgroup (frattini Ambient)
  have hquotientCard : Nat.card (Ambient ⧸ frattini Ambient) < 64 := by nlinarith
  have hlog : Nat.log 2 (Nat.card (Ambient ⧸ frattini Ambient)) ≤ 5 := by
    obtain ⟨rank, hrankCard⟩ := (hpgroup.to_quotient (frattini Ambient)).exists_card_eq
    rw [hrankCard, Nat.log_pow (by decide : 1 < 2)]
    by_contra hlarge
    have hpower : 2 ^ 6 ≤ 2 ^ rank := Nat.pow_le_pow_right (by decide) (by omega)
    rw [← hrankCard] at hpower
    norm_num at hpower
    omega
  exact hlog

theorem residual_even_two_subgroup_generator_rank {Acting : Type groupUniverse} [Group Acting]
    [Finite Acting] (hpgroup : IsPGroup 2 Acting) {twist : ZMod 4}
    (htwist : twist = 0 ∨ twist = 2) (embedding : Acting →* (ResidualRing twist)ˣ)
    (hinjective : Function.Injective embedding) : pGeneratorRank 2 Acting ≤ 5 := by
  have hcard : Nat.card Acting ≤ 64 :=
    (Nat.card_le_card_of_injective embedding hinjective).trans (residual_unit_card_even htwist)
  by_cases hfrattini : frattini Acting = ⊥
  · have hsquare : ∀ element : Acting, element ^ 2 = 1 := by
      intro element
      have hmem := pGroup_pow_mem_frattini Nat.prime_two hpgroup element
      rw [hfrattini] at hmem
      exact hmem
    let candidates : Acting → ResidualInvolutionCandidates twist := fun element =>
      ⟨(embedding element).val, residual_unit_determinant (embedding element), by
        have hzero : (embedding element) ^ 2 = 1 := by rw [← map_pow, hsquare, map_one]
        exact congrArg Units.val hzero⟩
    have hcandidates : Function.Injective candidates := by
      intro first second heq
      apply hinjective
      exact Units.ext (congrArg Subtype.val heq)
    have hsmall := (Nat.card_le_card_of_injective candidates hcandidates).trans_lt
      (residual_involution_candidates_small htwist)
    exact two_group_card_lt_64_generator_rank hpgroup hsmall
  · exact two_group_card_le_64_nontrivial_frattini_rank hpgroup hcard hfrattini

theorem residual_one_two_subgroup_generator_rank {Acting : Type groupUniverse} [Group Acting]
    [Finite Acting] (hpgroup : IsPGroup 2 Acting) (embedding : Acting →* (ResidualRing 1)ˣ)
    (hinjective : Function.Injective embedding) : pGeneratorRank 2 Acting ≤ 5 := by
  let equivalence := MonoidHom.ofInjective hinjective
  have hdivides : Nat.card Acting ∣ 96 := by
    rw [Nat.card_congr equivalence.toEquiv]
    exact (residual_unit_card_eq_one) ▸ embedding.range.card_subgroup_dvd_card
  obtain ⟨rank, hrankCard⟩ := hpgroup.exists_card_eq
  have hrank : rank ≤ 5 := by
    by_contra hlarge
    have hpower : 2 ^ 6 ∣ 2 ^ rank := Nat.pow_dvd_pow 2 (by omega)
    have hbad : 64 ∣ 96 := by rw [← hrankCard] at hpower; exact hpower.trans hdivides
    norm_num at hbad
  apply two_group_card_lt_64_generator_rank hpgroup
  rw [hrankCard]
  exact (Nat.pow_le_pow_right (by decide : 0 < 2) hrank).trans_lt (by decide)

theorem residual_binary_two_subgroup_generator_rank {Acting : Type groupUniverse} [Group Acting]
    [Finite Acting] (hpgroup : IsPGroup 2 Acting) {twist : ZMod 4}
    (htwist : twist = 1 ∨ twist = 0 ∨ twist = 2) (embedding : Acting →* (ResidualRing twist)ˣ)
    (hinjective : Function.Injective embedding) : pGeneratorRank 2 Acting ≤ 5 := by
  rcases htwist with rfl | heven
  · exact residual_one_two_subgroup_generator_rank hpgroup embedding hinjective
  · exact residual_even_two_subgroup_generator_rank hpgroup heven embedding hinjective

end CFSG.LargeEvenClassification.Helpers
