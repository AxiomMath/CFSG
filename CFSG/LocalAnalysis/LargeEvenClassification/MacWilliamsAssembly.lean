module

public import CFSG.LocalAnalysis.LargeEvenClassification.MacWilliamsReduction
public import CFSG.LocalAnalysis.LargeEvenClassification.CyclicTwoFourGenerators
public import CFSG.LocalAnalysis.LargeEvenClassification.CyclicFourLarge
public import CFSG.LocalAnalysis.LargeEvenClassification.SmallCfourFourGenerators

public section

namespace CFSG.LargeEvenClassification.Helpers

theorem ambient_generators_of_subgroup_generators {S : Type*} [Group S]
    (U : Subgroup S) {bound : ℕ} (generators : Finset U)
    (hgenerates : Subgroup.closure (generators : Set U) = ⊤)
    (hcard : generators.card ≤ bound) :
    ∃ X : Finset S, X.card ≤ bound ∧ Subgroup.closure (X : Set S) = U := by
  classical
  refine ⟨generators.image U.subtype, Finset.card_image_le.trans hcard, ?_⟩
  rw [Finset.coe_image, ← MonoidHom.map_closure, hgenerates, Subgroup.map_top]
  exact U.range_subtype

theorem large_rank_two_exponent_cases {upper lower : ℕ}
    (hlower : 0 < lower) (hordered : lower ≤ upper) (hlarge : 4 ≤ upper + lower) :
    (lower = 1 ∧ 3 ≤ upper) ∨ 3 ≤ lower ∨ (lower = 2 ∧ 4 ≤ upper) ∨
      (upper = 2 ∧ lower = 2) ∨ (upper = 3 ∧ lower = 2) := by
  omega

section C8FourBoundary

variable {S : Type*} [Group S] [Finite S]
variable (hpgroup : IsPGroup 2 S)
variable (hnoEight : ∀ E : Subgroup S, E.Normal → CFSG.Open.IsElemAbelian 2 E → Nat.card E ≠ 8)
variable (c8Four : ∀ (A : Subgroup S) [A.Normal],
    IsMulCommutative A → Subgroup.centralizer (A : Set S) = A →
    (Additive A ≃+ (ZMod 8 × ZMod 4)) →
    ∀ U : Subgroup S, ∃ X : Finset U, Subgroup.closure (X : Set U) = ⊤ ∧ X.card ≤ 4)

include hpgroup hnoEight c8Four in
theorem rank_two_large_four_generators_of_c8_four (A : Subgroup S) [A.Normal]
    (hcommutative : IsMulCommutative A)
    (hselfCentralizing : Subgroup.centralizer (A : Set S) = A)
    {upper lower : ℕ} (hlower : 0 < lower) (hordered : lower ≤ upper)
    (hlarge : 4 ≤ upper + lower)
    (coordinates : A ≃* Multiplicative (ZMod (2 ^ upper)) ×
      Multiplicative (ZMod (2 ^ lower))) (U : Subgroup S) :
    ∃ X : Finset U, Subgroup.closure (X : Set U) = ⊤ ∧ X.card ≤ 4 := by
  let : CommGroup A := { (inferInstance : Group A) with
    mul_comm := @mul_comm' A _ hcommutative }
  rcases large_rank_two_exponent_cases hlower hordered hlarge with
    ⟨rfl, hupper⟩ | hlowerLarge | ⟨rfl, hupper⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · have converted : A ≃* Multiplicative (ZMod (2 ^ (upper - 3 + 3))) ×
        Multiplicative (ZMod 2) := by
      rw [Nat.sub_add_cancel hupper]
      exact coordinates
    exact rank_two_cyclic_times_two_four_generators hpgroup A hcommutative
      hselfCentralizing hnoEight (upper - 3) converted U
  · exact rank_two_large_exponent_four_generators hpgroup A hcommutative
      hselfCentralizing hnoEight upper lower hordered hlowerLarge coordinates U
  · have converted : A ≃* Multiplicative (ZMod (2 ^ (upper - 4 + 4))) ×
        Multiplicative (ZMod 4) := by
      rw [Nat.sub_add_cancel hupper]
      exact coordinates
    exact rank_two_cyclic_times_four_large_four_generators hpgroup A hcommutative
      hselfCentralizing hnoEight (upper - 4) converted U
  · exact small_cfour_four_generators hpgroup A hcommutative hselfCentralizing
      hnoEight (rankTwoAddCoordinates coordinates) U
  · exact c8Four A hcommutative hselfCentralizing (rankTwoAddCoordinates coordinates) U

include hpgroup hnoEight c8Four in
theorem rank_two_large_ambient_four_generators_of_c8_four (A : Subgroup S) [A.Normal]
    (hcommutative : IsMulCommutative A)
    (hselfCentralizing : Subgroup.centralizer (A : Set S) = A)
    {upper lower : ℕ} (hlower : 0 < lower) (hordered : lower ≤ upper)
    (hlarge : 4 ≤ upper + lower)
    (coordinates : A ≃* Multiplicative (ZMod (2 ^ upper)) ×
      Multiplicative (ZMod (2 ^ lower))) (U : Subgroup S) :
    ∃ X : Finset S, X.card ≤ 4 ∧ Subgroup.closure (X : Set S) = U := by
  obtain ⟨X, hX, hcard⟩ := rank_two_large_four_generators_of_c8_four hpgroup hnoEight c8Four
    A hcommutative hselfCentralizing hlower hordered hlarge coordinates U
  exact ambient_generators_of_subgroup_generators U X hX hcard

include hpgroup hnoEight c8Four in
theorem macwilliams_four_generators_of_c8_four :
    ∀ U : Subgroup S, ∃ X : Finset S, X.card ≤ 4 ∧ Subgroup.closure (X : Set S) = U := by
  obtain ⟨A, hnormal, hcommutative, hmaximal⟩ := exists_maximal_abelian_normal (Ambient := S)
  let : A.Normal := hnormal
  let : CommGroup A := { (inferInstance : Group A) with
    mul_comm := @mul_comm' A _ hcommutative }
  have hselfCentralizing := maximal_abelian_normal_selfCentralizing Nat.prime_two hpgroup
    A hcommutative hmaximal
  obtain ⟨normalGenerators, hnormalGenerates, hnormalCard⟩ :=
    no_normal_eight_abelian_normal_two_generators hpgroup hnoEight A hcommutative
  have hnormalRank := (pGeneratorRank_le_generators Nat.prime_two
    (hpgroup.to_subgroup A) normalGenerators hnormalGenerates).trans hnormalCard
  rcases commutative_pGroup_rank_two_coordinates Nat.prime_two (hpgroup.to_subgroup A)
      hnormalRank with hcyclic | ⟨upper, lower, hlower, hordered, ⟨coordinates⟩⟩
  · let : IsCyclic A := hcyclic
    intro U
    obtain ⟨X, hX, hcard⟩ := cyclic_maximal_abelian_normal_three_generators hpgroup A hmaximal U
    exact ambient_generators_of_subgroup_generators U X hX (hcard.trans (by decide))
  · intro U
    by_cases hsmall : upper + lower ≤ 3
    · obtain ⟨X, hX, hcard⟩ := small_rank_two_selfCentralizing_four_generators
        hpgroup A hlower hordered hsmall coordinates hselfCentralizing U
      exact ambient_generators_of_subgroup_generators U X hX hcard
    · exact rank_two_large_ambient_four_generators_of_c8_four hpgroup hnoEight c8Four
        A hcommutative hselfCentralizing hlower hordered (by omega) coordinates U

end C8FourBoundary

end CFSG.LargeEvenClassification.Helpers
