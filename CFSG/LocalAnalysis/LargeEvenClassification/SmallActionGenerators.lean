module

public import CFSG.LocalAnalysis.LargeEvenClassification.AbelianGeneratorRank

public section

namespace CFSG.LargeEvenClassification.Helpers

universe groupUniverse targetUniverse

theorem card_le_two_cyclic {Ambient : Type groupUniverse} [Group Ambient] [Finite Ambient]
    (hcard : Nat.card Ambient ≤ 2) : IsCyclic Ambient := by
  have hpositive : 0 < Nat.card Ambient := Nat.card_pos
  have hcases : Nat.card Ambient = 1 ∨ Nat.card Ambient = 2 := by omega
  rcases hcases with hone | htwo
  · let : Subsingleton Ambient := (Nat.card_eq_one_iff_unique.mp hone).1
    infer_instance
  · let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact isCyclic_of_prime_card htwo

theorem cyclic_index_two_subgroup_generators {Ambient : Type groupUniverse} [Group Ambient]
    [Finite Ambient] (Cyclic : Subgroup Ambient) [Cyclic.Normal] [IsCyclic Cyclic]
    (hindex : Cyclic.index ≤ 2) (SubgroupOfAmbient : Subgroup Ambient) :
    ∃ generators : Finset SubgroupOfAmbient,
      Subgroup.closure (generators : Set SubgroupOfAmbient) = ⊤ ∧ generators.card ≤ 2 := by
  let projection := QuotientGroup.mk' Cyclic
  let restriction := projection.comp SubgroupOfAmbient.subtype
  let quotient := restriction.rangeRestrict
  let kernelEmbedding : quotient.ker →* Cyclic := {
    toFun := fun element => ⟨element.val.val, by
      have hzero := congrArg (fun entry : restriction.range =>
        (entry : Ambient ⧸ Cyclic)) element.property
      change (QuotientGroup.mk' Cyclic) element.val.val = 1 at hzero
      exact (QuotientGroup.eq_one_iff _).mp hzero⟩
    map_one' := rfl
    map_mul' := fun _ _ => rfl }
  have hkernelInjective : Function.Injective kernelEmbedding := by
    intro first second heq
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun entry : Cyclic => (entry : Ambient)) heq
  let : IsCyclic quotient.ker := isCyclic_of_injective kernelEmbedding hkernelInjective
  have himageCard : Nat.card restriction.range ≤ 2 := by
    have hle := restriction.range.card_le_card_group
    rw [← Cyclic.index_eq_card] at hle
    exact hle.trans hindex
  let : IsCyclic restriction.range := card_le_two_cyclic himageCard
  exact extension_generator_bound quotient restriction.rangeRestrict_surjective
    (cyclic_generators (Ambient := quotient.ker))
    (cyclic_generators (Ambient := restriction.range))

theorem cyclic_large_subgroup_two_generators {Ambient : Type groupUniverse} [Group Ambient]
    [Finite Ambient] (generator : Ambient) (hcard : Nat.card Ambient ≤ 2 * orderOf generator)
    (SubgroupOfAmbient : Subgroup Ambient) :
    ∃ generators : Finset SubgroupOfAmbient,
      Subgroup.closure (generators : Set SubgroupOfAmbient) = ⊤ ∧ generators.card ≤ 2 := by
  let Cyclic := Subgroup.zpowers generator
  have hpositive : 0 < Nat.card Cyclic := Nat.card_pos
  have hindex : Cyclic.index ≤ 2 := by
    have hformula := Cyclic.card_mul_index
    rw [show Nat.card Cyclic = orderOf generator from Nat.card_zpowers generator] at hpositive hformula
    nlinarith
  have hindexPositive : Cyclic.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hnormal : Cyclic.Normal := by
    have hcases : Cyclic.index = 1 ∨ Cyclic.index = 2 := by omega
    rcases hcases with hone | htwo
    · exact Subgroup.normal_of_index_eq_one hone
    · exact Subgroup.normal_of_index_eq_two htwo
  let := hnormal
  exact cyclic_index_two_subgroup_generators Cyclic hindex SubgroupOfAmbient

end CFSG.LargeEvenClassification.Helpers
