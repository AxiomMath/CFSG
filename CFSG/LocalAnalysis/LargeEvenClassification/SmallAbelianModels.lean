module

public import CFSG.LocalAnalysis.LargeEvenClassification.ConjugationGenerators
public import CFSG.LocalAnalysis.LargeEvenClassification.SmallActionGenerators

public section

namespace CFSG.LargeEvenClassification.Helpers

universe groupUniverse targetUniverse

abbrev FourTwo := Multiplicative (ZMod 4) × Multiplicative (ZMod 2)

def fourTwoFirst : FourTwo := (Multiplicative.ofAdd 1, 1)

def fourTwoSecond : FourTwo := (1, Multiplicative.ofAdd 1)

theorem fourTwo_coordinates : ∀ element : FourTwo,
    ∃ first : Fin 4, ∃ second : Fin 2,
      fourTwoFirst ^ first.val * fourTwoSecond ^ second.val = element := by
  decide

theorem fourTwo_generators :
    Subgroup.closure ({fourTwoFirst, fourTwoSecond} : Set FourTwo) = ⊤ := by
  apply top_unique
  intro element _
  obtain ⟨first, second, rfl⟩ := fourTwo_coordinates element
  exact Subgroup.mul_mem _
    (Subgroup.pow_mem _ (Subgroup.subset_closure (by simp)) _)
    (Subgroup.pow_mem _ (Subgroup.subset_closure (by simp)) _)

theorem fourTwo_generator_rank : pGeneratorRank 2 FourTwo ≤ 2 := by
  have hpgroup : IsPGroup 2 FourTwo := by
    apply IsPGroup.of_card (n := 3)
    rw [Nat.card_eq_fintype_card]
    decide
  have hgenerates : Subgroup.closure (({fourTwoFirst, fourTwoSecond} : Finset FourTwo) :
      Set FourTwo) = ⊤ := by simpa using fourTwo_generators
  exact (pGeneratorRank_le_generators Nat.prime_two hpgroup _ hgenerates).trans (by decide)

theorem fourTwo_isPGroup : IsPGroup 2 FourTwo := by
  apply IsPGroup.of_card (n := 3)
  rw [Nat.card_eq_fintype_card]
  decide

def fourTwoRotate (element : FourTwo) : FourTwo :=
  (Multiplicative.ofAdd (element.1.toAdd + 2 * (element.2.toAdd.val : ZMod 4)),
    Multiplicative.ofAdd ((element.1.toAdd.val : ZMod 2) + element.2.toAdd))

def fourTwoRotation : MulAut FourTwo := {
  toFun := fourTwoRotate
  invFun := fun element => fourTwoRotate (fourTwoRotate (fourTwoRotate element))
  left_inv := by decide
  right_inv := by decide
  map_mul' := by decide }

theorem fourTwo_rotation_order : orderOf fourTwoRotation = 4 := by
  apply (orderOf_eq_iff (by decide : 0 < 4)).mpr
  constructor
  · decide
  · intro exponent hless hpositive
    interval_cases exponent <;> decide

abbrev FourTwoAutomorphismPairs := { pair : FourTwo × FourTwo //
  pair.1 ^ 4 = 1 ∧ pair.1 ^ 2 ≠ 1 ∧ pair.2 ^ 2 = 1 ∧ pair.2 ≠ 1 ∧ pair.2 ≠ pair.1 ^ 2 }

theorem fourTwo_automorphism_pairs_card : Nat.card FourTwoAutomorphismPairs = 8 := by
  rw [Nat.card_eq_fintype_card]
  decide

def fourTwoAutomorphismPair (automorphism : MulAut FourTwo) : FourTwoAutomorphismPairs :=
  ⟨(automorphism fourTwoFirst, automorphism fourTwoSecond), by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [← map_pow, show fourTwoFirst ^ 4 = 1 from by decide, map_one]
    · intro heq
      have hzero : automorphism (fourTwoFirst ^ 2) = automorphism 1 := by
        simpa only [map_pow, map_one] using heq
      exact (by decide : fourTwoFirst ^ 2 ≠ 1) (automorphism.injective hzero)
    · rw [← map_pow, show fourTwoSecond ^ 2 = 1 from by decide, map_one]
    · intro heq
      exact (by decide : fourTwoSecond ≠ 1)
        (automorphism.injective (heq.trans (map_one automorphism).symm))
    · intro heq
      have hequal : automorphism fourTwoSecond = automorphism (fourTwoFirst ^ 2) := by
        simpa only [map_pow] using heq
      exact (by decide : fourTwoSecond ≠ fourTwoFirst ^ 2) (automorphism.injective hequal)⟩

theorem fourTwoAutomorphismPair_injective : Function.Injective fourTwoAutomorphismPair := by
  intro first second heq
  have hpairs := congrArg (fun pair : FourTwoAutomorphismPairs => pair.val) heq
  apply MulEquiv.toMonoidHom_injective
  apply MonoidHom.eq_of_eqOn_dense fourTwo_generators
  intro element helement
  rcases helement with rfl | rfl
  · exact congrArg Prod.fst hpairs
  · exact congrArg Prod.snd hpairs

theorem fourTwo_automorphism_card_le : Nat.card (MulAut FourTwo) ≤ 8 := by
  have hcard := Nat.card_le_card_of_injective fourTwoAutomorphismPair
    fourTwoAutomorphismPair_injective
  rwa [fourTwo_automorphism_pairs_card] at hcard

theorem fourTwo_automorphism_subgroup_two_generators (Action : Subgroup (MulAut FourTwo)) :
    ∃ generators : Finset Action, Subgroup.closure (generators : Set Action) = ⊤ ∧
      generators.card ≤ 2 := by
  apply cyclic_large_subgroup_two_generators fourTwoRotation _ Action
  rw [fourTwo_rotation_order]
  exact fourTwo_automorphism_card_le

theorem fourTwo_automorphism_embedding_generator_rank {Acting : Type groupUniverse}
    [Group Acting] [Finite Acting] (hpacting : IsPGroup 2 Acting)
    (embedding : Acting →* MulAut FourTwo) (hinjective : Function.Injective embedding) :
    pGeneratorRank 2 Acting ≤ 2 := by
  let equivalence := MonoidHom.ofInjective hinjective
  rw [pGeneratorRank_mulEquiv Nat.prime_two hpacting equivalence]
  obtain ⟨generators, hgenerates, hcard⟩ :=
    fourTwo_automorphism_subgroup_two_generators embedding.range
  have hpimage := hpacting.of_surjective embedding.rangeRestrict embedding.rangeRestrict_surjective
  exact (pGeneratorRank_le_generators Nat.prime_two hpimage generators hgenerates).trans hcard

theorem fourTwo_selfCentralizing_four_generators {Ambient : Type groupUniverse} [Group Ambient]
    [Finite Ambient] (hpgroup : IsPGroup 2 Ambient) (Normal : Subgroup Ambient) [Normal.Normal]
    (equivalence : Normal ≃* FourTwo)
    (hselfCentralizing : Subgroup.centralizer (Normal : Set Ambient) = Normal)
    (SubgroupOfAmbient : Subgroup Ambient) :
    ∃ generators : Finset SubgroupOfAmbient,
      Subgroup.closure (generators : Set SubgroupOfAmbient) = ⊤ ∧ generators.card ≤ 4 := by
  have hcommutative : IsMulCommutative Normal := by
    apply isMulCommutative_iff.mpr
    intro first second
    apply equivalence.injective
    rw [map_mul, map_mul, mul_comm]
  have hnormalRank : pGeneratorRank 2 Normal ≤ 2 := by
    rw [pGeneratorRank_mulEquiv Nat.prime_two (hpgroup.to_subgroup Normal) equivalence]
    exact fourTwo_generator_rank
  let action := (MulAut.conjNormal (H := Normal)).comp SubgroupOfAmbient.subtype
  let actionEquivalence := MulAut.congr equivalence
  let embedding := actionEquivalence.toMonoidHom.comp action.range.subtype
  have hinjective : Function.Injective embedding :=
    actionEquivalence.injective.comp Subtype.val_injective
  have hpaction := (hpgroup.to_subgroup SubgroupOfAmbient).of_surjective action.rangeRestrict
    action.rangeRestrict_surjective
  have hactionRank := fourTwo_automorphism_embedding_generator_rank hpaction embedding hinjective
  exact selfCentralizing_conj_subgroup_generator_bound Nat.prime_two hpgroup Normal hcommutative
    hselfCentralizing SubgroupOfAmbient hnormalRank hactionRank

end CFSG.LargeEvenClassification.Helpers
