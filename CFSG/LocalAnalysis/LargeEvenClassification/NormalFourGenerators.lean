module

public import CFSG.LocalAnalysis.LargeEvenClassification.ConjugationGenerators
public import CFSG.LocalAnalysis.LargeEvenClassification.SmallActionGenerators

public section

namespace CFSG.LargeEvenClassification.Helpers

universe groupUniverse

def automorphismNonidentityPermutation {Ambient : Type groupUniverse} [Group Ambient] :
    MulAut Ambient →* Equiv.Perm {element : Ambient // element ≠ 1} := {
  toFun := fun automorphism => automorphism.toEquiv.subtypeEquiv
    (fun _ => automorphism.map_ne_one_iff.symm)
  map_one' := by ext element; rfl
  map_mul' := by intro first second; ext element; rfl }

theorem automorphismNonidentityPermutation_injective {Ambient : Type groupUniverse}
    [Group Ambient] : Function.Injective (automorphismNonidentityPermutation (Ambient := Ambient)) := by
  intro first second heq
  apply MulEquiv.ext
  intro element
  by_cases hone : element = 1
  · rw [hone, map_one, map_one]
  · exact congrArg (fun permutation : Equiv.Perm {entry : Ambient // entry ≠ 1} =>
      (permutation ⟨element, hone⟩ : Ambient)) heq

theorem two_group_four_aut_embedding_cyclic {Acting Normal : Type groupUniverse}
    [Group Acting] [Group Normal] [Finite Acting] [Finite Normal]
    (hpacting : IsPGroup 2 Acting) (hcard : Nat.card Normal = 4)
    (embedding : Acting →* MulAut Normal) (hinjective : Function.Injective embedding) :
    IsCyclic Acting := by
  classical
  let : Fintype Normal := Fintype.ofFinite Normal
  let permutationAction := automorphismNonidentityPermutation.comp embedding
  have hpermutationInjective : Function.Injective permutationAction :=
    automorphismNonidentityPermutation_injective.comp hinjective
  have hdivides := card_dvd_of_injective_hom permutationAction hpermutationInjective
  have hnonidentityCard : Fintype.card {element : Normal // element ≠ 1} = 3 := by
    have hformula := Fintype.card_subtype_compl (fun element : Normal => element = 1)
    have hfiniteCard : Fintype.card Normal = 4 := Nat.card_eq_fintype_card.symm.trans hcard
    rw [hfiniteCard] at hformula
    simpa using hformula
  rw [Nat.card_eq_fintype_card (α := Equiv.Perm {element : Normal // element ≠ 1}),
    Fintype.card_perm, hnonidentityCard] at hdivides
  norm_num at hdivides
  obtain ⟨rank, hrankCard⟩ := hpacting.exists_card_eq
  have hrank : rank ≤ 1 := by
    by_contra hlarge
    have hfour : 4 ∣ 6 := by
      have hpower : 2 ^ 2 ∣ 2 ^ rank := Nat.pow_dvd_pow 2 (by omega)
      rw [← hrankCard] at hpower
      exact hpower.trans hdivides
    norm_num at hfour
  apply card_le_two_cyclic
  rw [hrankCard]
  exact (Nat.pow_le_pow_right (by decide : 0 < 2) hrank).trans (by decide)

theorem abelian_normal_four_three_generators {Ambient : Type groupUniverse} [Group Ambient]
    [Finite Ambient] (hpgroup : IsPGroup 2 Ambient) (Normal : Subgroup Ambient) [Normal.Normal]
    (hcommutative : IsMulCommutative Normal) (hcard : Nat.card Normal = 4)
    (hselfCentralizing : Subgroup.centralizer (Normal : Set Ambient) = Normal)
    (SubgroupOfAmbient : Subgroup Ambient) :
    ∃ generators : Finset SubgroupOfAmbient,
      Subgroup.closure (generators : Set SubgroupOfAmbient) = ⊤ ∧ generators.card ≤ 3 := by
  let : CommGroup Normal := { (inferInstance : Group Normal) with
    mul_comm := @mul_comm' Normal _ hcommutative }
  have hnormalRank : pGeneratorRank 2 Normal ≤ 2 := by
    unfold pGeneratorRank
    have hquotientCard := Nat.card_le_card_of_surjective (QuotientGroup.mk' (frattini Normal))
      (QuotientGroup.mk'_surjective (frattini Normal))
    rw [hcard] at hquotientCard
    exact (Nat.log_mono_right (b := 2) hquotientCard).trans (by decide)
  let action := (MulAut.conjNormal (H := Normal)).comp SubgroupOfAmbient.subtype
  have hpaction := (hpgroup.to_subgroup SubgroupOfAmbient).of_surjective action.rangeRestrict
    action.rangeRestrict_surjective
  let : IsCyclic action.range := two_group_four_aut_embedding_cyclic hpaction hcard
    action.range.subtype Subtype.val_injective
  have hactionRank := cyclic_pGeneratorRank_le_one Nat.prime_two hpaction
  exact selfCentralizing_conj_subgroup_generator_bound Nat.prime_two hpgroup Normal hcommutative
    hselfCentralizing SubgroupOfAmbient hnormalRank hactionRank

end CFSG.LargeEvenClassification.Helpers
