module

public import CFSG.LocalAnalysis.LargeEvenClassification.SmallActionGenerators
public import CFSG.LocalAnalysis.LargeEvenClassification.CyclicNormObstruction
public import CFSG.LocalAnalysis.LargeEvenClassification.CyclicScalarNorm

public section

open CFSG.Open

namespace CFSG.LargeEvenClassification.Helpers

universe groupUniverse

theorem rank_one_cyclic_action_excludes_congruence_involution {Ambient : Type groupUniverse}
    [Group Ambient] [Finite Ambient] (hpgroup : IsPGroup 2 Ambient) (hrank : twoRank Ambient ≤ 1)
    (Normal : Subgroup Ambient) [Normal.Normal] [IsCyclic Normal]
    (hselfCentralizing : Subgroup.centralizer (Normal : Set Ambient) = Normal)
    (exponent : ℕ) (coordinates : Multiplicative (ZMod (2 ^ (exponent + 3))) ≃* Normal) :
    binaryCongruenceInvolution exponent ∉
      ((cyclicScalarAutEquiv (2 ^ (exponent + 3)) coordinates).toMonoidHom.comp
        (MulAut.conjNormal (H := Normal))).range := by
  let action := (cyclicScalarAutEquiv (2 ^ (exponent + 3)) coordinates).toMonoidHom.comp
    (MulAut.conjNormal (H := Normal))
  intro hinRange
  obtain ⟨element, hscalar⟩ := hinRange
  change (cyclicScalarAutEquiv (2 ^ (exponent + 3)) coordinates) (MulAut.conjNormal element) =
    binaryCongruenceInvolution exponent at hscalar
  have hactionKernel : action.ker = Normal := by
    have heq := MonoidHom.ker_comp_of_injective (MulAut.conjNormal (H := Normal))
      (cyclicScalarAutEquiv (2 ^ (exponent + 3)) coordinates).toMonoidHom
        (cyclicScalarAutEquiv (2 ^ (exponent + 3)) coordinates).injective
    change action.ker = (MulAut.conjNormal (H := Normal)).ker at heq
    exact heq.trans ((conjNormal_ker_eq_centralizer Normal).trans hselfCentralizing)
  have helementNe : element ∉ Normal := by
    intro helement
    have hone : action element = 1 := hactionKernel.symm.le helement
    change (cyclicScalarAutEquiv (2 ^ (exponent + 3)) coordinates) (MulAut.conjNormal element) = 1 at hone
    exact binaryCongruenceInvolution_ne_one exponent (hscalar.symm.trans hone)
  have hsquare : element ^ 2 ∈ Normal := by
    apply hactionKernel.le
    change action (element ^ 2) = 1
    rw [map_pow]
    change ((cyclicScalarAutEquiv (2 ^ (exponent + 3)) coordinates) (MulAut.conjNormal element)) ^ 2 = 1
    rw [hscalar, binaryCongruenceInvolution_sq]
  let : CommGroup Normal := IsCyclic.commGroup
  apply rank_one_cyclic_norm_obstruction hpgroup hrank Normal hselfCentralizing element helementNe hsquare
  · intro source hfixed
    apply cyclic_congruence_fixed_square (Cyclic := Normal) exponent coordinates
      (MulAut.conjNormal element) hscalar source
    apply Subtype.ext
    exact hfixed
  · intro square
    obtain ⟨source, hnorm⟩ := cyclic_congruence_norm_surjective exponent coordinates
      (MulAut.conjNormal element) hscalar square
    exact ⟨source, congrArg (fun entry : Normal => entry.val) hnorm⟩

theorem binary_congruence_kernel_card (exponent : ℕ) :
    Nat.card (ZMod.unitsMap (show 4 ∣ 2 ^ (exponent + 3) from by
      rw [show exponent + 3 = 2 + (exponent + 1) by omega, pow_add]
      exact dvd_mul_right _ _)).ker = 2 ^ (exponent + 1) := by
  let : NeZero (2 ^ (exponent + 3)) := ⟨by positivity⟩
  let divides : 4 ∣ 2 ^ (exponent + 3) := by
    rw [show exponent + 3 = 2 + (exponent + 1) by omega, pow_add]
    exact dvd_mul_right _ _
  let reduction := ZMod.unitsMap divides
  have hsurjective : Function.Surjective reduction := ZMod.unitsMap_surjective divides
  have hformula := Subgroup.card_eq_card_quotient_mul_card_subgroup reduction.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective reduction hsurjective).toEquiv] at hformula
  have hsourceCard : Nat.card (ZMod (2 ^ (exponent + 3)))ˣ = 2 ^ (exponent + 2) := binary_unit_card (exponent + 2)
  have htargetCard : Nat.card (ZMod 4)ˣ = 2 := by
    rw [Nat.card_eq_fintype_card]
    decide
  rw [hsourceCard, htargetCard] at hformula
  have hpower : 2 ^ (exponent + 2) = 2 * 2 ^ (exponent + 1) := by
    simp only [pow_succ']
  rw [hpower] at hformula
  exact Nat.eq_of_mul_eq_mul_left (by decide : 0 < 2) hformula.symm

theorem binary_congruence_subgroup_excludes_involution {exponent : ℕ}
    (Action : Subgroup (ZMod (2 ^ (exponent + 3)))ˣ)
    (hexcludes : binaryCongruenceInvolution exponent ∉ Action) :
    Disjoint Action (ZMod.unitsMap (show 4 ∣ 2 ^ (exponent + 3) from by
      rw [show exponent + 3 = 2 + (exponent + 1) by omega, pow_add]
      exact dvd_mul_right _ _)).ker := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : NeZero (2 ^ (exponent + 3)) := ⟨by positivity⟩
  let divides : 4 ∣ 2 ^ (exponent + 3) := by
    rw [show exponent + 3 = 2 + (exponent + 1) by omega, pow_add]
    exact dvd_mul_right _ _
  let Congruence := (ZMod.unitsMap divides).ker
  let Intersection := Action ⊓ Congruence
  have hcongruenceCyclic : IsCyclic Congruence := binary_unit_mod_four_kernel_cyclic (exponent + 1)
  let := hcongruenceCyclic
  have hcongruenceCard : Nat.card Congruence = 2 ^ (exponent + 1) := binary_congruence_kernel_card exponent
  have hcongruenceGroup : IsPGroup 2 Congruence := IsPGroup.of_card hcongruenceCard
  apply disjoint_iff.mpr
  apply le_antisymm _ bot_le
  by_contra hnotLe
  have hintersectionNe : Intersection ≠ ⊥ := fun hzero => hnotLe (le_of_eq hzero)
  have hintersectionGroup : IsPGroup 2 Intersection := hcongruenceGroup.to_le inf_le_right
  obtain hcardOne | htwoDivides := hintersectionGroup.card_eq_or_dvd
  · exact hintersectionNe (Subgroup.card_eq_one.mp hcardOne)
  · obtain ⟨internalInvolution, horder⟩ := exists_prime_orderOf_dvd_card' 2 htwoDivides
    let Involution := (⟨internalInvolution.val, internalInvolution.property.2⟩ : Congruence)
    let Standard := (⟨binaryCongruenceInvolution exponent, binaryCongruenceInvolution_mod_four exponent⟩ : Congruence)
    have hinvolutionOrder : orderOf Involution = 2 := by
      have heq := orderOf_injective (Subgroup.inclusion (show Intersection ≤ Congruence from inf_le_right))
        (Subgroup.inclusion_injective _) internalInvolution
      exact heq.trans horder
    have hstandardOrder : orderOf Standard = 2 := by
      apply orderOf_eq_prime_iff.mpr
      constructor
      · apply Subtype.ext
        exact binaryCongruenceInvolution_sq exponent
      · intro hone
        exact binaryCongruenceInvolution_ne_one exponent (congrArg Subtype.val hone)
    have heq := cyclic_two_group_involutions_unique Involution Standard hinvolutionOrder hstandardOrder
    apply hexcludes
    have hvalEq := congrArg (fun entry : Congruence => entry.val) heq
    change internalInvolution.val = binaryCongruenceInvolution exponent at hvalEq
    exact hvalEq ▸ internalInvolution.property.1

theorem rank_one_self_centralizing_cyclic_index_two {Ambient : Type groupUniverse}
    [Group Ambient] [Finite Ambient] (hpgroup : IsPGroup 2 Ambient) (hrank : twoRank Ambient ≤ 1)
    (Normal : Subgroup Ambient) [Normal.Normal] [IsCyclic Normal]
    (hselfCentralizing : Subgroup.centralizer (Normal : Set Ambient) = Normal) :
    Normal.index ≤ 2 := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hconjugationKernel : (MulAut.conjNormal (H := Normal)).ker = Normal :=
    (conjNormal_ker_eq_centralizer Normal).trans hselfCentralizing
  obtain ⟨normalRank, hnormalCard⟩ := (hpgroup.to_subgroup Normal).exists_card_eq
  by_cases hsmall : normalRank ≤ 2
  · have hautomorphismCard : Nat.card (MulAut Normal) ≤ 2 := by
      rw [IsCyclic.card_mulAut, hnormalCard]
      interval_cases normalRank
      · norm_num
      · norm_num
      · decide
    rw [← hconjugationKernel, Subgroup.index_ker]
    exact (MulAut.conjNormal (H := Normal)).range.card_le_card_group.trans hautomorphismCard
  · obtain ⟨exponent, hrankEq⟩ : ∃ exponent, normalRank = exponent + 3 :=
      ⟨normalRank - 3, by omega⟩
    rw [hrankEq] at hnormalCard
    let coordinates : Multiplicative (ZMod (2 ^ (exponent + 3))) ≃* Normal := by
      rw [← hnormalCard]
      exact zmodCyclicMulEquiv (inferInstance : IsCyclic Normal)
    let action := (cyclicScalarAutEquiv (2 ^ (exponent + 3)) coordinates).toMonoidHom.comp
      (MulAut.conjNormal (H := Normal))
    have hexcludes : binaryCongruenceInvolution exponent ∉ action.range :=
      rank_one_cyclic_action_excludes_congruence_involution hpgroup hrank Normal hselfCentralizing
        exponent coordinates
    let divides : 4 ∣ 2 ^ (exponent + 3) := by
      rw [show exponent + 3 = 2 + (exponent + 1) by omega, pow_add]
      exact dvd_mul_right _ _
    let reduction := ZMod.unitsMap divides
    have hdisjoint : Disjoint action.range reduction.ker :=
      binary_congruence_subgroup_excludes_involution action.range hexcludes
    let restricted := reduction.comp action.range.subtype
    have hrestrictedInjective : Function.Injective restricted := by
      apply (MonoidHom.ker_eq_bot_iff restricted).mp
      apply le_antisymm _ bot_le
      intro scalar hscalar
      apply Subgroup.mem_bot.mpr
      apply Subtype.ext
      exact Subgroup.disjoint_def.mp hdisjoint scalar.property hscalar
    have hcardRange : Nat.card action.range ≤ 2 := by
      have hbound := Nat.card_le_card_of_injective restricted hrestrictedInjective
      have htargetCard : Nat.card (ZMod 4)ˣ = 2 := by
        rw [Nat.card_eq_fintype_card]
        decide
      exact hbound.trans_eq htargetCard
    have hactionKernel : action.ker = Normal :=
      (MonoidHom.ker_comp_of_injective (MulAut.conjNormal (H := Normal))
        (cyclicScalarAutEquiv (2 ^ (exponent + 3)) coordinates).toMonoidHom
          (cyclicScalarAutEquiv (2 ^ (exponent + 3)) coordinates).injective).trans hconjugationKernel
    rw [← hactionKernel, Subgroup.index_ker]
    exact hcardRange

theorem rank_one_two_group_two_generators {Ambient : Type groupUniverse} [Group Ambient]
    [Finite Ambient] (hpgroup : IsPGroup 2 Ambient) (hrank : twoRank Ambient ≤ 1)
    (Candidate : Subgroup Ambient) :
    ∃ generators : Finset Candidate,
      Subgroup.closure (generators : Set Candidate) = ⊤ ∧ generators.card ≤ 2 := by
  obtain ⟨Normal, hnormal, hcyclic, hselfCentralizing⟩ :=
    rank_one_two_group_abelian_normal_cyclic hpgroup hrank
  let := hnormal
  let := hcyclic
  exact cyclic_index_two_subgroup_generators Normal
    (rank_one_self_centralizing_cyclic_index_two hpgroup hrank Normal hselfCentralizing) Candidate

theorem rank_one_two_group_generator_rank_le_two {Ambient : Type groupUniverse} [Group Ambient]
    [Finite Ambient] (hpgroup : IsPGroup 2 Ambient) (hrank : twoRank Ambient ≤ 1) :
    pGeneratorRank 2 Ambient ≤ 2 := by
  obtain ⟨generators, hgenerates, hcard⟩ := rank_one_two_group_two_generators hpgroup hrank ⊤
  have hbound : pGeneratorRank 2 (⊤ : Subgroup Ambient) ≤ 2 :=
    (pGeneratorRank_le_generators Nat.prime_two (hpgroup.to_subgroup ⊤) generators hgenerates).trans hcard
  rw [← pGeneratorRank_mulEquiv Nat.prime_two hpgroup Subgroup.topEquiv.symm] at hbound
  exact hbound

end CFSG.LargeEvenClassification.Helpers
