module

public import CFSG.Open.LocalVocabulary

public section

open CFSG.Open

namespace CFSG.PreuniquenessRankFour.Helpers

universe u v

theorem binary_units_has_cyclic_index_at_most_two (exponent : ℕ) :
    ∃ cyclic : Subgroup (ZMod (2 ^ exponent))ˣ, IsCyclic cyclic ∧ cyclic.index ≤ 2 := by
  rcases exponent with _ | _ | exponent
  · refine ⟨⊤, ?_, ?_⟩
    · let : IsCyclic (ZMod (2 ^ 0))ˣ := by simpa using ZMod.isCyclic_units_one
      infer_instance
    · simp
  · refine ⟨⊤, ?_, ?_⟩
    · let : IsCyclic (ZMod (2 ^ 1))ˣ := by simpa using ZMod.isCyclic_units_two
      infer_instance
    · simp
  have hunit : IsUnit (5 : ZMod (2 ^ (exponent + 2))) := by
    apply (ZMod.isUnit_iff_coprime 5 _).mpr
    exact (by norm_num : Nat.Coprime 5 2).pow_right _
  let generator := hunit.unit
  let cyclic := Subgroup.zpowers generator
  have hcard : Nat.card cyclic = 2 ^ exponent := by
    rw [Nat.card_zpowers, ← orderOf_units, hunit.unit_spec]
    exact ZMod.orderOf_five exponent
  have hactorCard : Nat.card (ZMod (2 ^ (exponent + 2)))ˣ = 2 * 2 ^ exponent := by
    rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient,
      Nat.totient_prime_pow (by norm_num : Nat.Prime 2) (by omega)]
    rw [show exponent + 2 - 1 = exponent + 1 by omega]
    simp only [Nat.reduceSub, pow_succ, mul_comm, one_mul]
  have hindex : cyclic.index = 2 := by
    have hproduct := cyclic.index_mul_card
    rw [hcard, hactorCard] at hproduct
    exact Nat.mul_right_cancel (by positivity : 0 < (2 : ℕ) ^ exponent) hproduct
  exact ⟨cyclic, inferInstance, hindex.le⟩

theorem injective_cyclic_index_at_most_two_has_cyclic_index_at_most_two
    {source : Type u} {target : Type v}
    [Group source] [Finite source] [Group target] [Finite target]
    (cyclic : Subgroup target) [IsCyclic cyclic] [cyclic.Normal]
    (hindex : cyclic.index ≤ 2) (hom : source →* target) (hinjective : Function.Injective hom) :
    ∃ preimage : Subgroup source, IsCyclic preimage ∧ preimage.index ≤ 2 := by
  let preimage := cyclic.comap hom
  let restriction : preimage →* cyclic :=
    { toFun := fun member => ⟨hom member, member.property⟩
      map_one' := Subtype.ext hom.map_one
      map_mul' := fun first second => Subtype.ext (hom.map_mul first second) }
  have hrestriction : Function.Injective restriction := by
    intro first second hequal
    apply Subtype.ext
    exact hinjective (congrArg Subtype.val hequal)
  have hpreimage : IsCyclic preimage := isCyclic_of_injective restriction hrestriction
  have hdivides : preimage.index ∣ cyclic.index := by
    rw [Subgroup.index_comap]
    exact cyclic.relIndex_dvd_index_of_normal hom.range
  exact ⟨preimage, hpreimage, (Nat.le_of_dvd (Subgroup.index_ne_zero_of_finite (H := cyclic) |> Nat.pos_of_ne_zero)
    hdivides).trans hindex⟩

theorem cyclic_twoGroup_aut_has_cyclic_index_at_most_two
    {source : Type u} [Group source] [Finite source]
    (hsource : IsPGroup 2 source) (hcyclic : IsCyclic source) :
    ∃ cyclic : Subgroup (MulAut source), IsCyclic cyclic ∧ cyclic.index ≤ 2 := by
  let : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  let : IsCyclic source := hcyclic
  obtain ⟨exponent, hcard⟩ := hsource.exists_card_eq
  obtain ⟨cyclic, hcyclic, hindex⟩ := binary_units_has_cyclic_index_at_most_two exponent
  let : IsCyclic cyclic := hcyclic
  let : cyclic.Normal := inferInstance
  let unitsEquiv := (IsCyclic.mulAutMulEquiv source).trans
    (Units.mapEquiv (ZMod.ringEquivCongr hcard).toMulEquiv)
  exact injective_cyclic_index_at_most_two_has_cyclic_index_at_most_two cyclic hindex
    unitsEquiv.toMonoidHom unitsEquiv.injective

theorem cyclic_group_rank_at_most_one
    {source : Type u} [Group source] [Finite source] [IsCyclic source] :
    Group.rank source ≤ 1 := by
  classical
  obtain ⟨generator, hgenerator⟩ := IsCyclic.exists_generator (α := source)
  have hclosure : Subgroup.closure ({generator} : Set source) = ⊤ := by
    rw [← Subgroup.zpowers_eq_closure]
    exact top_unique fun member _ => hgenerator member
  have hclosureFinset : Subgroup.closure (({generator} : Finset source) : Set source) = ⊤ := by
    simpa only [Finset.coe_singleton] using hclosure
  simpa only [Finset.card_singleton] using
    (Group.rank_le (S := {generator}) hclosureFinset)

theorem subgroup_rank_le_rank_add_quotient_rank
    {source : Type u} [Group source] [Finite source]
    (normal : Subgroup source) [normal.Normal] :
    Group.rank source ≤ Group.rank normal + Group.rank (source ⧸ normal) := by
  classical
  obtain ⟨normalGenerators, hnormalCard, hnormalGeneration⟩ := Group.rank_spec normal
  obtain ⟨quotientGenerators, hquotientCard, hquotientGeneration⟩ := Group.rank_spec (source ⧸ normal)
  let lift : (source ⧸ normal) → source :=
    fun member => Classical.choose (QuotientGroup.mk'_surjective normal member)
  have hlift : ∀ member, (QuotientGroup.mk' normal) (lift member) = member :=
    fun member => Classical.choose_spec (QuotientGroup.mk'_surjective normal member)
  let generators := normalGenerators.image normal.subtype ∪ quotientGenerators.image lift
  let generated := Subgroup.closure (generators : Set source)
  have hnormal : normal ≤ generated := by
    have hcomap : (⊤ : Subgroup normal) ≤ generated.comap normal.subtype := by
      rw [← hnormalGeneration]
      apply (Subgroup.closure_le _).mpr
      intro member hmember
      apply Subgroup.subset_closure
      exact Finset.mem_union_left _ (Finset.mem_image_of_mem _ hmember)
    intro member hmember
    exact hcomap (Subgroup.mem_top (⟨member, hmember⟩ : normal))
  have hquotient : generated.map (QuotientGroup.mk' normal) = ⊤ := by
    apply top_unique
    rw [← hquotientGeneration]
    apply (Subgroup.closure_le _).mpr
    intro member hmember
    refine ⟨lift member, ?_, hlift member⟩
    apply Subgroup.subset_closure
    exact Finset.mem_union_right _ (Finset.mem_image_of_mem _ hmember)
  have hgenerated : generated = ⊤ := by
    apply top_unique
    intro member _
    obtain ⟨representative, hrepresentative, hequal⟩ :=
      (show (QuotientGroup.mk' normal) member ∈ generated.map (QuotientGroup.mk' normal) from
        hquotient ▸ Subgroup.mem_top _)
    have hdifference : representative⁻¹ * member ∈ normal := by
      apply (QuotientGroup.eq_one_iff _).mp
      change (QuotientGroup.mk' normal) (representative⁻¹ * member) = 1
      rw [map_mul, map_inv, hequal, inv_mul_cancel]
    simpa only [mul_inv_cancel_left] using generated.mul_mem hrepresentative (hnormal hdifference)
  apply (Group.rank_le (S := generators) hgenerated).trans
  apply (Finset.card_union_le _ _).trans
  exact (Nat.add_le_add (Finset.card_image_le) (Finset.card_image_le)).trans
    (le_of_eq (congrArg₂ (· + ·) hnormalCard hquotientCard))

theorem cyclic_index_at_most_two_group_rank_at_most_two
    {source : Type u} [Group source] [Finite source]
    (cyclic : Subgroup source) [IsCyclic cyclic] [cyclic.Normal] (hindex : cyclic.index ≤ 2) :
    Group.rank source ≤ 2 := by
  have hquotientCard : Nat.card (source ⧸ cyclic) ≤ 2 := by
    rw [← cyclic.index_eq_card]
    exact hindex
  have hquotientCyclic : IsCyclic (source ⧸ cyclic) := by
    have hpositive : 0 < Nat.card (source ⧸ cyclic) := Nat.card_pos
    have hcards : Nat.card (source ⧸ cyclic) = 1 ∨ Nat.card (source ⧸ cyclic) = 2 := by omega
    rcases hcards with hone | htwo
    · let : Subsingleton (source ⧸ cyclic) := (Nat.card_eq_one_iff_unique.mp hone).1
      infer_instance
    · exact isCyclic_of_prime_card htwo
  let : IsCyclic (source ⧸ cyclic) := hquotientCyclic
  exact (subgroup_rank_le_rank_add_quotient_rank cyclic).trans
    (by have hfirst := cyclic_group_rank_at_most_one (source := cyclic)
        have hsecond := cyclic_group_rank_at_most_one (source := source ⧸ cyclic)
        omega)

theorem injective_cyclic_twoGroup_aut_group_rank_at_most_two
    {source : Type u} {acting : Type v}
    [Group source] [Finite source] [Group acting] [Finite acting]
    (hsource : IsPGroup 2 source) (hcyclic : IsCyclic source)
    (hom : acting →* MulAut source) (hinjective : Function.Injective hom) :
    Group.rank acting ≤ 2 := by
  let : IsCyclic source := hcyclic
  obtain ⟨cyclic, hcyclic, hindex⟩ := cyclic_twoGroup_aut_has_cyclic_index_at_most_two hsource hcyclic
  let : IsCyclic cyclic := hcyclic
  let unitsEquiv := IsCyclic.mulAutMulEquiv source
  let cyclicUnits := cyclic.map unitsEquiv.toMonoidHom
  let : IsCyclic cyclicUnits :=
    ((cyclic.equivMapOfInjective unitsEquiv.toMonoidHom unitsEquiv.injective).isCyclic).mp inferInstance
  have hcyclicUnits : cyclicUnits.index ≤ 2 := by
    change (cyclic.map unitsEquiv.toMonoidHom).index ≤ 2
    rw [show unitsEquiv.toMonoidHom = (unitsEquiv : MulAut source →* (ZMod (Nat.card source))ˣ) from rfl,
      Subgroup.index_map_equiv]
    exact hindex
  let : cyclicUnits.Normal := inferInstance
  obtain ⟨preimage, hpreimage, hpreimageIndex⟩ :=
    injective_cyclic_index_at_most_two_has_cyclic_index_at_most_two cyclicUnits hcyclicUnits
      (unitsEquiv.toMonoidHom.comp hom) (unitsEquiv.injective.comp hinjective)
  let : IsCyclic preimage := hpreimage
  let : IsMulCommutative acting := IsMulCommutative.of_comm fun first second =>
    (unitsEquiv.injective.comp hinjective) (by
      change (unitsEquiv.toMonoidHom.comp hom) (first * second) =
        (unitsEquiv.toMonoidHom.comp hom) (second * first)
      rw [map_mul, map_mul, mul_comm])
  let : preimage.Normal := inferInstance
  exact cyclic_index_at_most_two_group_rank_at_most_two preimage hpreimageIndex

end CFSG.PreuniquenessRankFour.Helpers
