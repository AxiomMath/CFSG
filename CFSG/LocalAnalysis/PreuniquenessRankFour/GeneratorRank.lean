module

public import CFSG.LocalAnalysis.PreuniquenessRankFour.BinaryRank
public import CFSG.LocalAnalysis.PreuniquenessRankFour.CriticalCentralizer
public import CFSG.LocalAnalysis.PreuniquenessRankFour.BinaryUnits

public section

open CFSG.Open

namespace CFSG.PreuniquenessRankFour.Helpers

universe u v

theorem binary_module_finrank_le_group_rank
    {source : Type u} [CommGroup source] [Finite source]
    [Module (ZMod 2) (Additive source)] :
    Module.finrank (ZMod 2) (Additive source) ≤ Group.rank source := by
  classical
  obtain ⟨generators, hcard, hgeneration⟩ := Group.rank_spec source
  let vectors := generators.image (Additive.ofMul : source → Additive source)
  let span := Submodule.span (ZMod 2) (vectors : Set (Additive source))
  have hclosure : Subgroup.closure (generators : Set source) ≤ span.toAddSubgroup.toSubgroup' := by
    apply (Subgroup.closure_le _).mpr
    intro member hmember
    change Additive.ofMul member ∈ span
    exact Submodule.subset_span (Finset.mem_image_of_mem _ hmember)
  have hspan : span = ⊤ := by
    apply Submodule.eq_top_iff'.mpr
    intro member
    exact hclosure (hgeneration ▸ Subgroup.mem_top member.toMul)
  have hdimension := finrank_span_finset_le_card (R := ZMod 2) vectors
  change Module.finrank (ZMod 2) span ≤ vectors.card at hdimension
  rw [hspan, finrank_top] at hdimension
  exact hdimension.trans (Finset.card_image_le.trans hcard.le)

theorem binary_module_group_rank_le_finrank
    {source : Type u} [CommGroup source] [Finite source]
    [Module (ZMod 2) (Additive source)] :
    Group.rank source ≤ Module.finrank (ZMod 2) (Additive source) := by
  classical
  let basis := Module.finBasis (ZMod 2) (Additive source)
  let generators := Finset.univ.image (fun index => (basis index).toMul)
  let generated := Subgroup.closure (generators : Set source)
  let submodule := (AddSubgroup.toZModSubmodule 2) generated.toAddSubgroup
  have hbasis : Submodule.span (ZMod 2) (Set.range basis) ≤ submodule := by
    apply Submodule.span_le.mpr
    rintro member ⟨index, rfl⟩
    change (basis index).toMul ∈ generated
    apply Subgroup.subset_closure
    exact Finset.mem_image_of_mem _ (Finset.mem_univ index)
  have hgenerated : generated = ⊤ := by
    apply top_unique
    intro member _
    have hspan : Additive.ofMul member ∈ Submodule.span (ZMod 2) (Set.range basis) :=
      basis.span_eq ▸ Submodule.mem_top
    have hmem := hbasis hspan
    change Additive.ofMul member ∈ submodule.toAddSubgroup at hmem
    rw [AddSubgroup.toZModSubmodule_toAddSubgroup] at hmem
    exact hmem
  exact (Group.rank_le (S := generators) hgenerated).trans
    (Finset.card_image_le.trans (by simp))

theorem binary_module_group_rank_eq_finrank
    {source : Type u} [CommGroup source] [Finite source]
    [Module (ZMod 2) (Additive source)] :
    Group.rank source = Module.finrank (ZMod 2) (Additive source) :=
  le_antisymm binary_module_group_rank_le_finrank binary_module_finrank_le_group_rank

theorem twoGroup_frattini_finrank_eq_group_rank
    {source : Type u} [Group source] [Finite source] (hsource : IsPGroup 2 source) :
    letI : IsMulCommutative (source ⧸ frattini source) :=
      pGroup_frattini_quotient_isMulCommutative 2 hsource
    letI : CommGroup (source ⧸ frattini source) := IsMulCommutative.instCommGroup
    letI := pGroup_binary_frattini_quotient_module hsource
    Module.finrank (ZMod 2) (Additive (source ⧸ frattini source)) = Group.rank source := by
  classical
  let : IsMulCommutative (source ⧸ frattini source) :=
    pGroup_frattini_quotient_isMulCommutative 2 hsource
  let : CommGroup (source ⧸ frattini source) := IsMulCommutative.instCommGroup
  let := pGroup_binary_frattini_quotient_module hsource
  apply le_antisymm
  · exact binary_module_finrank_le_group_rank.trans
      (Group.rank_le_of_surjective (QuotientGroup.mk' (frattini source))
        (QuotientGroup.mk'_surjective (frattini source)))
  · obtain ⟨quotientGenerators, hcard, hgeneration⟩ := Group.rank_spec (source ⧸ frattini source)
    let lift : (source ⧸ frattini source) → source :=
      fun member => Classical.choose (QuotientGroup.mk'_surjective (frattini source) member)
    have hlift : ∀ member, (QuotientGroup.mk' (frattini source)) (lift member) = member :=
      fun member => Classical.choose_spec (QuotientGroup.mk'_surjective (frattini source) member)
    let generators := quotientGenerators.image lift
    let generated := Subgroup.closure (generators : Set source)
    have hquotient : generated.map (QuotientGroup.mk' (frattini source)) = ⊤ := by
      apply top_unique
      rw [← hgeneration]
      apply (Subgroup.closure_le _).mpr
      intro member hmember
      exact ⟨lift member, Subgroup.subset_closure (Finset.mem_image_of_mem _ hmember), hlift member⟩
    have hjoin : generated ⊔ frattini source = ⊤ := by
      rw [← QuotientGroup.ker_mk' (frattini source), ← Subgroup.comap_map_eq, hquotient,
        Subgroup.comap_top]
    have hgenerated : generated = ⊤ := frattini_nongenerating hjoin
    exact (Group.rank_le (S := generators) hgenerated).trans
      (Finset.card_image_le.trans (hcard.le.trans binary_module_group_rank_le_finrank))

theorem cyclic_binary_center_quotient_group_rank_bound
    {source : Type u} [Group source] [Finite source]
    (hcenter : IsCyclic (Subgroup.center source))
    (hcommutator : commutator source ≤ Subgroup.center source)
    (hsquares : ∀ member : source, member ^ 2 ∈ Subgroup.center source) :
    letI : IsMulCommutative (source ⧸ Subgroup.center source) :=
      Subgroup.Normal.quotient_commutative_iff_commutator_le.mpr hcommutator
    letI : CommGroup (source ⧸ Subgroup.center source) := IsMulCommutative.instCommGroup
    letI := class_two_binary_center_quotient_module hsquares
    Group.rank source ≤ Module.finrank (ZMod 2) (Additive (source ⧸ Subgroup.center source)) + 1 := by
  let : IsCyclic (Subgroup.center source) := hcenter
  let : IsMulCommutative (source ⧸ Subgroup.center source) :=
    Subgroup.Normal.quotient_commutative_iff_commutator_le.mpr hcommutator
  let : CommGroup (source ⧸ Subgroup.center source) := IsMulCommutative.instCommGroup
  let := class_two_binary_center_quotient_module hsquares
  have hbound := subgroup_rank_le_rank_add_quotient_rank (Subgroup.center source)
  have hcenterRank := cyclic_group_rank_at_most_one (source := Subgroup.center source)
  have hquotientRank := binary_module_group_rank_eq_finrank (source := source ⧸ Subgroup.center source)
  omega

theorem critical_cyclic_center_group_rank_bound
    {source : Type u} [Group source] [Finite source]
    (hsource : IsPGroup 2 source)
    (critical : Subgroup source) [critical.Characteristic]
    (hcritical : Subgroup.centralizer (critical : Set source) ≤ critical)
    (hcommutator : ⁅(⊤ : Subgroup source), critical⁆ ≤
      (Subgroup.center critical).map critical.subtype)
    (hfrattini : (frattini critical).map critical.subtype ≤
      (Subgroup.center critical).map critical.subtype)
    (hcenter : IsCyclic (Subgroup.center critical)) (hnontrivial : Nontrivial critical) :
    ∃ hcommutatorLocal : commutator critical ≤ Subgroup.center critical,
      ∃ hsquares : ∀ member : critical, member ^ 2 ∈ Subgroup.center critical,
        letI : IsMulCommutative (critical ⧸ Subgroup.center critical) :=
          Subgroup.Normal.quotient_commutative_iff_commutator_le.mpr hcommutatorLocal
        letI : CommGroup (critical ⧸ Subgroup.center critical) := IsMulCommutative.instCommGroup
        letI := class_two_binary_center_quotient_module hsquares
        Group.rank source ≤ Module.finrank (ZMod 2) (Additive (critical ⧸ Subgroup.center critical)) + 3 := by
  let : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  have hfrattiniLocal : frattini critical ≤ Subgroup.center critical :=
    (Subgroup.map_le_map_iff_of_injective (f := critical.subtype) Subtype.val_injective).mp hfrattini
  have hcommutatorLocal : commutator critical ≤ Subgroup.center critical :=
    (pGroup_commutator_le_frattini 2 (hsource.to_subgroup critical)).trans hfrattiniLocal
  have hsquares : ∀ member : critical, member ^ 2 ∈ Subgroup.center critical :=
    fun member => hfrattiniLocal (pGroup_pow_mem_frattini 2 (hsource.to_subgroup critical) member)
  let : IsMulCommutative (critical ⧸ Subgroup.center critical) :=
    Subgroup.Normal.quotient_commutative_iff_commutator_le.mpr hcommutatorLocal
  let : CommGroup (critical ⧸ Subgroup.center critical) := IsMulCommutative.instCommGroup
  let := class_two_binary_center_quotient_module hsquares
  obtain ⟨embedding, hinjective⟩ := critical_cyclic_center_quotient_embeds_center_aut
    hsource critical hcritical hcommutator hfrattini hcenter hnontrivial
  have hquotientRank := injective_cyclic_twoGroup_aut_group_rank_at_most_two
    ((hsource.to_subgroup critical).to_subgroup (Subgroup.center critical)) hcenter embedding hinjective
  have hcriticalRank := cyclic_binary_center_quotient_group_rank_bound hcenter hcommutatorLocal hsquares
  have hsourceRank := subgroup_rank_le_rank_add_quotient_rank critical
  exact ⟨hcommutatorLocal, hsquares, by omega⟩

theorem binary_module_embedding_group_rank_bound
    {source : Type u} {target : Type v}
    [Group source] [Finite source] [CommGroup target] [Finite target]
    [Module (ZMod 2) (Additive target)]
    (hpow : ∀ member : target, member ^ 2 = 1)
    (hom : source →* target) (hinjective : Function.Injective hom) :
    Group.rank source ≤ Module.finrank (ZMod 2) (Additive target) := by
  let : IsMulCommutative source := IsMulCommutative.of_comm fun first second =>
    hinjective (by rw [map_mul, map_mul, mul_comm])
  let : CommGroup source := IsMulCommutative.instCommGroup
  have hsourcePow : ∀ member : source, member ^ 2 = 1 := by
    intro member
    apply hinjective
    rw [map_pow, hpow, map_one]
  let : Module (ZMod 2) (Additive source) :=
    AddCommGroup.zmodModule fun member => by
      change Additive.ofMul (member.toMul ^ 2) = 0
      rw [hsourcePow]
      rfl
  let linear := AddMonoidHom.toZModLinearMap 2 (MonoidHom.toAdditive hom)
  have hlinear : Function.Injective linear := hinjective
  exact (binary_module_group_rank_eq_finrank (source := source)).le.trans
    (LinearMap.finrank_le_finrank_of_injective hlinear)

theorem cyclic_binary_center_quotient_subgroup_rank_bound
    {source : Type u} [Group source] [Finite source]
    (hcenter : IsCyclic (Subgroup.center source))
    (hcommutator : commutator source ≤ Subgroup.center source)
    (hsquares : ∀ member : source, member ^ 2 ∈ Subgroup.center source)
    (subgroup : Subgroup source) :
    letI : IsMulCommutative (source ⧸ Subgroup.center source) :=
      Subgroup.Normal.quotient_commutative_iff_commutator_le.mpr hcommutator
    letI : CommGroup (source ⧸ Subgroup.center source) := IsMulCommutative.instCommGroup
    letI := class_two_binary_center_quotient_module hsquares
    Group.rank subgroup ≤ Module.finrank (ZMod 2) (Additive (source ⧸ Subgroup.center source)) + 1 := by
  let : IsCyclic (Subgroup.center source) := hcenter
  let : IsMulCommutative (source ⧸ Subgroup.center source) :=
    Subgroup.Normal.quotient_commutative_iff_commutator_le.mpr hcommutator
  let : CommGroup (source ⧸ Subgroup.center source) := IsMulCommutative.instCommGroup
  let := class_two_binary_center_quotient_module hsquares
  let hom := (QuotientGroup.mk' (Subgroup.center source)).comp subgroup.subtype
  let kernel := hom.ker
  let restriction : kernel →* Subgroup.center source :=
    { toFun := fun member => ⟨((member : subgroup) : source),
        (QuotientGroup.eq_one_iff _).mp member.property⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hrestriction : Function.Injective restriction := by
    intro first second hequal
    have hvalues : ((first : subgroup) : source) = ((second : subgroup) : source) :=
      congrArg (fun member : Subgroup.center source => (member : source)) hequal
    apply Subtype.ext
    apply Subtype.ext
    exact hvalues
  let : IsCyclic kernel := isCyclic_of_injective restriction hrestriction
  have hkernelRank := cyclic_group_rank_at_most_one (source := kernel)
  have hquotientRank := binary_module_embedding_group_rank_bound
    (class_two_center_quotient_pow_two_eq_one hsquares)
    (QuotientGroup.kerLift hom) (QuotientGroup.kerLift_injective hom)
  change Group.rank (subgroup ⧸ kernel) ≤
    Module.finrank (ZMod 2) (Additive (source ⧸ Subgroup.center source)) at hquotientRank
  have hsourceRank := subgroup_rank_le_rank_add_quotient_rank kernel
  omega

theorem critical_cyclic_center_subgroup_rank_bound
    {source : Type u} [Group source] [Finite source]
    (hsource : IsPGroup 2 source)
    (critical : Subgroup source) [critical.Characteristic]
    (hcritical : Subgroup.centralizer (critical : Set source) ≤ critical)
    (hcommutator : ⁅(⊤ : Subgroup source), critical⁆ ≤
      (Subgroup.center critical).map critical.subtype)
    (hfrattini : (frattini critical).map critical.subtype ≤
      (Subgroup.center critical).map critical.subtype)
    (hcenter : IsCyclic (Subgroup.center critical)) (hnontrivial : Nontrivial critical)
    (subgroup : Subgroup source) :
    ∃ hcommutatorLocal : commutator critical ≤ Subgroup.center critical,
      ∃ hsquares : ∀ member : critical, member ^ 2 ∈ Subgroup.center critical,
        letI : IsMulCommutative (critical ⧸ Subgroup.center critical) :=
          Subgroup.Normal.quotient_commutative_iff_commutator_le.mpr hcommutatorLocal
        letI : CommGroup (critical ⧸ Subgroup.center critical) := IsMulCommutative.instCommGroup
        letI := class_two_binary_center_quotient_module hsquares
        Group.rank subgroup ≤ Module.finrank (ZMod 2) (Additive (critical ⧸ Subgroup.center critical)) + 3 := by
  let : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  have hfrattiniLocal : frattini critical ≤ Subgroup.center critical :=
    (Subgroup.map_le_map_iff_of_injective (f := critical.subtype) Subtype.val_injective).mp hfrattini
  have hcommutatorLocal : commutator critical ≤ Subgroup.center critical :=
    (pGroup_commutator_le_frattini 2 (hsource.to_subgroup critical)).trans hfrattiniLocal
  have hsquares : ∀ member : critical, member ^ 2 ∈ Subgroup.center critical :=
    fun member => hfrattiniLocal (pGroup_pow_mem_frattini 2 (hsource.to_subgroup critical) member)
  let : IsMulCommutative (critical ⧸ Subgroup.center critical) :=
    Subgroup.Normal.quotient_commutative_iff_commutator_le.mpr hcommutatorLocal
  let : CommGroup (critical ⧸ Subgroup.center critical) := IsMulCommutative.instCommGroup
  let := class_two_binary_center_quotient_module hsquares
  obtain ⟨embedding, hinjective⟩ := critical_cyclic_center_quotient_embeds_center_aut
    hsource critical hcritical hcommutator hfrattini hcenter hnontrivial
  let hom := (QuotientGroup.mk' critical).comp subgroup.subtype
  let kernel := hom.ker
  let restriction : kernel →* critical :=
    { toFun := fun member => ⟨((member : subgroup) : source),
        (QuotientGroup.eq_one_iff _).mp member.property⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hrestriction : Function.Injective restriction := by
    intro first second hequal
    have hvalues : ((first : subgroup) : source) = ((second : subgroup) : source) :=
      congrArg (fun member : critical => (member : source)) hequal
    apply Subtype.ext
    apply Subtype.ext
    exact hvalues
  have hkernelRank := cyclic_binary_center_quotient_subgroup_rank_bound
    hcenter hcommutatorLocal hsquares restriction.range
  have hkernelRankTransport : Group.rank kernel = Group.rank restriction.range :=
    Group.rank_congr (MonoidHom.ofInjective hrestriction)
  have hquotientRank := injective_cyclic_twoGroup_aut_group_rank_at_most_two
    ((hsource.to_subgroup critical).to_subgroup (Subgroup.center critical)) hcenter
    (embedding.comp (QuotientGroup.kerLift hom))
    (hinjective.comp (QuotientGroup.kerLift_injective hom))
  change Group.rank (subgroup ⧸ kernel) ≤ 2 at hquotientRank
  have hsourceRank := subgroup_rank_le_rank_add_quotient_rank kernel
  exact ⟨hcommutatorLocal, hsquares, by omega⟩

theorem rank_four_local_twoCore_group_rank_at_least_eight
    {ambient : Type u} [Group ambient] [Finite ambient]
    (prime : ℕ) (hprime : prime.Prime) (hodd : prime ≠ 2)
    (hchar : IsCharTwoType ambient) (localGroup : Subgroup ambient) (hlocal : IsTwoLocal localGroup)
    (hrank : 4 ≤ pRank prime localGroup) : 8 ≤ Group.rank (pCoreOf 2 localGroup) := by
  let : IsMulCommutative (pCoreOf 2 localGroup ⧸ frattini (pCoreOf 2 localGroup)) :=
    pGroup_frattini_quotient_isMulCommutative 2 (pCoreOf_isPGroup 2 localGroup)
  let : CommGroup (pCoreOf 2 localGroup ⧸ frattini (pCoreOf 2 localGroup)) := IsMulCommutative.instCommGroup
  let := pGroup_binary_frattini_quotient_module (pCoreOf_isPGroup 2 localGroup)
  have hdimension := local_twoCore_frattini_dimension_bound prime hprime hodd hchar localGroup hlocal
  rw [twoGroup_frattini_finrank_eq_group_rank (pCoreOf_isPGroup 2 localGroup)] at hdimension
  omega

theorem local_twoCore_small_group_rank_forces_prime_three
    {ambient : Type u} [Group ambient] [Finite ambient]
    (prime : ℕ) (hprime : prime.Prime) (hodd : prime ≠ 2)
    (hchar : IsCharTwoType ambient) (localGroup : Subgroup ambient) (hlocal : IsTwoLocal localGroup)
    (hrank : 4 ≤ pRank prime localGroup) (hsmall : Group.rank (pCoreOf 2 localGroup) ≤ 11) : prime = 3 := by
  let : Fact prime.Prime := ⟨hprime⟩
  let : IsMulCommutative (pCoreOf 2 localGroup ⧸ frattini (pCoreOf 2 localGroup)) :=
    pGroup_frattini_quotient_isMulCommutative 2 (pCoreOf_isPGroup 2 localGroup)
  let : CommGroup (pCoreOf 2 localGroup ⧸ frattini (pCoreOf 2 localGroup)) := IsMulCommutative.instCommGroup
  let := pGroup_binary_frattini_quotient_module (pCoreOf_isPGroup 2 localGroup)
  have hdimension := local_twoCore_frattini_order_dimension_bound prime hprime hodd hchar localGroup hlocal
  rw [twoGroup_frattini_finrank_eq_group_rank (pCoreOf_isPGroup 2 localGroup)] at hdimension
  by_contra hthree
  have horder := binary_prime_order_at_least_three_of_ne_three prime hodd hthree
  have hcost : 12 ≤ orderOf (2 : ZMod prime) * pRank prime localGroup :=
    Nat.mul_le_mul horder hrank
  omega

theorem containing_twoGroup_small_subgroup_ranks_force_local_prime_three
    {ambient : Type u} [Group ambient] [Finite ambient]
    (prime : ℕ) (hprime : prime.Prime) (hodd : prime ≠ 2)
    (hchar : IsCharTwoType ambient) (localGroup : Subgroup ambient) (hlocal : IsTwoLocal localGroup)
    (hrank : 4 ≤ pRank prime localGroup) (containing : Subgroup ambient)
    (hcontained : pCoreOf 2 localGroup ≤ containing)
    (hsmall : ∀ subgroup : Subgroup containing, Group.rank subgroup ≤ 11) : prime = 3 := by
  apply local_twoCore_small_group_rank_forces_prime_three prime hprime hodd hchar localGroup hlocal hrank
  have hequivalence := (pCoreOf 2 localGroup).subgroupOfEquivOfLe hcontained
  rw [← Group.rank_congr hequivalence]
  exact hsmall _

end CFSG.PreuniquenessRankFour.Helpers
