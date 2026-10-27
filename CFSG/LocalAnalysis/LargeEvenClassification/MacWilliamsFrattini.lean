module

public import CFSG.LocalAnalysis.LargeEvenClassification.IndependentKernelCount

public section

namespace CFSG.LargeEvenClassification.Helpers

universe groupUniverse indexUniverse

theorem pGeneratorRank_eq_group_rank {Ambient : Type groupUniverse} [Group Ambient]
    [Finite Ambient] {prime : ℕ} (hprime : prime.Prime) (hpgroup : IsPGroup prime Ambient) :
    pGeneratorRank prime Ambient = Group.rank Ambient := by
  obtain ⟨minimal, hminimalCard, hminimalGenerates⟩ := Group.rank_spec Ambient
  obtain ⟨generators, hgenerates, hcard⟩ := pGeneratorRank_generators hprime hpgroup
  apply le_antisymm
  · rw [← hminimalCard]
    exact pGeneratorRank_le_generators hprime hpgroup minimal hminimalGenerates
  · rw [← hcard]
    exact Group.rank_le hgenerates

noncomputable def normalFrattiniQuotientEquivImage {Ambient : Type groupUniverse} [Group Ambient]
    (Normal : Subgroup Ambient) :
    Normal ⧸ (frattini Ambient).subgroupOf Normal ≃*
      Normal.map (QuotientGroup.mk' (frattini Ambient)) := by
  let projection := QuotientGroup.mk' (frattini Ambient)
  let restriction := projection.subgroupMap Normal
  have hkernel : (frattini Ambient).subgroupOf Normal = restriction.ker := by
    ext element
    change (element : Ambient) ∈ frattini Ambient ↔ restriction element = 1
    constructor
    · intro hmem
      exact Subtype.ext ((QuotientGroup.eq_one_iff _).mpr hmem)
    · intro heq
      exact (QuotientGroup.eq_one_iff _).mp (congrArg Subtype.val heq)
  exact QuotientGroup.liftEquiv _ (projection.subgroupMap_surjective Normal) hkernel

theorem normal_frattini_quotient_elementary {Ambient : Type groupUniverse} [Group Ambient]
    [Finite Ambient] {prime : ℕ} (hprime : prime.Prime) (hpgroup : IsPGroup prime Ambient)
    (Normal : Subgroup Ambient) :
    IsMulCommutative (Normal ⧸ (frattini Ambient).subgroupOf Normal) ∧
      ∀ element : Normal ⧸ (frattini Ambient).subgroupOf Normal, element ^ prime = 1 := by
  let : CommGroup (Ambient ⧸ frattini Ambient) := pGroupFrattiniCommGroup hprime hpgroup
  let equivalence := normalFrattiniQuotientEquivImage Normal
  constructor
  · apply IsMulCommutative.of_comm
    intro first second
    apply equivalence.injective
    rw [map_mul, map_mul, mul_comm]
  · intro element
    apply equivalence.injective
    rw [map_pow, map_one]
    apply Subtype.ext
    exact pGroup_frattini_quotient_exponent hprime hpgroup (equivalence element)

theorem normal_frattini_kernel_generator_count {Ambient : Type groupUniverse} [Group Ambient]
    [Finite Ambient] {prime : ℕ} (hprime : prime.Prime) (hpgroup : IsPGroup prime Ambient)
    (Normal : Subgroup Ambient) [Normal.Normal] :
    let _ : CommGroup (Normal ⧸ (frattini Ambient).subgroupOf Normal) :=
      { (inferInstance : Group (Normal ⧸ (frattini Ambient).subgroupOf Normal)) with
        mul_comm := @mul_comm' _ _ (normal_frattini_quotient_elementary hprime hpgroup Normal).1 }
    ∃ module : Module (ZMod prime)
        (Additive (Normal ⧸ (frattini Ambient).subgroupOf Normal)),
      let _ := module
      pGeneratorRank prime Ambient = pGeneratorRank prime (Ambient ⧸ Normal) +
        Module.finrank (ZMod prime) (Additive (Normal ⧸ (frattini Ambient).subgroupOf Normal)) := by
  dsimp only
  let : CommGroup (Normal ⧸ (frattini Ambient).subgroupOf Normal) :=
    { (inferInstance : Group (Normal ⧸ (frattini Ambient).subgroupOf Normal)) with
      mul_comm := @mul_comm' _ _ (normal_frattini_quotient_elementary hprime hpgroup Normal).1 }
  let module : Module (ZMod prime)
      (Additive (Normal ⧸ (frattini Ambient).subgroupOf Normal)) :=
    elementaryZModModule (normal_frattini_quotient_elementary hprime hpgroup Normal).2
  refine ⟨module, ?_⟩
  have hformula := pGeneratorRank_extension hprime hpgroup (QuotientGroup.mk' Normal)
    (QuotientGroup.mk'_surjective Normal)
  rw [QuotientGroup.ker_mk',
    ← Nat.card_congr (normalFrattiniQuotientEquivImage Normal).toEquiv,
    elementary_log_card_eq_finrank hprime] at hformula
  exact hformula

theorem normal_frattini_independent_generator_bound {Ambient : Type groupUniverse} [Group Ambient]
    [Finite Ambient] {Index : Type indexUniverse} [Fintype Index] {prime bound : ℕ}
    (hprime : prime.Prime) (hpgroup : IsPGroup prime Ambient) (Normal : Subgroup Ambient)
    [Normal.Normal] (hbound : pGeneratorRank prime Normal ≤ bound) (family : Index → Normal)
    (hfrattini : ∀ index, (family index : Ambient) ∈ frattini Ambient) :
    let _ : CommGroup (Normal ⧸ frattini Normal) :=
      pGroupFrattiniCommGroup hprime (hpgroup.to_subgroup Normal)
    ∀ module : Module (ZMod prime) (Additive (Normal ⧸ frattini Normal)),
      let _ := module
      LinearIndependent (ZMod prime)
        (fun index => Additive.ofMul ((QuotientGroup.mk' (frattini Normal)) (family index))) →
      pGeneratorRank prime Ambient ≤ pGeneratorRank prime (Ambient ⧸ Normal) +
        (bound - Fintype.card Index) := by
  dsimp only
  let : CommGroup (Normal ⧸ frattini Normal) :=
    pGroupFrattiniCommGroup hprime (hpgroup.to_subgroup Normal)
  let : Fact prime.Prime := ⟨hprime⟩
  intro module
  let := module
  intro hindependent
  have hcount : Fintype.card Index ≤ pGeneratorRank prime Normal := by
    rw [pGeneratorRank_eq_frattini_finrank hprime (hpgroup.to_subgroup Normal) module]
    exact hindependent.fintype_card_le_finrank
  have hsaving := pGeneratorRank_normal_independent_saving hprime hpgroup Normal family hfrattini
    module hindependent
  omega

end CFSG.LargeEvenClassification.Helpers
