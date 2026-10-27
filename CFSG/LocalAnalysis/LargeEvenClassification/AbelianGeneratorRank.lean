module

public import CFSG.LocalAnalysis.LargeEvenClassification.ExtensionGenerators
public import CFSG.LocalAnalysis.LargeEvenClassification.FrattiniExact

public section

namespace CFSG.LargeEvenClassification.Helpers

universe groupUniverse targetUniverse

theorem pGeneratorRank_surjective_le {Source : Type groupUniverse} [Group Source] [Finite Source]
    {Target : Type targetUniverse} [Group Target] {prime : ℕ} (hprime : prime.Prime)
    (hpgroup : IsPGroup prime Source) (quotient : Source →* Target)
    (hsurjective : Function.Surjective quotient) :
    pGeneratorRank prime Target ≤ pGeneratorRank prime Source := by
  have hformula := pGeneratorRank_extension hprime hpgroup quotient hsurjective
  omega

theorem pGeneratorRank_mulEquiv {Source : Type groupUniverse} [Group Source] [Finite Source]
    {Target : Type targetUniverse} [Group Target] {prime : ℕ} (hprime : prime.Prime)
    (hpgroup : IsPGroup prime Source) (equivalence : Source ≃* Target) :
    pGeneratorRank prime Source = pGeneratorRank prime Target := by
  let : Finite Target := Finite.of_equiv Source equivalence.toEquiv
  have htarget := hpgroup.of_surjective equivalence.toMonoidHom equivalence.surjective
  exact le_antisymm
    (pGeneratorRank_surjective_le hprime htarget equivalence.symm.toMonoidHom
      equivalence.symm.surjective)
    (pGeneratorRank_surjective_le hprime hpgroup equivalence.toMonoidHom equivalence.surjective)

theorem commutative_frattini_card_eq_power_kernel {Ambient : Type groupUniverse}
    [CommGroup Ambient] [Finite Ambient] {prime : ℕ} (hprime : prime.Prime)
    (hpgroup : IsPGroup prime Ambient) :
    Nat.card (Ambient ⧸ frattini Ambient) =
      Nat.card (powMonoidHom prime : Ambient →* Ambient).ker := by
  let powerMap := (powMonoidHom prime : Ambient →* Ambient)
  rw [commutative_frattini_eq_power_range hprime hpgroup]
  have hrange := Subgroup.card_eq_card_quotient_mul_card_subgroup powerMap.range
  have hkernel := Subgroup.card_eq_card_quotient_mul_card_subgroup powerMap.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange powerMap).toEquiv] at hkernel
  have hpositive : 0 < Nat.card powerMap.range := Nat.card_pos
  nlinarith

theorem commutative_pGeneratorRank_embedding_le {Source : Type groupUniverse} [CommGroup Source]
    {Target : Type targetUniverse} [CommGroup Target] [Finite Target] {prime : ℕ}
    (hprime : prime.Prime) (hptarget : IsPGroup prime Target) (embedding : Source →* Target)
    (hinjective : Function.Injective embedding) :
    pGeneratorRank prime Source ≤ pGeneratorRank prime Target := by
  let : Finite Source := Finite.of_injective embedding hinjective
  have hpsource := hptarget.of_injective embedding hinjective
  let kernelEmbedding : (powMonoidHom prime : Source →* Source).ker →
      (powMonoidHom prime : Target →* Target).ker := fun element =>
    ⟨embedding element, by
      change (embedding (element : Source)) ^ prime = 1
      rw [← map_pow, show (element : Source) ^ prime = 1 from element.property, map_one]⟩
  have hkernelInjective : Function.Injective kernelEmbedding := by
    intro first second heq
    apply Subtype.ext
    exact hinjective (congrArg Subtype.val heq)
  have hcard := Nat.card_le_card_of_injective kernelEmbedding hkernelInjective
  unfold pGeneratorRank
  rw [commutative_frattini_card_eq_power_kernel hprime hpsource,
    commutative_frattini_card_eq_power_kernel hprime hptarget]
  exact Nat.log_mono_right hcard

theorem commutative_pGeneratorRank_subgroup_le {Ambient : Type groupUniverse} [CommGroup Ambient]
    [Finite Ambient] {prime : ℕ} (hprime : prime.Prime) (hpgroup : IsPGroup prime Ambient)
    (SubgroupOfAmbient : Subgroup Ambient) :
    pGeneratorRank prime SubgroupOfAmbient ≤ pGeneratorRank prime Ambient := by
  exact commutative_pGeneratorRank_embedding_le hprime hpgroup SubgroupOfAmbient.subtype
    Subtype.val_injective

theorem cyclic_generators {Ambient : Type groupUniverse} [Group Ambient] [IsCyclic Ambient] :
    ∃ generators : Finset Ambient, Subgroup.closure (generators : Set Ambient) = ⊤ ∧
      generators.card ≤ 1 := by
  classical
  obtain ⟨generator, hgenerator⟩ := IsCyclic.exists_generator (α := Ambient)
  refine ⟨{generator}, ?_, by simp⟩
  apply top_unique
  intro element _
  rw [Finset.coe_singleton]
  rw [← Subgroup.zpowers_eq_closure]
  exact hgenerator element

theorem cyclic_pGeneratorRank_le_one {Ambient : Type groupUniverse} [Group Ambient]
    [Finite Ambient] [IsCyclic Ambient] {prime : ℕ} (hprime : prime.Prime)
    (hpgroup : IsPGroup prime Ambient) : pGeneratorRank prime Ambient ≤ 1 := by
  obtain ⟨generators, hgenerates, hcard⟩ := cyclic_generators (Ambient := Ambient)
  exact (pGeneratorRank_le_generators hprime hpgroup generators hgenerates).trans hcard

theorem pGeneratorRank_of_cyclic_kernel_image {Source : Type groupUniverse} [Group Source]
    [Finite Source] {Target : Type targetUniverse} [Group Target] [IsCyclic Target]
    {prime : ℕ} (hprime : prime.Prime) (hpgroup : IsPGroup prime Source)
    (quotient : Source →* Target) (hsurjective : Function.Surjective quotient)
    [IsCyclic quotient.ker] : pGeneratorRank prime Source ≤ 2 := by
  obtain ⟨generators, hgenerates, hcard⟩ := extension_generator_bound quotient hsurjective
    (cyclic_generators (Ambient := quotient.ker)) (cyclic_generators (Ambient := Target))
  exact (pGeneratorRank_le_generators hprime hpgroup generators hgenerates).trans hcard

theorem pGeneratorRank_extension_le {Ambient : Type groupUniverse} [Group Ambient]
    [Finite Ambient] {prime : ℕ} (hprime : prime.Prime) (hpgroup : IsPGroup prime Ambient)
    (Normal : Subgroup Ambient) [Normal.Normal] :
    pGeneratorRank prime Ambient ≤ pGeneratorRank prime (Ambient ⧸ Normal) +
      pGeneratorRank prime Normal := by
  let : CommGroup (Ambient ⧸ frattini Ambient) := pGroupFrattiniCommGroup hprime hpgroup
  let projection := QuotientGroup.mk' (frattini Ambient)
  have hexponent : ∀ element : Normal.map projection, element ^ prime = 1 := by
    intro element
    apply Subtype.ext
    exact pGroup_frattini_quotient_exponent hprime hpgroup element
  have hbound := pGeneratorRank_surjective_le hprime (hpgroup.to_subgroup Normal)
    (projection.subgroupMap Normal) (projection.subgroupMap_surjective Normal)
  rw [elementary_pGeneratorRank_eq_log_card hprime hexponent] at hbound
  have hformula := pGeneratorRank_extension hprime hpgroup (QuotientGroup.mk' Normal)
    (QuotientGroup.mk'_surjective Normal)
  rw [QuotientGroup.ker_mk'] at hformula
  change Nat.log prime (Nat.card (Normal.map (QuotientGroup.mk' (frattini Ambient)))) ≤
    pGeneratorRank prime Normal at hbound
  omega

end CFSG.LargeEvenClassification.Helpers
