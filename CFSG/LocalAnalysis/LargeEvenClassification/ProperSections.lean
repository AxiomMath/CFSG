module

public import CFSG.Open.OrderForm
import CFSG.Foundations.KCoreOpen

public section

open CFSG.Open

namespace CFSG.LargeEvenClassification.Helpers

universe groupUniverse targetUniverse

instance normal_map_mulEquiv {Ambient : Type groupUniverse} [Group Ambient]
    {Target : Type targetUniverse} [Group Target] (NormalSubgroup : Subgroup Ambient)
    [NormalSubgroup.Normal] (equivalence : Ambient ≃* Target) :
    (NormalSubgroup.map equivalence.toMonoidHom).Normal :=
  Subgroup.Normal.map inferInstance equivalence.toMonoidHom equivalence.surjective

theorem nonabelian_of_mulEquiv {Source : Type groupUniverse} [Group Source]
    {Target : Type targetUniverse} [Group Target] (equivalence : Source ≃* Target)
    (hnonab : ∃ first second : Source, first * second ≠ second * first) :
    ∃ first second : Target, first * second ≠ second * first := by
  obtain ⟨first, second, hne⟩ := hnonab
  refine ⟨equivalence first, equivalence second, ?_⟩
  intro heq
  apply hne
  apply equivalence.injective
  simpa using heq

theorem section_equiv_map {Ambient : Type groupUniverse} [Group Ambient]
    {Target : Type targetUniverse} [Group Target] (embedding : Ambient →* Target)
    (hinjective : Function.Injective embedding) (Numerator Denominator : Subgroup Ambient)
    (hle : Denominator ≤ Numerator) [(Denominator.subgroupOf Numerator).Normal] :
    ∃ _ : (Numerator ⧸ Denominator.subgroupOf Numerator) ≃*
        ((Numerator.map embedding) ⧸
          (Denominator.subgroupOf Numerator).map
            (Numerator.equivMapOfInjective embedding hinjective).toMonoidHom),
      ((Denominator.map embedding).subgroupOf (Numerator.map embedding)) =
        (Denominator.subgroupOf Numerator).map
          (Numerator.equivMapOfInjective embedding hinjective).toMonoidHom := by
  let equivalence := Numerator.equivMapOfInjective embedding hinjective
  have hnormal : ((Denominator.subgroupOf Numerator).map equivalence.toMonoidHom).Normal :=
    Subgroup.Normal.map inferInstance equivalence.toMonoidHom equivalence.surjective
  let : ((Denominator.subgroupOf Numerator).map equivalence.toMonoidHom).Normal := hnormal
  refine ⟨QuotientGroup.congr (Denominator.subgroupOf Numerator)
    ((Denominator.subgroupOf Numerator).map equivalence.toMonoidHom) equivalence rfl, ?_⟩
  apply (Numerator.map embedding).map_subtype_inj.mp
  rw [Subgroup.map_subgroupOf_eq_of_le (Subgroup.map_mono hle), Subgroup.map_map]
  have hcomposition : (Numerator.map embedding).subtype.comp equivalence.toMonoidHom =
      embedding.comp Numerator.subtype := by
    ext element
    rfl
  rw [hcomposition, ← Subgroup.map_map, Subgroup.map_subgroupOf_eq_of_le hle]

theorem simple_section_order_of_embedding {Ambient : Type groupUniverse} [Group Ambient]
    {Target : Type targetUniverse} [Group Target] (embedding : Ambient →* Target)
    (hinjective : Function.Injective embedding) (hK : IsKProperByOrder Target)
    (Numerator Denominator : Subgroup Ambient) (hle : Denominator ≤ Numerator)
    [(Denominator.subgroupOf Numerator).Normal]
    (hproper : Numerator.map embedding ≠ ⊤)
    [IsSimpleGroup (Numerator ⧸ Denominator.subgroupOf Numerator)]
    (hnonab : ∃ first second : Numerator ⧸ Denominator.subgroupOf Numerator,
      first * second ≠ second * first) :
    Nat.card (Numerator ⧸ Denominator.subgroupOf Numerator) ∈ knownSimpleOrders := by
  obtain ⟨equivalence, hdenominator⟩ := section_equiv_map embedding hinjective
    Numerator Denominator hle
  let : ((Denominator.map embedding).subgroupOf (Numerator.map embedding)).Normal := by
    rw [hdenominator]
    infer_instance
  have actualEquivalence : (Numerator ⧸ Denominator.subgroupOf Numerator) ≃*
      ((Numerator.map embedding) ⧸
        (Denominator.map embedding).subgroupOf (Numerator.map embedding)) :=
    equivalence.trans (QuotientGroup.quotientMulEquivOfEq hdenominator.symm)
  let : IsSimpleGroup ((Numerator.map embedding) ⧸
      (Denominator.map embedding).subgroupOf (Numerator.map embedding)) :=
    actualEquivalence.symm.isSimpleGroup
  have hknown := hK (Numerator.map embedding) (Denominator.map embedding)
    hproper (Subgroup.map_mono hle) inferInstance
    (nonabelian_of_mulEquiv actualEquivalence hnonab)
  rwa [← Nat.card_congr actualEquivalence.toEquiv] at hknown

theorem isKProper_of_injective {Ambient : Type groupUniverse} [Group Ambient]
    {Target : Type targetUniverse} [Group Target] (embedding : Ambient →* Target)
    (hinjective : Function.Injective embedding) (hK : IsKProperByOrder Target) :
    IsKProperByOrder Ambient :=
  hK.of_injective embedding hinjective

theorem isKProper_subgroup {Ambient : Type groupUniverse} [Group Ambient]
    (hK : IsKProperByOrder Ambient) (Local : Subgroup Ambient) : IsKProperByOrder Local := by
  exact isKProper_of_injective Local.subtype Local.subtype_injective hK

theorem proper_subgroup_simple_section_order {Ambient : Type groupUniverse} [Group Ambient]
    (hK : IsKProperByOrder Ambient) (Local : Subgroup Ambient) (hproper : Local ≠ ⊤)
    (Numerator Denominator : Subgroup Local) (hle : Denominator ≤ Numerator)
    [(Denominator.subgroupOf Numerator).Normal]
    [IsSimpleGroup (Numerator ⧸ Denominator.subgroupOf Numerator)]
    (hnonab : ∃ first second : Numerator ⧸ Denominator.subgroupOf Numerator,
      first * second ≠ second * first) :
    Nat.card (Numerator ⧸ Denominator.subgroupOf Numerator) ∈ knownSimpleOrders := by
  apply simple_section_order_of_embedding Local.subtype Local.subtype_injective hK
    Numerator Denominator hle _ hnonab
  intro hmapTop
  have hmapLe : Numerator.map Local.subtype ≤ Local := by
    simpa using Numerator.map_le_range Local.subtype
  exact hproper (top_unique (hmapTop ▸ hmapLe))

end CFSG.LargeEvenClassification.Helpers
