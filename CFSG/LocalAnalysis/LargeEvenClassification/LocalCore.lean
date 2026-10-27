module

public import CFSG.Open.LocalVocabulary

public section

open CFSG.Open
open CFSG.Open

namespace CFSG.LargeEvenClassification.Helpers

universe groupUniverse

theorem normal_pSubgroup_le_pCore {Ambient : Type groupUniverse} [Group Ambient]
    {prime : ℕ} (NormalSubgroup : Subgroup Ambient) (hnormal : NormalSubgroup.Normal)
    (hpgroup : IsPGroup prime NormalSubgroup) : NormalSubgroup ≤ pCore prime Ambient :=
  le_sSup ⟨hnormal, hpgroup⟩

theorem pCore_eq_maximal_normal_pSubgroup (Ambient : Type groupUniverse) [Group Ambient]
    [Finite Ambient] (prime : ℕ) :
    ∃ Core : Subgroup Ambient,
      Core.Normal ∧ IsPGroup prime Core ∧ pCore prime Ambient = Core := by
  have hbot : (⊥ : Subgroup Ambient).Normal ∧ IsPGroup prime (⊥ : Subgroup Ambient) :=
    ⟨inferInstance, IsPGroup.of_bot⟩
  obtain ⟨Core, _, hmaximal⟩ := Finite.exists_le_maximal
    (p := fun NormalSubgroup : Subgroup Ambient =>
      NormalSubgroup.Normal ∧ IsPGroup prime NormalSubgroup) hbot
  obtain ⟨hnormal, hpgroup⟩ := hmaximal.prop
  refine ⟨Core, hnormal, hpgroup, le_antisymm ?_ ?_⟩
  · rw [CFSG.pCore_eq_iSup]
    apply iSup_le
    intro NormalSubgroup
    apply iSup_le
    intro hsubgroupNormal
    apply iSup_le
    intro hsubgroupPGroup
    let : Core.Normal := hnormal
    let : NormalSubgroup.Normal := hsubgroupNormal
    have hsup : (Core ⊔ NormalSubgroup).Normal ∧
        IsPGroup prime (Core ⊔ NormalSubgroup : Subgroup Ambient) :=
      ⟨inferInstance, hpgroup.to_sup_of_normal_left hsubgroupPGroup⟩
    exact le_trans le_sup_right (hmaximal.2 hsup le_sup_left)
  · exact normal_pSubgroup_le_pCore Core hnormal hpgroup

theorem pCore_normal (Ambient : Type groupUniverse) [Group Ambient] [Finite Ambient]
    (prime : ℕ) : (pCore prime Ambient).Normal := by
  obtain ⟨Core, hnormal, _, hcore⟩ := pCore_eq_maximal_normal_pSubgroup Ambient prime
  exact hcore ▸ hnormal

theorem pCore_isPGroup (Ambient : Type groupUniverse) [Group Ambient] [Finite Ambient]
    (prime : ℕ) : IsPGroup prime (pCore prime Ambient) := by
  obtain ⟨Core, _, hpgroup, hcore⟩ := pCore_eq_maximal_normal_pSubgroup Ambient prime
  exact hcore ▸ hpgroup

theorem pCoreOf_le {Ambient : Type groupUniverse} [Group Ambient] (prime : ℕ)
    (Local : Subgroup Ambient) : pCoreOf prime Local ≤ Local := by
  intro element helement
  obtain ⟨preimage, _, hpreimage⟩ := helement
  exact hpreimage ▸ preimage.property

theorem pCoreOf_isPGroup {Ambient : Type groupUniverse} [Group Ambient] [Finite Ambient]
    (prime : ℕ) (Local : Subgroup Ambient) : IsPGroup prime (pCoreOf prime Local) := by
  exact (pCore_isPGroup Local prime).map Local.subtype

theorem normal_pSubgroup_le_pCoreOf {Ambient : Type groupUniverse} [Group Ambient]
    {prime : ℕ} (NormalSubgroup Local : Subgroup Ambient) (hle : NormalSubgroup ≤ Local)
    (hnormal : (NormalSubgroup.subgroupOf Local).Normal)
    (hpgroup : IsPGroup prime NormalSubgroup) : NormalSubgroup ≤ pCoreOf prime Local := by
  have hpgroupOf : IsPGroup prime (NormalSubgroup.subgroupOf Local) :=
    hpgroup.of_equiv (Subgroup.subgroupOfEquivOfLe hle).symm
  have hcore := normal_pSubgroup_le_pCore (NormalSubgroup.subgroupOf Local) hnormal hpgroupOf
  have hmap := Subgroup.map_mono (f := Local.subtype) hcore
  rwa [Subgroup.map_subgroupOf_eq_of_le hle] at hmap

theorem twoLocal_core_ne_bot {Ambient : Type groupUniverse} [Group Ambient]
    (Local : Subgroup Ambient) (hlocal : IsTwoLocal Local) : pCoreOf 2 Local ≠ ⊥ := by
  obtain ⟨TwoSubgroup, hnontrivial, hpgroup, hnormalizer⟩ := hlocal
  have hle : TwoSubgroup ≤ Local := hnormalizer ▸ Subgroup.le_normalizer
  have hnormal : (TwoSubgroup.subgroupOf Local).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hle).mpr (le_of_eq hnormalizer)
  have hcore := normal_pSubgroup_le_pCoreOf TwoSubgroup Local hle hnormal hpgroup
  intro hbot
  apply hnontrivial
  exact le_antisymm (hbot ▸ hcore) bot_le

theorem pCoreOf_subgroupOf_normal {Ambient : Type groupUniverse} [Group Ambient]
    [Finite Ambient] (prime : ℕ) (Local : Subgroup Ambient) :
    ((pCoreOf prime Local).subgroupOf Local).Normal := by
  have heq : (pCoreOf prime Local).subgroupOf Local = pCore prime Local :=
    Subgroup.comap_map_eq_self_of_injective Local.subtype_injective _
  rw [heq]
  exact pCore_normal Local prime

theorem charTwo_odd_subgroup_disjoint_core {Ambient : Type groupUniverse} [Group Ambient]
    [Finite Ambient] {prime : ℕ} (hprime : prime.Prime) (hodd : prime ≠ 2)
    (OddSubgroup Local : Subgroup Ambient) (hpgroup : IsPGroup prime OddSubgroup) :
    Disjoint OddSubgroup (pCoreOf 2 Local) := by
  let : Fact prime.Prime := ⟨hprime⟩
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact IsPGroup.disjoint_of_ne prime 2 hodd OddSubgroup (pCoreOf 2 Local)
    hpgroup (pCoreOf_isPGroup 2 Local)

theorem charTwo_odd_subgroup_core_centralizer {Ambient : Type groupUniverse} [Group Ambient]
    [Finite Ambient] {prime : ℕ} (hprime : prime.Prime) (hodd : prime ≠ 2)
    (hchar : IsCharTwoType Ambient) (OddSubgroup Local : Subgroup Ambient)
    (hle : OddSubgroup ≤ Local) (hpgroup : IsPGroup prime OddSubgroup)
    (hlocal : IsTwoLocal Local) :
    OddSubgroup ⊓ Subgroup.centralizer (pCoreOf 2 Local : Set Ambient) = ⊥ := by
  have hdisjoint := charTwo_odd_subgroup_disjoint_core hprime hodd OddSubgroup Local hpgroup
  apply le_antisymm _ bot_le
  intro element helement
  apply Subgroup.mem_bot.mpr
  apply Subgroup.disjoint_def.mp hdisjoint helement.1
  exact hchar Local hlocal ⟨hle helement.1, helement.2⟩

theorem charTwo_odd_core_action_injective {Ambient : Type groupUniverse} [Group Ambient]
    [Finite Ambient] {prime : ℕ} (hprime : prime.Prime) (hodd : prime ≠ 2)
    (hchar : IsCharTwoType Ambient) (OddSubgroup Local : Subgroup Ambient)
    (hle : OddSubgroup ≤ Local) (hpgroup : IsPGroup prime OddSubgroup)
    (hlocal : IsTwoLocal Local) :
    ∃ action : OddSubgroup →* MulAut ((pCoreOf 2 Local).subgroupOf Local),
      Function.Injective action := by
  let : ((pCoreOf 2 Local).subgroupOf Local).Normal := pCoreOf_subgroupOf_normal 2 Local
  let action : OddSubgroup →* MulAut ((pCoreOf 2 Local).subgroupOf Local) :=
    MulAut.conjNormal.comp (Subgroup.inclusion hle)
  refine ⟨action, ?_⟩
  apply (MonoidHom.ker_eq_bot_iff action).mp
  apply le_antisymm _ bot_le
  intro element helement
  apply Subgroup.mem_bot.mpr
  apply Subtype.ext
  change (element : Ambient) = 1
  have hcentralizer : (element : Ambient) ∈
      Subgroup.centralizer (pCoreOf 2 Local : Set Ambient) := by
    apply Subgroup.mem_centralizer_iff.mpr
    intro coreElement hcoreElement
    have hcoreLocal : coreElement ∈ Local := pCoreOf_le 2 Local hcoreElement
    let coreElementOf : (pCoreOf 2 Local).subgroupOf Local :=
      ⟨⟨coreElement, hcoreLocal⟩, hcoreElement⟩
    have hfixed := congrArg (fun automorphism => automorphism coreElementOf) helement
    have hambient := congrArg
      (fun fixedElement : (pCoreOf 2 Local).subgroupOf Local =>
        ((fixedElement : Local) : Ambient)) hfixed
    change (element : Ambient) * coreElement * (element : Ambient)⁻¹ = coreElement at hambient
    exact ((mul_inv_eq_iff_eq_mul).mp hambient).symm
  have htrivial := charTwo_odd_subgroup_core_centralizer hprime hodd hchar
    OddSubgroup Local hle hpgroup hlocal
  exact Subgroup.mem_bot.mp (htrivial ▸ ⟨element.property, hcentralizer⟩)

end CFSG.LargeEvenClassification.Helpers
