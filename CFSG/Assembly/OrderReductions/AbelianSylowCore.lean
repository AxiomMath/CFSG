module

public import CFSG.Assembly.OrderReductions.ThompsonCenter
public import CFSG.Assembly.OrderReductions.SolvablePrimeCore

public section

namespace CFSG.OrderReductions.AbelianSylowCore

open CFSG.OrderReductions.PrimeCore
open CFSG.OrderReductions.PrimeComplementCore

theorem sylow_eq_primeCore_of_abelian {group : Type*} [Group group] [Finite group]
    [Group.IsSolvable group] (prime : ℕ) [Fact (Nat.Prime prime)]
    (core_bot : primeComplementCore prime group = ⊥)
    (sylow : Sylow prime group) [IsMulCommutative (sylow : Subgroup group)] :
    (sylow : Subgroup group) = primeCore prime group := by
  apply le_antisymm
  · apply le_trans _ (CFSG.OrderReductions.SolvablePrimeCore.centralizer_primeCore_le prime core_bot)
    intro element element_mem
    apply Subgroup.mem_centralizer_iff.mpr
    intro other other_mem
    exact congrArg Subtype.val ((isMulCommutative_iff.mp inferInstance)
      (⟨other, primeCore_le_sylow prime sylow other_mem⟩ : (sylow : Subgroup group)) ⟨element, element_mem⟩)
  · exact primeCore_le_sylow prime sylow

theorem sylow_characteristic_of_abelian {group : Type*} [Group group] [Finite group]
    [Group.IsSolvable group] (prime : ℕ) [Fact (Nat.Prime prime)]
    (core_bot : primeComplementCore prime group = ⊥)
    (sylow : Sylow prime group) [IsMulCommutative (sylow : Subgroup group)] :
    (sylow : Subgroup group).Characteristic := by
  rw [sylow_eq_primeCore_of_abelian prime core_bot sylow]
  infer_instance

theorem core_sup_sylow_characteristic_of_abelian {group : Type*} [Group group] [Finite group]
    [Group.IsSolvable group] (prime : ℕ) [Fact (Nat.Prime prime)]
    (sylow : Sylow prime group) [IsMulCommutative (sylow : Subgroup group)] :
    (primeComplementCore prime group ⊔ (sylow : Subgroup group)).Characteristic := by
  let core := primeComplementCore prime group
  let projection := QuotientGroup.mk' core
  have surjective : Function.Surjective projection := QuotientGroup.mk'_surjective core
  let image := Sylow.mapSurjective surjective sylow
  have image_eq : (image : Subgroup (group ⧸ core)) = (sylow : Subgroup group).map projection :=
    Sylow.coe_mapSurjective surjective sylow
  have : IsMulCommutative (image : Subgroup (group ⧸ core)) := by
    rw [image_eq]
    infer_instance
  have : (image : Subgroup (group ⧸ core)).Characteristic :=
    sylow_characteristic_of_abelian prime (core_quotient_eq_bot prime group) image
  have characteristic := Subgroup.Characteristic.comap_quotient_mk
    (H := core) (inferInstance : (image : Subgroup (group ⧸ core)).Characteristic)
  have preimage_eq : (image : Subgroup (group ⧸ core)).comap projection =
      core ⊔ (sylow : Subgroup group) := by
    rw [image_eq, Subgroup.comap_map_eq, QuotientGroup.ker_mk', sup_comm]
  exact preimage_eq ▸ characteristic

theorem core_sup_thompsonCenter_characteristic_of_abelian {group : Type*} [Group group] [Finite group]
    [Group.IsSolvable group] (prime : ℕ) [Fact (Nat.Prime prime)]
    (sylow : Sylow prime group) [IsMulCommutative (sylow : Subgroup group)] :
    (primeComplementCore prime group ⊔
      (CFSG.OrderReductions.ThompsonCenter.thompsonCenter (sylow : Subgroup group)).map
        (sylow : Subgroup group).subtype).Characteristic := by
  rw [CFSG.OrderReductions.ThompsonCenter.thompsonCenter_eq_top_of_abelian,
    ← MonoidHom.range_eq_map, Subgroup.subtype_range]
  exact core_sup_sylow_characteristic_of_abelian prime sylow

end CFSG.OrderReductions.AbelianSylowCore
