module

public import CFSG.Assembly.OrderReductions.ThompsonCoreProduct
import CFSG.Foundations.MaxOrderThompsonImage

public section

namespace CFSG.OrderReductions.ThompsonQuotient

open CFSG.OrderReductions.ThompsonCenter
open CFSG.OrderReductions.ThompsonCoreProduct
open CFSG.OrderReductions.PrimeComplementCore

theorem prime_subgroup_injective_of_coprime_kernel {source target : Type*}
    [Group source] [Finite source] [Group target]
    (prime : ℕ) [Fact (Nat.Prime prime)] (homomorphism : source →* target)
    (kernel_coprime : ¬ prime ∣ Nat.card homomorphism.ker)
    (subgroup : Subgroup source) (prime_group : IsPGroup prime subgroup) :
    Function.Injective (homomorphism.subgroupMap subgroup) := fun _ _ equal =>
  CFSG.injective_comp_subtype_of_coprime_card_ker homomorphism
    ((Fact.out : prime.Prime).coprime_iff_not_dvd.mpr kernel_coprime) prime_group
    (congrArg Subtype.val equal)

theorem thompsonCenter_image_of_coprime_kernel {source target : Type*}
    [Group source] [Finite source] [Group target]
    (prime : ℕ) [Fact (Nat.Prime prime)] (homomorphism : source →* target)
    (kernel_coprime : ¬ prime ∣ Nat.card homomorphism.ker)
    (subgroup : Subgroup source) (prime_group : IsPGroup prime subgroup) :
    ((thompsonCenter subgroup).map subgroup.subtype).map homomorphism =
      (thompsonCenter (subgroup.map homomorphism)).map (subgroup.map homomorphism).subtype :=
  CFSG.map_maxCardZJ_map_subtype_of_injective homomorphism subgroup
    (CFSG.injective_comp_subtype_of_coprime_card_ker homomorphism
      ((Fact.out : prime.Prime).coprime_iff_not_dvd.mpr kernel_coprime) prime_group)

theorem coreProduct_eq_preimage_quotient_center {group : Type*} [Group group] [Finite group]
    (prime : ℕ) [Fact (Nat.Prime prime)] (sylow : Sylow prime group) :
    let core := primeComplementCore prime group
    let projection := QuotientGroup.mk' core
    let image := (sylow : Subgroup group).map projection
    coreProduct prime sylow = ((thompsonCenter image).map image.subtype).comap projection := by
  let core := primeComplementCore prime group
  let projection := QuotientGroup.mk' core
  let image := (sylow : Subgroup group).map projection
  have kernel_coprime : ¬ prime ∣ Nat.card projection.ker := by
    rw [QuotientGroup.ker_mk']
    exact primeComplementCore_coprime prime group
  have center_eq := thompsonCenter_image_of_coprime_kernel prime projection kernel_coprime
    (sylow : Subgroup group) sylow.isPGroup'
  change coreProduct prime sylow = _
  rw [← center_eq, Subgroup.comap_map_eq, QuotientGroup.ker_mk', sup_comm]
  rfl

theorem coreProduct_characteristic_of_quotient_center {group : Type*} [Group group] [Finite group]
    (prime : ℕ) [Fact (Nat.Prime prime)] (sylow : Sylow prime group)
    (characteristic :
      let core := primeComplementCore prime group
      let image := (sylow : Subgroup group).map (QuotientGroup.mk' core)
      ((thompsonCenter image).map image.subtype).Characteristic) :
    (coreProduct prime sylow).Characteristic := by
  rw [coreProduct_eq_preimage_quotient_center prime sylow]
  exact Subgroup.Characteristic.comap_quotient_mk characteristic

theorem coreProduct_characteristic_of_nilpotent {group : Type*} [Group group] [Finite group]
    [Group.IsNilpotent group] (prime : ℕ) [Fact (Nat.Prime prime)] (sylow : Sylow prime group) :
    (coreProduct prime sylow).Characteristic := by
  have : (sylow : Subgroup group).Normal :=
    Sylow.normal_of_normalizerCondition Group.normalizerCondition_of_isNilpotent sylow
  have : (sylow : Subgroup group).Characteristic := sylow.characteristic_of_normal inferInstance
  unfold coreProduct
  infer_instance

end CFSG.OrderReductions.ThompsonQuotient
