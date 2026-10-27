module

public import CFSG.Assembly.OrderReductions.ThompsonNormality
import CFSG.Foundations.MaxOrderThompsonImage
import CFSG.GroupTheory.SylowNaturalCharacteristic

public section

namespace CFSG.OrderReductions.ThompsonCharacteristic

open CFSG.OrderReductions.ThompsonCenter CFSG.OrderReductions.ActionPrimeCore CFSG.OrderReductions.PrimeCore

theorem thompsonCenter_image_map {source target : Type*} [Group source] [Group target]
    (equivalence : source ≃* target) (subgroup : Subgroup source) :
    ((thompsonCenter subgroup).map subgroup.subtype).map equivalence.toMonoidHom =
      (thompsonCenter (subgroup.map equivalence.toMonoidHom)).map
        (subgroup.map equivalence.toMonoidHom).subtype :=
  CFSG.map_maxCardZJ_map_subtype_of_injective equivalence.toMonoidHom subgroup
    (equivalence.injective.comp subgroup.subtype_injective)

theorem thompsonCenter_image_map_sylow {group : Type*} [Group group] [Finite group]
    (prime : ℕ) [Fact (Nat.Prime prime)] (equivalence : MulAut group) (sylow : Sylow prime group) :
    ((thompsonCenter (sylow : Subgroup group)).map (sylow : Subgroup group).subtype).map equivalence.toMonoidHom =
      (thompsonCenter ((Sylow.mapSurjective (f := equivalence.toMonoidHom) equivalence.surjective sylow) : Subgroup group)).map
        ((Sylow.mapSurjective (f := equivalence.toMonoidHom) equivalence.surjective sylow) : Subgroup group).subtype := by
  have mapped := thompsonCenter_image_map equivalence (sylow : Subgroup group)
  rw [← Sylow.coe_mapSurjective (f := equivalence.toMonoidHom) equivalence.surjective sylow] at mapped
  exact mapped

theorem thompsonCenter_image_independent_of_normal {group : Type*} [Group group] [Finite group]
    (prime : ℕ) [Fact (Nat.Prime prime)] (sylow : Sylow prime group)
    (normal : ((thompsonCenter (sylow : Subgroup group)).map (sylow : Subgroup group).subtype).Normal)
    (other : Sylow prime group) :
    (thompsonCenter (other : Subgroup group)).map (other : Subgroup group).subtype =
      (thompsonCenter (sylow : Subgroup group)).map (sylow : Subgroup group).subtype := by
  obtain ⟨conjugator, conjugates⟩ := MulAction.exists_smul_eq group sylow other
  have surjective : Function.Surjective (MulAut.conj conjugator).toMonoidHom := (MulAut.conj conjugator).surjective
  have sylow_eq : sylow.mapSurjective surjective = other := by
    apply Sylow.ext
    rw [Sylow.coe_mapSurjective, ← CFSG.OrderReductions.FixedPairSylow.sylow_smul_subgroup_eq, conjugates]
  have mapped := thompsonCenter_image_map_sylow prime (MulAut.conj conjugator) sylow
  rw [sylow_eq] at mapped
  have : ((thompsonCenter (sylow : Subgroup group)).map (sylow : Subgroup group).subtype).Normal := normal
  have invariant := Subgroup.Normal.map_conj_eq
    ((thompsonCenter (sylow : Subgroup group)).map (sylow : Subgroup group).subtype) conjugator
  exact mapped.symm.trans invariant

theorem thompsonCenter_image_characteristic_of_normal {group : Type*} [Group group] [Finite group]
    (prime : ℕ) [Fact (Nat.Prime prime)] (sylow : Sylow prime group)
    (normal : ((thompsonCenter (sylow : Subgroup group)).map (sylow : Subgroup group).subtype).Normal) :
    ((thompsonCenter (sylow : Subgroup group)).map (sylow : Subgroup group).subtype).Characteristic :=
  have := normal
  CFSG.characteristic_of_normal_of_map_mulEquiv
    (fun subgroup => (thompsonCenter subgroup).map subgroup.subtype)
    (fun automorphism subgroup => thompsonCenter_image_map automorphism subgroup) sylow

theorem glauberman_characteristic {group : Type*} [Group group] [Finite group]
    (prime : ℕ) [Fact (Nat.Prime prime)] (odd_prime : Odd prime) (sylow : Sylow prime group)
    (self_centralizing : Subgroup.centralizer (primeCore prime group : Set group) ≤ primeCore prime group)
    (stable : ∀ normal : Subgroup group, ∀ [normal.Normal], IsPGroup prime normal →
      primeStable prime (conjugationAction normal)) :
    ((thompsonCenter (sylow : Subgroup group)).map (sylow : Subgroup group).subtype).Characteristic :=
  thompsonCenter_image_characteristic_of_normal prime sylow
    (CFSG.OrderReductions.ThompsonNormality.thompsonCenter_image_normal prime odd_prime sylow self_centralizing stable)

end CFSG.OrderReductions.ThompsonCharacteristic
