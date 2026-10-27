module

public import Mathlib
public import Mathlib.Algebra.CharP.Lemmas
public import Mathlib.Algebra.Module.ZMod
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.GroupTheory.Frattini
public import Mathlib.GroupTheory.Subgroup.Center
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.RepresentationTheory.Basic
public import Mathlib.RepresentationTheory.Irreducible
public import Mathlib.RingTheory.TensorProduct.Finite
public import CFSG.Assembly.OrderReductions.OddCore
public import CFSG.Assembly.OrderReductions.PrimeComplementCore
public import CFSG.GroupTheory.PCore.Construction
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PCore

public section

namespace CFSG.OrderReductions.PrimeCore

@[expose] def primeCore (prime : ℕ) (group : Type*) [Group group] : Subgroup group :=
  CFSG.pCore prime group

theorem primeCore_isPGroup (prime : ℕ) (group : Type*) [Group group] :
    IsPGroup prime (primeCore prime group) :=
  CFSG.pCore_isPGroup

instance primeCore_normal (prime : ℕ) (group : Type*) [Group group] :
    (primeCore prime group).Normal :=
  CFSG.pCore_normal

theorem normal_le_primeCore {group : Type*} [Group group] (prime : ℕ)
    (normal : Subgroup group) [normal.Normal] (prime_group : IsPGroup prime normal) :
    normal ≤ primeCore prime group :=
  le_sSup ⟨inferInstance, prime_group⟩

theorem map_core_le_of_surjective {source target : Type*} [Group source] [Group target]
    (prime : ℕ) (homomorphism : source →* target)
    (surjective : Function.Surjective homomorphism) :
    (primeCore prime source).map homomorphism ≤ primeCore prime target := by
  have : ((primeCore prime source).map homomorphism).Normal :=
    (inferInstance : (primeCore prime source).Normal).map homomorphism surjective
  exact normal_le_primeCore prime _ ((primeCore_isPGroup prime source).map homomorphism)

theorem map_core_eq_of_equiv {source target : Type*} [Group source] [Group target]
    (prime : ℕ) (equivalence : source ≃* target) :
    (primeCore prime source).map equivalence.toMonoidHom = primeCore prime target :=
  CFSG.pCore_map_iso prime equivalence

instance primeCore_characteristic (prime : ℕ) (group : Type*) [Group group] :
    (primeCore prime group).Characteristic :=
  Subgroup.characteristic_iff_map_eq.mpr (map_core_eq_of_equiv prime)

theorem primeCore_le_sylow {group : Type*} [Group group] (prime : ℕ)
    [Fact (Nat.Prime prime)] (sylow : Sylow prime group) :
    primeCore prime group ≤ sylow :=
  (primeCore_isPGroup prime group).le_sylow_of_normal sylow

theorem disjoint_of_primeComplement {group : Type*} [Group group] [Finite group]
    (prime : ℕ) [Fact (Nat.Prime prime)] (prime_subgroup complement : Subgroup group)
    (prime_group : IsPGroup prime prime_subgroup)
    (coprime : ¬ prime ∣ Nat.card complement) : Disjoint prime_subgroup complement := by
  obtain ⟨exponent, card_eq⟩ := IsPGroup.iff_card.mp prime_group
  have cards_coprime : (Nat.card prime_subgroup).Coprime (Nat.card complement) := by
    rw [card_eq]
    exact ((Fact.out : Nat.Prime prime).coprime_pow_of_not_dvd coprime).symm
  apply disjoint_iff_inf_le.mpr
  have inf_card_dvd : Nat.card ↥(prime_subgroup ⊓ complement) ∣
      Nat.gcd (Nat.card prime_subgroup) (Nat.card complement) :=
    Nat.dvd_gcd (Subgroup.card_dvd_of_le inf_le_left) (Subgroup.card_dvd_of_le inf_le_right)
  rw [cards_coprime.gcd_eq_one, Nat.dvd_one, Subgroup.card_eq_one] at inf_card_dvd
  exact inf_card_dvd.le

theorem nilpotent_normal_le_primeCore {group : Type*} [Group group] [Finite group]
    (prime : ℕ) [Fact (Nat.Prime prime)]
    (core_bot : CFSG.OrderReductions.PrimeComplementCore.primeComplementCore prime group = ⊥)
    (normal : Subgroup group) [normal.Normal] [Group.IsNilpotent normal] :
    normal ≤ primeCore prime group := by
  have normal_prime_group : IsPGroup prime normal := by
    apply IsPGroup.iff_card.mpr
    refine ⟨_, Nat.eq_prime_pow_of_unique_prime_dvd (ne_of_gt Nat.card_pos) ?_⟩
    intro divisor divisor_prime divisor_dvd
    by_contra distinct
    have : Fact (Nat.Prime divisor) := ⟨divisor_prime⟩
    obtain ⟨sylow⟩ := Sylow.nonempty (p := divisor) (G := normal)
    have sylow_normal : (sylow : Subgroup normal).Normal :=
      Sylow.normal_of_normalizerCondition (Group.normalizerCondition_of_isNilpotent) sylow
    have : (sylow : Subgroup normal).Characteristic := sylow.characteristic_of_normal sylow_normal
    have : ((sylow : Subgroup normal).map normal.subtype).Normal :=
      CFSG.OrderReductions.OddCore.characteristic_subgroup_map_normal normal _
    have image_coprime : ¬ prime ∣ Nat.card ((sylow : Subgroup normal).map normal.subtype) := by
      rw [Subgroup.card_map_of_injective Subtype.val_injective, sylow.card_eq_multiplicity]
      intro divides
      exact distinct ((divisor_prime.dvd_iff_eq (Fact.out : Nat.Prime prime).ne_one).mp
        ((Fact.out : Nat.Prime prime).dvd_of_dvd_pow divides))
    have image_le := CFSG.OrderReductions.PrimeComplementCore.normal_le_primeComplementCore prime
      ((sylow : Subgroup normal).map normal.subtype) image_coprime
    rw [core_bot] at image_le
    have image_eq := le_bot_iff.mp image_le
    have trivial_card : Nat.card (sylow : Subgroup normal) = 1 := by
      rw [← Subgroup.card_map_of_injective (f := normal.subtype) Subtype.val_injective, image_eq,
        Subgroup.card_bot]
    have divides := sylow.dvd_card_of_dvd_card divisor_dvd
    rw [trivial_card] at divides
    exact divisor_prime.not_dvd_one divides
  exact normal_le_primeCore prime normal normal_prime_group

end CFSG.OrderReductions.PrimeCore
