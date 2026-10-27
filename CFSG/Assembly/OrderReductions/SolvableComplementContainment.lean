module

public import CFSG.Assembly.OrderReductions.SolvablePrimeCore

public section

namespace CFSG.OrderReductions.SolvableComplementContainment

theorem commutator_le_of_normalizes {group : Type*} [Group group]
    (normalizing normalized : Subgroup group)
    (normalizes : normalizing ≤ Subgroup.normalizer (normalized : Set group)) :
    ⁅normalizing, normalized⁆ ≤ normalized := by
  apply Subgroup.commutator_le.mpr
  intro first first_mem second second_mem
  rw [commutatorElement_def]
  exact normalized.mul_mem
    ((Subgroup.mem_normalizer_iff.mp (normalizes first_mem) second).mp second_mem)
    (normalized.inv_mem second_mem)

theorem normalized_complement_eq_bot_of_core_bot {group : Type*}
    [Group group] [Finite group] [Group.IsSolvable group]
    (prime : ℕ) [Fact (Nat.Prime prime)]
    (core_bot : CFSG.OrderReductions.PrimeComplementCore.primeComplementCore prime group = ⊥)
    (sylow : Sylow prime group) (complement : Subgroup group)
    (coprime : ¬ prime ∣ Nat.card complement)
    (normalizes : (sylow : Subgroup group) ≤ Subgroup.normalizer (complement : Set group)) :
    complement = ⊥ := by
  let core := CFSG.OrderReductions.PrimeCore.primeCore prime group
  have disjoint := CFSG.OrderReductions.PrimeCore.disjoint_of_primeComplement prime core complement
    (CFSG.OrderReductions.PrimeCore.primeCore_isPGroup prime group) coprime
  have commutator_le : ⁅core, complement⁆ ≤ core ⊓ complement :=
    le_inf (Subgroup.commutator_le_left core complement)
      (commutator_le_of_normalizes core complement
        ((CFSG.OrderReductions.PrimeCore.primeCore_le_sylow prime sylow).trans normalizes))
  have commutator_bot : ⁅complement, core⁆ = ⊥ := by
    rw [Subgroup.commutator_comm]
    exact le_bot_iff.mp (commutator_le.trans (disjoint_iff_inf_le.mp disjoint))
  have complement_le : complement ≤ core :=
    (Subgroup.commutator_eq_bot_iff_le_centralizer.mp commutator_bot).trans
      (CFSG.OrderReductions.SolvablePrimeCore.centralizer_primeCore_le prime core_bot)
  exact le_bot_iff.mp ((le_inf complement_le le_rfl).trans
    (disjoint_iff_inf_le.mp disjoint))

theorem sylow_normalized_complement_le_core {group : Type*}
    [Group group] [Finite group] [Group.IsSolvable group]
    (prime : ℕ) [Fact (Nat.Prime prime)] (sylow : Sylow prime group)
    (complement : Subgroup group) (coprime : ¬ prime ∣ Nat.card complement)
    (normalizes : (sylow : Subgroup group) ≤ Subgroup.normalizer (complement : Set group)) :
    complement ≤ CFSG.OrderReductions.PrimeComplementCore.primeComplementCore prime group := by
  let core := CFSG.OrderReductions.PrimeComplementCore.primeComplementCore prime group
  let projection := QuotientGroup.mk' core
  let image_sylow := sylow.mapSurjective (QuotientGroup.mk'_surjective core)
  have image_coprime : ¬ prime ∣ Nat.card (complement.map projection) :=
    fun divides => coprime (divides.trans (complement.card_map_dvd projection))
  have image_normalizes : (image_sylow : Subgroup (group ⧸ core)) ≤
      Subgroup.normalizer (↑(complement.map projection) : Set (group ⧸ core)) := by
    rw [Sylow.coe_mapSurjective]
    exact (Subgroup.map_mono normalizes).trans (Subgroup.le_normalizer_map projection)
  have image_bot := normalized_complement_eq_bot_of_core_bot prime
    (CFSG.OrderReductions.PrimeComplementCore.core_quotient_eq_bot prime group)
    image_sylow (complement.map projection) image_coprime image_normalizes
  have kernel_le := (Subgroup.map_eq_bot_iff complement).mp image_bot
  rwa [QuotientGroup.ker_mk'] at kernel_le

theorem full_primePart_core_le {group : Type*}
    [Group group] [Finite group] [Group.IsSolvable group]
    (prime : ℕ) [Fact (Nat.Prime prime)] (subgroup : Subgroup group)
    (full_primePart : CFSG.OrderReductions.PrimePart.primePart prime (Nat.card subgroup) =
      CFSG.OrderReductions.PrimePart.primePart prime (Nat.card group)) :
    CFSG.OrderReductions.PrimeComplementCore.ambientCore prime subgroup ≤
      CFSG.OrderReductions.PrimeComplementCore.primeComplementCore prime group := by
  obtain ⟨internal_sylow⟩ := Sylow.nonempty (p := prime) (G := subgroup)
  let image := (internal_sylow : Subgroup subgroup).map subgroup.subtype
  have image_card : Nat.card image = prime ^ (Nat.card group).factorization prime :=
    (CFSG.OrderReductions.PrimePart.sylow_map_card_eq_primePart prime subgroup internal_sylow).trans full_primePart
  let sylow := Sylow.ofCard image image_card
  have normalizes : subgroup ≤ Subgroup.normalizer
      (CFSG.OrderReductions.PrimeComplementCore.ambientCore prime subgroup : Set group) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer
      (CFSG.OrderReductions.PrimeComplementCore.ambientCore_le prime subgroup)).mp
      (CFSG.OrderReductions.PrimeComplementCore.ambientCore_normal_in_subgroup prime subgroup)
  exact sylow_normalized_complement_le_core prime sylow
    (CFSG.OrderReductions.PrimeComplementCore.ambientCore prime subgroup)
    (CFSG.OrderReductions.PrimeComplementCore.ambientCore_coprime prime subgroup)
    ((Subgroup.map_subtype_le (internal_sylow : Subgroup subgroup)).trans normalizes)

theorem full_primePart_ambientCore_le {group : Type*} [Group group] [Finite group]
    (prime : ℕ) [Fact (Nat.Prime prime)] (smaller larger : Subgroup group)
    [Group.IsSolvable larger] (contains : smaller ≤ larger)
    (full_primePart : CFSG.OrderReductions.PrimePart.primePart prime (Nat.card smaller) =
      CFSG.OrderReductions.PrimePart.primePart prime (Nat.card larger)) :
    CFSG.OrderReductions.PrimeComplementCore.ambientCore prime smaller ≤
      CFSG.OrderReductions.PrimeComplementCore.ambientCore prime larger := by
  let internal := smaller.subgroupOf larger
  let equivalence := Subgroup.subgroupOfEquivOfLe contains
  have internal_full : CFSG.OrderReductions.PrimePart.primePart prime (Nat.card internal) =
      CFSG.OrderReductions.PrimePart.primePart prime (Nat.card larger) := by
    rw [Nat.card_congr equivalence.toEquiv]
    exact full_primePart
  have internal_le := full_primePart_core_le prime internal internal_full
  have image_le := Subgroup.map_mono (f := larger.subtype) internal_le
  have core_eq := CFSG.OrderReductions.PrimeComplementCore.map_core_eq_of_equiv prime equivalence
  have transported := congrArg (Subgroup.map smaller.subtype) core_eq
  rw [Subgroup.map_map] at transported
  have intertwines : smaller.subtype.comp equivalence.toMonoidHom =
      larger.subtype.comp internal.subtype := by
    ext element
    rfl
  rw [intertwines, ← Subgroup.map_map] at transported
  change ((CFSG.OrderReductions.PrimeComplementCore.primeComplementCore prime internal).map
    internal.subtype).map larger.subtype ≤ _ at image_le
  rw [transported] at image_le
  exact image_le

end CFSG.OrderReductions.SolvableComplementContainment
