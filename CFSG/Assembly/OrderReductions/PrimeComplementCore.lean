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
public import CFSG.Assembly.OrderReductions.StrongEmbeddingInheritance
public import CFSG.Assembly.OrderReductions.OddCore

public section

namespace CFSG.OrderReductions.PrimeComplementCore

@[expose] def PrimeComplementNormal {group : Type*} [Group group] (prime : ℕ)
    (subgroup : Subgroup group) : Prop := subgroup.Normal ∧ ¬ prime ∣ Nat.card subgroup

theorem primeComplement_sup {group : Type*} [Group group] [Finite group]
    (prime : ℕ) [Fact (Nat.Prime prime)] (first second : Subgroup group) [first.Normal]
    (first_coprime : ¬ prime ∣ Nat.card first) (second_coprime : ¬ prime ∣ Nat.card second) :
    ¬ prime ∣ Nat.card ↥(first ⊔ second) := by
  let projection := QuotientGroup.mk' first
  have image_eq : (first ⊔ second).map projection = second.map projection := by
    rw [Subgroup.map_sup, QuotientGroup.map_mk'_self, bot_sup_eq]
  have image_coprime : ¬ prime ∣ Nat.card ((first ⊔ second).map projection) := by
    rw [image_eq]
    exact fun divides => second_coprime (divides.trans (second.card_map_dvd projection))
  have kernel_coprime : ¬ prime ∣ Nat.card (projection.ker.subgroupOf (first ⊔ second)) := by
    change ¬ prime ∣ Nat.card ((QuotientGroup.mk' first).ker.subgroupOf (first ⊔ second))
    rw [QuotientGroup.ker_mk', Nat.card_congr
      (Subgroup.subgroupOfEquivOfLe (show first ≤ first ⊔ second from le_sup_left)).toEquiv]
    exact first_coprime
  rw [← CFSG.OrderReductions.StrongEmbeddingInheritance.map_card_mul_kernel_card projection (first ⊔ second),
    (Fact.out : Nat.Prime prime).dvd_mul]
  exact not_or.mpr ⟨image_coprime, kernel_coprime⟩

theorem exists_greatest_primeComplement_normal {group : Type*} [Group group] [Finite group]
    (prime : ℕ) [Fact (Nat.Prime prime)] :
    ∃ core : Subgroup group, PrimeComplementNormal prime core ∧
      ∀ normal : Subgroup group, PrimeComplementNormal prime normal → normal ≤ core := by
  have bot_prop : PrimeComplementNormal prime (⊥ : Subgroup group) := by
    refine ⟨inferInstance, ?_⟩
    rw [Subgroup.card_bot]
    exact (Fact.out : Nat.Prime prime).not_dvd_one
  obtain ⟨core, _, maximal⟩ := Finite.exists_le_maximal bot_prop
  refine ⟨core, maximal.prop, ?_⟩
  intro normal normal_prop
  have := maximal.prop.1
  have := normal_prop.1
  have sup_prop : PrimeComplementNormal prime (core ⊔ normal) :=
    ⟨inferInstance, primeComplement_sup prime core normal maximal.prop.2 normal_prop.2⟩
  have equal_sup := maximal.eq_of_le sup_prop le_sup_left
  rw [equal_sup]
  exact le_sup_right

@[expose] noncomputable def primeComplementCore (prime : ℕ) (group : Type*) [Group group] [Finite group]
    [Fact (Nat.Prime prime)] : Subgroup group :=
  Classical.choose (exists_greatest_primeComplement_normal (group := group) prime)

theorem primeComplementCore_coprime (prime : ℕ) (group : Type*) [Group group] [Finite group]
    [Fact (Nat.Prime prime)] : ¬ prime ∣ Nat.card (primeComplementCore prime group) :=
  (Classical.choose_spec (exists_greatest_primeComplement_normal (group := group) prime)).1.2

instance primeComplementCore_normal (prime : ℕ) (group : Type*) [Group group] [Finite group]
    [Fact (Nat.Prime prime)] : (primeComplementCore prime group).Normal :=
  (Classical.choose_spec (exists_greatest_primeComplement_normal (group := group) prime)).1.1

theorem normal_le_primeComplementCore {group : Type*} [Group group] [Finite group]
    (prime : ℕ) [Fact (Nat.Prime prime)] (normal : Subgroup group) [normal.Normal]
    (coprime : ¬ prime ∣ Nat.card normal) : normal ≤ primeComplementCore prime group :=
  (Classical.choose_spec (exists_greatest_primeComplement_normal (group := group) prime)).2 normal
    ⟨inferInstance, coprime⟩

theorem map_core_le_of_surjective {source target : Type*}
    [Group source] [Finite source] [Group target] [Finite target]
    (prime : ℕ) [Fact (Nat.Prime prime)] (homomorphism : source →* target)
    (surjective : Function.Surjective homomorphism) :
    (primeComplementCore prime source).map homomorphism ≤ primeComplementCore prime target := by
  have := (inferInstance : (primeComplementCore prime source).Normal).map homomorphism surjective
  exact normal_le_primeComplementCore prime _ (fun divides =>
    primeComplementCore_coprime prime source
      (divides.trans ((primeComplementCore prime source).card_map_dvd homomorphism)))

theorem map_core_eq_of_equiv {source target : Type*}
    [Group source] [Finite source] [Group target] [Finite target]
    (prime : ℕ) [Fact (Nat.Prime prime)] (equivalence : source ≃* target) :
    (primeComplementCore prime source).map equivalence.toMonoidHom =
      primeComplementCore prime target := by
  apply le_antisymm (map_core_le_of_surjective prime equivalence.toMonoidHom equivalence.surjective)
  have reverse := Subgroup.map_mono (f := equivalence.toMonoidHom)
    (map_core_le_of_surjective prime equivalence.symm.toMonoidHom equivalence.symm.surjective)
  have composite : equivalence.toMonoidHom.comp equivalence.symm.toMonoidHom =
      MonoidHom.id target := by
    ext element
    exact equivalence.apply_symm_apply element
  rwa [Subgroup.map_map, composite, Subgroup.map_id] at reverse

instance primeComplementCore_characteristic (prime : ℕ) (group : Type*) [Group group] [Finite group]
    [Fact (Nat.Prime prime)] : (primeComplementCore prime group).Characteristic :=
  Subgroup.characteristic_iff_map_eq.mpr (map_core_eq_of_equiv prime)

theorem primeComplement_preimage {source target : Type*}
    [Group source] [Finite source] [Group target]
    (prime : ℕ) [Fact (Nat.Prime prime)] (homomorphism : source →* target)
    (surjective : Function.Surjective homomorphism) (kernel_coprime : ¬ prime ∣ Nat.card homomorphism.ker)
    (subgroup : Subgroup target) (subgroup_coprime : ¬ prime ∣ Nat.card subgroup) :
    ¬ prime ∣ Nat.card (subgroup.comap homomorphism) := by
  have image_eq := Subgroup.map_comap_eq_self_of_surjective surjective subgroup
  have image_coprime : ¬ prime ∣ Nat.card ((subgroup.comap homomorphism).map homomorphism) := by
    rwa [image_eq]
  have kernel_le : homomorphism.ker ≤ subgroup.comap homomorphism := by
    intro element element_mem
    change homomorphism element ∈ subgroup
    rw [MonoidHom.mem_ker.mp element_mem]
    exact subgroup.one_mem
  have internal_kernel_coprime : ¬ prime ∣
      Nat.card (homomorphism.ker.subgroupOf (subgroup.comap homomorphism)) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe kernel_le).toEquiv]
    exact kernel_coprime
  rw [← CFSG.OrderReductions.StrongEmbeddingInheritance.map_card_mul_kernel_card homomorphism
    (subgroup.comap homomorphism), (Fact.out : Nat.Prime prime).dvd_mul]
  exact not_or.mpr ⟨image_coprime, internal_kernel_coprime⟩

theorem core_quotient_eq_bot (prime : ℕ) (group : Type*) [Group group] [Finite group]
    [Fact (Nat.Prime prime)] :
    primeComplementCore prime (group ⧸ primeComplementCore prime group) = ⊥ := by
  let projection := QuotientGroup.mk' (primeComplementCore prime group)
  let quotient_core := primeComplementCore prime (group ⧸ primeComplementCore prime group)
  let preimage := quotient_core.comap projection
  have : preimage.Normal := (inferInstance : quotient_core.Normal).comap projection
  have kernel_coprime : ¬ prime ∣ Nat.card projection.ker := by
    rw [QuotientGroup.ker_mk']
    exact primeComplementCore_coprime prime group
  have preimage_coprime : ¬ prime ∣ Nat.card preimage := primeComplement_preimage prime projection
    (QuotientGroup.mk'_surjective _) kernel_coprime quotient_core (primeComplementCore_coprime prime _)
  have preimage_le := normal_le_primeComplementCore prime preimage preimage_coprime
  have image_le := Subgroup.map_mono (f := projection) preimage_le
  rw [Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _),
    QuotientGroup.map_mk'_self] at image_le
  exact le_antisymm image_le bot_le

theorem normal_subgroup_core_map_le {group : Type*} [Group group] [Finite group]
    (prime : ℕ) [Fact (Nat.Prime prime)] (normal : Subgroup group) [normal.Normal] :
    (primeComplementCore prime normal).map normal.subtype ≤ primeComplementCore prime group := by
  have : ((primeComplementCore prime normal).map normal.subtype).Normal :=
    CFSG.OrderReductions.OddCore.characteristic_subgroup_map_normal normal (primeComplementCore prime normal)
  apply normal_le_primeComplementCore prime
  rw [Subgroup.card_map_of_injective Subtype.val_injective]
  exact primeComplementCore_coprime prime normal

theorem primeComplementCore_two_eq_oddCore (group : Type*) [Group group] [Finite group] :
    let prime_two : Fact (Nat.Prime 2) := ⟨by decide⟩
    primeComplementCore 2 group = CFSG.OrderReductions.OddCore.oddCore group := by
  have : Fact (Nat.Prime 2) := ⟨by decide⟩
  apply le_antisymm
  · apply CFSG.OrderReductions.OddCore.normal_le_oddCore
    exact Nat.not_even_iff_odd.mp (fun even_core => primeComplementCore_coprime 2 group even_core.two_dvd)
  · exact normal_le_primeComplementCore 2 _ (CFSG.OrderReductions.OddCore.oddCore_odd group).not_two_dvd_nat

@[expose] noncomputable def ambientCore {group : Type*} [Group group] [Finite group]
    (prime : ℕ) [Fact (Nat.Prime prime)] (subgroup : Subgroup group) : Subgroup group :=
  (primeComplementCore prime subgroup).map subgroup.subtype

theorem ambientCore_le {group : Type*} [Group group] [Finite group]
    (prime : ℕ) [Fact (Nat.Prime prime)] (subgroup : Subgroup group) :
    ambientCore prime subgroup ≤ subgroup := by
  intro element element_mem
  obtain ⟨original, _, image_eq⟩ := Subgroup.mem_map.mp element_mem
  exact image_eq ▸ original.property

theorem ambientCore_coprime {group : Type*} [Group group] [Finite group]
    (prime : ℕ) [Fact (Nat.Prime prime)] (subgroup : Subgroup group) :
    ¬ prime ∣ Nat.card (ambientCore prime subgroup) := by
  rw [ambientCore, Subgroup.card_map_of_injective Subtype.val_injective]
  exact primeComplementCore_coprime prime subgroup

theorem ambientCore_normal_in_subgroup {group : Type*} [Group group] [Finite group]
    (prime : ℕ) [Fact (Nat.Prime prime)] (subgroup : Subgroup group) :
    ((ambientCore prime subgroup).subgroupOf subgroup).Normal := by
  have equal_core : (ambientCore prime subgroup).subgroupOf subgroup =
      primeComplementCore prime subgroup := by
    change ((primeComplementCore prime subgroup).map subgroup.subtype).comap subgroup.subtype = _
    exact Subgroup.comap_map_eq_self_of_injective Subtype.val_injective _
  rw [equal_core]
  infer_instance

theorem normal_le_ambientCore {group : Type*} [Group group] [Finite group]
    (prime : ℕ) [Fact (Nat.Prime prime)] (normal ambient : Subgroup group)
    (contains : normal ≤ ambient) [(normal.subgroupOf ambient).Normal]
    (coprime : ¬ prime ∣ Nat.card normal) : normal ≤ ambientCore prime ambient := by
  have internal_coprime : ¬ prime ∣ Nat.card (normal.subgroupOf ambient) := by
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe contains).toEquiv]
  have internal_le := normal_le_primeComplementCore prime (normal.subgroupOf ambient) internal_coprime
  have image_le := Subgroup.map_mono (f := ambient.subtype) internal_le
  rwa [Subgroup.map_subgroupOf_eq_of_le contains] at image_le

theorem ambientCore_map_equiv {source target : Type*}
    [Group source] [Finite source] [Group target] [Finite target]
    (prime : ℕ) [Fact (Nat.Prime prime)] (equivalence : source ≃* target)
    (subgroup : Subgroup source) :
    (ambientCore prime subgroup).map equivalence.toMonoidHom =
      ambientCore prime (subgroup.map equivalence.toMonoidHom) := by
  let restricted : subgroup ≃* subgroup.map equivalence.toMonoidHom := equivalence.subgroupMap subgroup
  have core_eq : (primeComplementCore prime subgroup).map restricted.toMonoidHom =
      primeComplementCore prime (subgroup.map equivalence.toMonoidHom) :=
    map_core_eq_of_equiv prime restricted
  have image_eq := congrArg (Subgroup.map (subgroup.map equivalence.toMonoidHom).subtype) core_eq
  rw [Subgroup.map_map] at image_eq
  have intertwines : (subgroup.map equivalence.toMonoidHom).subtype.comp restricted.toMonoidHom =
      equivalence.toMonoidHom.comp subgroup.subtype := by
    ext element
    rfl
  rw [intertwines, ← Subgroup.map_map] at image_eq
  exact image_eq

theorem ambientCore_le_ambientCore_of_normal_inclusion {group : Type*}
    [Group group] [Finite group] (prime : ℕ) [Fact (Nat.Prime prime)]
    (smaller larger : Subgroup group) (contains : smaller ≤ larger)
    [(smaller.subgroupOf larger).Normal] :
    ambientCore prime smaller ≤ ambientCore prime larger := by
  let internal := smaller.subgroupOf larger
  let equivalence := Subgroup.subgroupOfEquivOfLe contains
  have internal_le := normal_subgroup_core_map_le prime internal
  have image_le := Subgroup.map_mono (f := larger.subtype) internal_le
  rw [Subgroup.map_map] at image_le
  have core_eq := map_core_eq_of_equiv prime equivalence
  have core_image_eq := congrArg (Subgroup.map smaller.subtype) core_eq
  rw [Subgroup.map_map] at core_image_eq
  have intertwines : smaller.subtype.comp equivalence.toMonoidHom =
      larger.subtype.comp internal.subtype := by
    ext element
    rfl
  rw [intertwines] at core_image_eq
  rw [core_image_eq] at image_le
  exact image_le

theorem core_preimage_eq_of_coprime_kernel {source target : Type*}
    [Group source] [Finite source] [Group target] [Finite target]
    (prime : ℕ) [Fact (Nat.Prime prime)] (homomorphism : source →* target)
    (surjective : Function.Surjective homomorphism) (kernel_coprime : ¬ prime ∣ Nat.card homomorphism.ker) :
    (primeComplementCore prime target).comap homomorphism = primeComplementCore prime source := by
  apply le_antisymm
  · have : ((primeComplementCore prime target).comap homomorphism).Normal :=
      (inferInstance : (primeComplementCore prime target).Normal).comap homomorphism
    exact normal_le_primeComplementCore prime _ (primeComplement_preimage prime homomorphism
      surjective kernel_coprime _ (primeComplementCore_coprime prime target))
  · exact Subgroup.map_le_iff_le_comap.mp (map_core_le_of_surjective prime homomorphism surjective)

theorem core_image_eq_of_coprime_kernel {source target : Type*}
    [Group source] [Finite source] [Group target] [Finite target]
    (prime : ℕ) [Fact (Nat.Prime prime)] (homomorphism : source →* target)
    (surjective : Function.Surjective homomorphism) (kernel_coprime : ¬ prime ∣ Nat.card homomorphism.ker) :
    (primeComplementCore prime source).map homomorphism = primeComplementCore prime target := by
  rw [← core_preimage_eq_of_coprime_kernel prime homomorphism surjective kernel_coprime,
    Subgroup.map_comap_eq_self_of_surjective surjective]

end CFSG.OrderReductions.PrimeComplementCore
