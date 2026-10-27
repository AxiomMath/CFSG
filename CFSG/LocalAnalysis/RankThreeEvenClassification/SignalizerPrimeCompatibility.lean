module

public import CFSG.LocalAnalysis.RankThreeEvenClassification.InvariantConjugacy
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerProducts

public section

open CFSG.Open

namespace CFSG.RankThreeEvenClassification.Helpers

universe u

@[expose] def SignalizerPrimeCompatible {G : Type u} [Group G]
    (prime subgroupPrime : ℕ) (actor : Subgroup G) (signalizer : G → Subgroup G)
    (subgroup : Subgroup G) : Prop :=
  SignalizerCompatible prime actor signalizer subgroup ∧ IsPGroup subgroupPrime subgroup

@[expose] def CommonFixedConjugate {G : Type u} [Group G]
    (actor : Subgroup G) (signalizer : G → Subgroup G) (first second : Subgroup G) : Prop :=
  ∃ conjugator ∈ signalizerCommonFixed actor signalizer,
    first.map (MulAut.conj conjugator).toMonoidHom = second

theorem subgroup_map_conj_one {G : Type u} [Group G] (subgroup : Subgroup G) :
    subgroup.map (MulAut.conj (1 : G)).toMonoidHom = subgroup := by
  have hone : (MulAut.conj (1 : G)).toMonoidHom = MonoidHom.id G := by
    ext element
    simp
  rw [hone, Subgroup.map_id]

theorem subgroup_map_conj_inv_cancel {G : Type u} [Group G]
    (subgroup : Subgroup G) (conjugator : G) :
    (subgroup.map (MulAut.conj conjugator).toMonoidHom).map
      (MulAut.conj conjugator⁻¹).toMonoidHom = subgroup := by
  rw [← subgroup_map_conj_mul, inv_mul_cancel, subgroup_map_conj_one]

theorem CommonFixedConjugate.refl {G : Type u} [Group G]
    (actor : Subgroup G) (signalizer : G → Subgroup G) (subgroup : Subgroup G) :
    CommonFixedConjugate actor signalizer subgroup subgroup :=
  ⟨1, (signalizerCommonFixed actor signalizer).one_mem, subgroup_map_conj_one subgroup⟩

theorem CommonFixedConjugate.symm {G : Type u} [Group G]
    (actor : Subgroup G) (signalizer : G → Subgroup G) (first second : Subgroup G)
    (hconjugate : CommonFixedConjugate actor signalizer first second) :
    CommonFixedConjugate actor signalizer second first := by
  obtain ⟨conjugator, hmem, heq⟩ := hconjugate
  refine ⟨conjugator⁻¹, (signalizerCommonFixed actor signalizer).inv_mem hmem, ?_⟩
  rw [← heq, subgroup_map_conj_inv_cancel]

theorem CommonFixedConjugate.trans {G : Type u} [Group G]
    (actor : Subgroup G) (signalizer : G → Subgroup G) (first second third : Subgroup G)
    (hfirst : CommonFixedConjugate actor signalizer first second)
    (hsecond : CommonFixedConjugate actor signalizer second third) :
    CommonFixedConjugate actor signalizer first third := by
  obtain ⟨firstConjugator, hfirstMem, hfirstEq⟩ := hfirst
  obtain ⟨secondConjugator, hsecondMem, hsecondEq⟩ := hsecond
  refine ⟨secondConjugator * firstConjugator,
    (signalizerCommonFixed actor signalizer).mul_mem hsecondMem hfirstMem, ?_⟩
  rw [subgroup_map_conj_mul, hfirstEq, hsecondEq]

theorem SignalizerPrimeCompatible.bot {G : Type u} [Group G]
    (prime : ℕ) (hprime : prime.Prime) (subgroupPrime : ℕ)
    (actor : Subgroup G) (signalizer : G → Subgroup G) :
    SignalizerPrimeCompatible prime subgroupPrime actor signalizer ⊥ :=
  ⟨SignalizerCompatible.bot prime hprime actor signalizer, IsPGroup.of_subsingleton _ _⟩

theorem SignalizerPrimeCompatible.of_le {G : Type u} [Group G] [Finite G]
    (prime subgroupPrime : ℕ) (actor : Subgroup G) (signalizer : G → Subgroup G)
    (subgroup smaller : Subgroup G)
    (hcompatible : SignalizerPrimeCompatible prime subgroupPrime actor signalizer subgroup)
    (hle : smaller ≤ subgroup) (hnormalized : actor ≤ Subgroup.normalizer (smaller : Set G)) :
    SignalizerPrimeCompatible prime subgroupPrime actor signalizer smaller :=
  ⟨SignalizerCompatible.of_le prime actor signalizer subgroup smaller hcompatible.1 hle hnormalized,
    hcompatible.2.to_le hle⟩

theorem SignalizerPrimeCompatible.normalized_sup {G : Type u} [Group G] [Finite G]
    (prime : ℕ) (hprime : prime.Prime) (subgroupPrime : ℕ)
    (actor : Subgroup G) (signalizer : G → Subgroup G) (hpgroup : IsPGroup prime actor)
    (first second : Subgroup G)
    (hfirst : SignalizerPrimeCompatible prime subgroupPrime actor signalizer first)
    (hsecond : SignalizerPrimeCompatible prime subgroupPrime actor signalizer second)
    (hnormalizes : second ≤ Subgroup.normalizer (first : Set G)) :
    SignalizerPrimeCompatible prime subgroupPrime actor signalizer (first ⊔ second) :=
  ⟨SignalizerCompatible.normalized_sup prime hprime actor signalizer hpgroup first second
      hfirst.1 hsecond.1 hnormalizes,
    hfirst.2.to_sup_of_normal_left' hsecond.2 hnormalizes⟩

theorem SignalizerPrimeCompatible.conjugate_by_common_fixed
    {G : Type u} [Group G] [Finite G]
    (prime subgroupPrime : ℕ) (actor : Subgroup G) (signalizer : G → Subgroup G)
    (hsignalizer : IsSolvableSignalizerFunctor prime actor signalizer)
    (subgroup : Subgroup G)
    (hcompatible : SignalizerPrimeCompatible prime subgroupPrime actor signalizer subgroup)
    (conjugator : G) (hconjugator : conjugator ∈ signalizerCommonFixed actor signalizer) :
    SignalizerPrimeCompatible prime subgroupPrime actor signalizer
      (subgroup.map (MulAut.conj conjugator).toMonoidHom) :=
  ⟨SignalizerCompatible.conjugate_by_common_fixed prime actor signalizer hsignalizer
      subgroup hcompatible.1 conjugator hconjugator,
    hcompatible.2.map _⟩

theorem exists_maximal_signalizer_prime_compatible_above
    {G : Type u} [Group G] [Finite G]
    (prime subgroupPrime : ℕ) (actor : Subgroup G) (signalizer : G → Subgroup G)
    (subgroup : Subgroup G)
    (hcompatible : SignalizerPrimeCompatible prime subgroupPrime actor signalizer subgroup) :
    ∃ maximal : Subgroup G, subgroup ≤ maximal ∧
      Maximal (SignalizerPrimeCompatible prime subgroupPrime actor signalizer) maximal :=
  Finite.exists_le_maximal hcompatible

theorem maximal_signalizer_prime_compatible_conjugate
    {G : Type u} [Group G] [Finite G]
    (prime subgroupPrime : ℕ) (actor : Subgroup G) (signalizer : G → Subgroup G)
    (hsignalizer : IsSolvableSignalizerFunctor prime actor signalizer)
    (subgroup : Subgroup G)
    (hmaximal : Maximal (SignalizerPrimeCompatible prime subgroupPrime actor signalizer) subgroup)
    (conjugator : G) (hconjugator : conjugator ∈ signalizerCommonFixed actor signalizer) :
    Maximal (SignalizerPrimeCompatible prime subgroupPrime actor signalizer)
      (subgroup.map (MulAut.conj conjugator).toMonoidHom) := by
  refine ⟨SignalizerPrimeCompatible.conjugate_by_common_fixed prime subgroupPrime actor signalizer
    hsignalizer subgroup hmaximal.1 conjugator hconjugator, ?_⟩
  intro larger hlarger hle
  have hinverseCompatible := SignalizerPrimeCompatible.conjugate_by_common_fixed prime subgroupPrime
    actor signalizer hsignalizer larger hlarger conjugator⁻¹
      ((signalizerCommonFixed actor signalizer).inv_mem hconjugator)
  have hinverseLe := Subgroup.map_mono (f := (MulAut.conj conjugator⁻¹).toMonoidHom) hle
  rw [subgroup_map_conj_inv_cancel] at hinverseLe
  have hreverse := hmaximal.2 hinverseCompatible hinverseLe
  have hmapped := Subgroup.map_mono (f := (MulAut.conj conjugator).toMonoidHom) hreverse
  rw [← subgroup_map_conj_mul, mul_inv_cancel, subgroup_map_conj_one] at hmapped
  exact hmapped

theorem subgroup_card_lt_of_lt {G : Type u} [Group G] [Finite G]
    (first second : Subgroup G) (hstrict : first < second) : Nat.card first < Nat.card second := by
  classical
  let : Fintype first := Fintype.ofFinite _
  let : Fintype second := Fintype.ofFinite _
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  apply Fintype.card_lt_of_injective_not_surjective (Subgroup.inclusion hstrict.le)
    (Subgroup.inclusion_injective hstrict.le)
  intro hsurjective
  apply hstrict.not_ge
  intro element helement
  obtain ⟨preimage, hpreimage⟩ := hsurjective ⟨element, helement⟩
  have heq : (preimage : G) = element := congrArg Subtype.val hpreimage
  exact heq ▸ preimage.property

end CFSG.RankThreeEvenClassification.Helpers
