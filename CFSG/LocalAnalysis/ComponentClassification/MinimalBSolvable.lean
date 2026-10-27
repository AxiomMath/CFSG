module

public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBTwoCore
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.MinimalNormal

public section

open CFSG.Open

namespace CFSG.ComponentClassification.MinimalBSolvable

theorem odd_elementaryAbelian {G : Type*} [Group G] [Finite G]
    (hsmaller : ∀ (subgroup : Subgroup G) (_ : subgroup.Normal),
      Nat.card (G ⧸ subgroup) < Nat.card G → CentralTwoBInclusion.Property (G ⧸ subgroup))
    (hproper : ∀ subgroup : Subgroup G, subgroup ≠ ⊤ → CentralTwoBInclusion.Property subgroup)
    (hfailure : ¬ CentralTwoBInclusion.Property G)
    (subgroup : Subgroup G) (hminimal : MinimalNormal.Property subgroup)
    [Group.IsSolvable subgroup] :
    ∃ prime dimension : ℕ, prime.Prime ∧ Odd prime ∧ 0 < dimension ∧
      IsElemAbelian prime subgroup ∧ Nat.card subgroup = prime ^ dimension := by
  let : subgroup.Normal := hminimal.prop.1
  obtain ⟨prime, hprime, helementary, hprimeGroup⟩ :=
    MinimalNormal.elementaryAbelian_of_solvable subgroup hminimal
  let : Fact prime.Prime := ⟨hprime⟩
  have hodd : Odd prime := by
    rcases hprime.eq_two_or_odd' with rfl | hodd
    · exact (hminimal.prop.2 (MinimalBTwoCore.normal_two_eq_bot
        (MinimalBCenter.odd_center hsmaller hfailure) hproper hfailure subgroup hprimeGroup)).elim
    · exact hodd
  let : Nontrivial subgroup := subgroup.nontrivial_iff_ne_bot.mpr hminimal.prop.2
  obtain ⟨dimension, hpositive, hcard⟩ := (hprimeGroup.nontrivial_iff_card).mp inferInstance
  exact ⟨prime, dimension, hprime, hodd, hpositive, helementary, hcard⟩

theorem odd_card {G : Type*} [Group G] [Finite G]
    (hsmaller : ∀ (subgroup : Subgroup G) (_ : subgroup.Normal),
      Nat.card (G ⧸ subgroup) < Nat.card G → CentralTwoBInclusion.Property (G ⧸ subgroup))
    (hproper : ∀ subgroup : Subgroup G, subgroup ≠ ⊤ → CentralTwoBInclusion.Property subgroup)
    (hfailure : ¬ CentralTwoBInclusion.Property G)
    (subgroup : Subgroup G) (hminimal : MinimalNormal.Property subgroup)
    [Group.IsSolvable subgroup] : Odd (Nat.card subgroup) := by
  obtain ⟨prime, dimension, _, hodd, _, _, hcard⟩ :=
    odd_elementaryAbelian hsmaller hproper hfailure subgroup hminimal
  rw [hcard]
  exact hodd.pow

theorem minimal_eq {G : Type*} [Group G] [Finite G]
    (hsmaller : ∀ (subgroup : Subgroup G) (_ : subgroup.Normal),
      Nat.card (G ⧸ subgroup) < Nat.card G → CentralTwoBInclusion.Property (G ⧸ subgroup))
    (hproper : ∀ subgroup : Subgroup G, subgroup ≠ ⊤ → CentralTwoBInclusion.Property subgroup)
    (hfailure : ¬ CentralTwoBInclusion.Property G)
    (first second : Subgroup G)
    (hfirst : MinimalNormal.Property first) (hsecond : MinimalNormal.Property second)
    [Group.IsSolvable first] [Group.IsSolvable second] : first = second := by
  classical
  let : first.Normal := hfirst.prop.1
  let : second.Normal := hsecond.prop.1
  by_cases hintersection : first ⊓ second = ⊥
  · let firstProjection := QuotientGroup.mk' first
    let secondProjection := QuotientGroup.mk' second
    have hfirstKernel : firstProjection.ker = first := QuotientGroup.ker_mk' first
    have hsecondKernel : secondProjection.ker = second := QuotientGroup.ker_mk' second
    let : Group.IsSolvable firstProjection.ker := by rw [hfirstKernel]; infer_instance
    let : Group.IsSolvable secondProjection.ker := by rw [hsecondKernel]; infer_instance
    have hfirstB := hsmaller first inferInstance
      (MinimalBCenter.quotient_card_lt first hfirst.prop.2)
    have hsecondB := hsmaller second inferInstance
      (MinimalBCenter.quotient_card_lt second hsecond.prop.2)
    apply (hfailure _).elim
    exact DisjointSolvableKernels.inclusion firstProjection secondProjection
      (QuotientGroup.mk'_surjective _) (QuotientGroup.mk'_surjective _)
      (by rw [hfirstKernel]; exact odd_card hsmaller hproper hfailure first hfirst)
      (by rw [hsecondKernel]; exact odd_card hsmaller hproper hfailure second hsecond)
      (by rwa [hfirstKernel, hsecondKernel]) hfirstB hsecondB
  · have hfirstEq : first = first ⊓ second :=
      (minimal_iff.mp hfirst).2 ⟨inferInstance, hintersection⟩ inf_le_left
    have hsecondEq : second = first ⊓ second :=
      (minimal_iff.mp hsecond).2 ⟨inferInstance, hintersection⟩ inf_le_right
    exact hfirstEq.trans hsecondEq.symm

theorem le_every_solvable_normal {G : Type*} [Group G] [Finite G]
    (hsmaller : ∀ (subgroup : Subgroup G) (_ : subgroup.Normal),
      Nat.card (G ⧸ subgroup) < Nat.card G → CentralTwoBInclusion.Property (G ⧸ subgroup))
    (hproper : ∀ subgroup : Subgroup G, subgroup ≠ ⊤ → CentralTwoBInclusion.Property subgroup)
    (hfailure : ¬ CentralTwoBInclusion.Property G)
    (subgroup : Subgroup G) (hminimal : MinimalNormal.Property subgroup)
    [Group.IsSolvable subgroup]
    (overgroup : Subgroup G) [overgroup.Normal] [Group.IsSolvable overgroup]
    (hne : overgroup ≠ ⊥) : subgroup ≤ overgroup := by
  obtain ⟨other, hle, hother⟩ := MinimalNormal.exists_le overgroup hne
  let : Group.IsSolvable other :=
    Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hle)
  rw [minimal_eq hsmaller hproper hfailure subgroup other hminimal hother]
  exact hle

theorem characteristic {G : Type*} [Group G] [Finite G]
    (hsmaller : ∀ (subgroup : Subgroup G) (_ : subgroup.Normal),
      Nat.card (G ⧸ subgroup) < Nat.card G → CentralTwoBInclusion.Property (G ⧸ subgroup))
    (hproper : ∀ subgroup : Subgroup G, subgroup ≠ ⊤ → CentralTwoBInclusion.Property subgroup)
    (hfailure : ¬ CentralTwoBInclusion.Property G)
    (subgroup : Subgroup G) (hminimal : MinimalNormal.Property subgroup)
    [Group.IsSolvable subgroup] : subgroup.Characteristic := by
  apply Subgroup.characteristic_iff_map_eq.mpr
  intro automorphism
  let equivalence := subgroup.equivMapOfInjective automorphism.toMonoidHom automorphism.injective
  let : Group.IsSolvable (subgroup.map automorphism.toMonoidHom) :=
    Group.isSolvable_of_surjective (f := equivalence.toMonoidHom) equivalence.surjective
  exact minimal_eq hsmaller hproper hfailure (subgroup.map automorphism.toMonoidHom) subgroup
    (MinimalNormal.equiv_image automorphism subgroup hminimal) hminimal

theorem exists_characteristic_le {G : Type*} [Group G] [Finite G]
    (hsmaller : ∀ (subgroup : Subgroup G) (_ : subgroup.Normal),
      Nat.card (G ⧸ subgroup) < Nat.card G → CentralTwoBInclusion.Property (G ⧸ subgroup))
    (hproper : ∀ subgroup : Subgroup G, subgroup ≠ ⊤ → CentralTwoBInclusion.Property subgroup)
    (hfailure : ¬ CentralTwoBInclusion.Property G)
    (overgroup : Subgroup G) [overgroup.Normal] [Group.IsSolvable overgroup]
    (hne : overgroup ≠ ⊥) :
    ∃ subgroup : Subgroup G, subgroup ≤ overgroup ∧ MinimalNormal.Property subgroup ∧
      Group.IsSolvable subgroup ∧ subgroup.Characteristic ∧
      ∀ other : Subgroup G, other.Normal → Group.IsSolvable other → other ≠ ⊥ → subgroup ≤ other := by
  obtain ⟨subgroup, hle, hminimal⟩ := MinimalNormal.exists_le overgroup hne
  let : Group.IsSolvable subgroup :=
    Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hle)
  refine ⟨subgroup, hle, hminimal, inferInstance, characteristic hsmaller hproper hfailure
    subgroup hminimal, ?_⟩
  intro other hnormal hsolvable hotherNe
  let : other.Normal := hnormal
  let : Group.IsSolvable other := hsolvable
  exact le_every_solvable_normal hsmaller hproper hfailure subgroup hminimal other hotherNe

end CFSG.ComponentClassification.MinimalBSolvable
