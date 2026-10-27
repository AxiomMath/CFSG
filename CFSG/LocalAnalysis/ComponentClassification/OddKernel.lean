module

public import Mathlib
public import Mathlib.GroupTheory.SpecificGroups.Cyclic
public import CFSG.Open.OrderForm
public import CFSG.LocalAnalysis.ComponentClassification.OddCore
public import CFSG.LocalAnalysis.ComponentClassification.Layer
public import CFSG.LocalAnalysis.ComponentClassification.TwoResidual

public section

open CFSG.Open

namespace CFSG.ComponentClassification.OddKernel

theorem core_map_le {G H : Type*} [Group G] [Finite G] [Group H] [Finite H]
    (quotient : G →* H) (hsurjective : Function.Surjective quotient) :
    (componentClassificationOddCore G).map quotient ≤ componentClassificationOddCore H := by
  apply OddCore.maximal
  · exact Subgroup.Normal.map inferInstance quotient hsurjective
  · exact (OddCore.odd_card G).of_dvd_nat ((componentClassificationOddCore G).card_map_dvd quotient)

theorem odd_card_preimage {G H : Type*} [Group G] [Finite G] [Group H]
    (quotient : G →* H) (hsurjective : Function.Surjective quotient)
    (hoddKernel : Odd (Nat.card quotient.ker)) (subgroup : Subgroup H)
    (hoddSubgroup : Odd (Nat.card subgroup)) : Odd (Nat.card (subgroup.comap quotient)) := by
  let preimage := subgroup.comap quotient
  let restriction : preimage →* subgroup :=
    (quotient.domRestrict preimage).codRestrict subgroup fun element => element.property
  have hrestriction : Function.Surjective restriction := by
    intro element
    obtain ⟨lift, hlift⟩ := hsurjective element.val
    have hmem : lift ∈ preimage := by
      change quotient lift ∈ subgroup
      rw [hlift]
      exact element.property
    exact ⟨⟨lift, hmem⟩, Subtype.ext hlift⟩
  have hkernel : restriction.ker = quotient.ker.subgroupOf preimage := by
    ext element
    change restriction element = 1 ↔ quotient element.val = 1
    exact ⟨fun hone => congrArg Subtype.val hone, fun hone => Subtype.ext hone⟩
  have hkernelCard : Nat.card restriction.ker = Nat.card quotient.ker := by
    rw [hkernel]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (Subgroup.ker_le_comap quotient subgroup)).toEquiv
  have hcard : Nat.card preimage = Nat.card subgroup * Nat.card quotient.ker := by
    have hcard := restriction.ker.card_eq_card_quotient_mul_card_subgroup
    rw [Nat.card_congr (QuotientGroup.liftEquiv restriction.ker hrestriction rfl).toEquiv,
      hkernelCard] at hcard
    exact hcard
  rw [hcard]
  exact hoddSubgroup.mul hoddKernel

theorem core_preimage {G H : Type*} [Group G] [Finite G] [Group H] [Finite H]
    (quotient : G →* H) (hsurjective : Function.Surjective quotient)
    (hoddKernel : Odd (Nat.card quotient.ker)) :
    (componentClassificationOddCore H).comap quotient = componentClassificationOddCore G := by
  apply le_antisymm
  · exact OddCore.maximal G _ (Subgroup.Normal.comap inferInstance quotient)
      (odd_card_preimage quotient hsurjective hoddKernel _ (OddCore.odd_card H))
  · exact Subgroup.map_le_iff_le_comap.mp (core_map_le quotient hsurjective)

theorem core_image {G H : Type*} [Group G] [Finite G] [Group H] [Finite H]
    (quotient : G →* H) (hsurjective : Function.Surjective quotient)
    (hoddKernel : Odd (Nat.card quotient.ker)) :
    (componentClassificationOddCore G).map quotient = componentClassificationOddCore H := by
  rw [← core_preimage quotient hsurjective hoddKernel]
  exact Subgroup.map_comap_eq_self_of_surjective hsurjective _

noncomputable def coreQuotientEquiv {G H : Type*} [Group G] [Finite G] [Group H] [Finite H]
    (quotient : G →* H) (hsurjective : Function.Surjective quotient)
    (hoddKernel : Odd (Nat.card quotient.ker)) :
    (G ⧸ componentClassificationOddCore G) ≃* (H ⧸ componentClassificationOddCore H) := by
  let composite := (QuotientGroup.mk' (componentClassificationOddCore H)).comp quotient
  have hsurjectiveComposite : Function.Surjective composite :=
    (QuotientGroup.mk'_surjective _).comp hsurjective
  have hkernel : composite.ker = componentClassificationOddCore G := by
    have hcomap : composite.ker = (componentClassificationOddCore H).comap quotient := by
      ext element
      exact QuotientGroup.eq_one_iff (quotient element)
    rw [hcomap]
    exact core_preimage quotient hsurjective hoddKernel
  exact QuotientGroup.liftEquiv _ hsurjectiveComposite hkernel.symm

theorem coreQuotientEquiv_mk {G H : Type*} [Group G] [Finite G] [Group H] [Finite H]
    (quotient : G →* H) (hsurjective : Function.Surjective quotient)
    (hoddKernel : Odd (Nat.card quotient.ker)) (g : G) :
    coreQuotientEquiv quotient hsurjective hoddKernel
      (QuotientGroup.mk' (componentClassificationOddCore G) g) =
      QuotientGroup.mk' (componentClassificationOddCore H) (quotient g) := by
  unfold coreQuotientEquiv
  rfl

theorem odd_card_restriction_kernel {G H : Type*} [Group G] [Group H]
    (quotient : G →* H) (hoddKernel : Odd (Nat.card quotient.ker))
    (subgroup : Subgroup G) : Odd (Nat.card (quotient.domRestrict subgroup).ker) := by
  let inclusion : (quotient.domRestrict subgroup).ker →* quotient.ker :=
    { toFun := fun element => ⟨element.val.val, element.property⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hinjective : Function.Injective inclusion := by
    intro left right heq
    have hvalue : left.val.val = right.val.val := congrArg (fun element : quotient.ker => element.val) heq
    apply Subtype.ext
    exact Subtype.ext hvalue
  exact hoddKernel.of_dvd_nat (Subgroup.card_dvd_of_injective inclusion hinjective)

theorem image_injective_on_two {G H : Type*} [Group G] [Finite G] [Group H]
    (quotient : G →* H) (hoddKernel : Odd (Nat.card quotient.ker))
    (twoSubgroup : Subgroup G) (htwo : IsPGroup 2 twoSubgroup) :
    Function.Injective (quotient.domRestrict twoSubgroup) := by
  have hkernelTwo : IsPGroup 2 (quotient.domRestrict twoSubgroup).ker :=
    htwo.to_subgroup _
  have hkernelOdd : Odd (Nat.card (quotient.domRestrict twoSubgroup).ker) :=
    odd_card_restriction_kernel quotient hoddKernel twoSubgroup
  obtain ⟨exponent, hcard⟩ := hkernelTwo.exists_card_eq
  have hcardOne : Nat.card (quotient.domRestrict twoSubgroup).ker = 1 := by
    apply Nat.eq_one_of_dvd_coprimes (hkernelOdd.coprime_two_left.pow_left exponent)
    · rw [hcard]
    · exact dvd_refl _
  exact (MonoidHom.ker_eq_bot_iff _).mp (Subgroup.card_eq_one.mp hcardOne)

end CFSG.ComponentClassification.OddKernel
