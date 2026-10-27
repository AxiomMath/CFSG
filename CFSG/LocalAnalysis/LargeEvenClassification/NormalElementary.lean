module

import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.Open.LocalVocabulary

public section

open CFSG.Open

namespace CFSG.LargeEvenClassification.Helpers

universe groupUniverse targetUniverse

theorem subgroup_normal_of_central {Ambient : Type groupUniverse} [Group Ambient]
    (Central : Subgroup Ambient) (hle : Central ≤ Subgroup.center Ambient) : Central.Normal := by
  constructor
  intro element helement conjugator
  rw [Subgroup.mem_center_iff.mp (hle helement) conjugator, mul_assoc, mul_inv_cancel, mul_one]
  exact helement

theorem pGroup_normal_center_nontrivial {Ambient : Type groupUniverse} [Group Ambient]
    [Finite Ambient] {prime : ℕ} (hprime : prime.Prime) (hpgroup : IsPGroup prime Ambient)
    (Normal : Subgroup Ambient) [Normal.Normal] (hnontrivial : Normal ≠ ⊥) :
    Normal ⊓ Subgroup.center Ambient ≠ ⊥ := by
  let : Fact prime.Prime := ⟨hprime⟩
  let : MulAction Ambient Normal := MulAction.compHom Normal (MulAut.conjNormal (H := Normal))
  have hdivides : prime ∣ Nat.card Normal := by
    rcases (hpgroup.to_subgroup Normal).card_eq_or_dvd with htrivial | hdivides
    · exact False.elim (hnontrivial (Subgroup.card_eq_one.mp htrivial))
    · exact hdivides
  have hidentity : (1 : Normal) ∈ MulAction.fixedPoints Ambient Normal := by
    intro element
    change (MulAut.conjNormal element) 1 = 1
    exact map_one _
  obtain ⟨element, hfixed, hne⟩ :=
    hpgroup.exists_fixed_point_of_prime_dvd_card_of_fixed_point Normal hdivides hidentity
  have hcentral : (element : Ambient) ∈ Subgroup.center Ambient := by
    apply Subgroup.mem_center_iff.mpr
    intro conjugator
    have hconjugate := congrArg Subtype.val (hfixed conjugator)
    change conjugator * (element : Ambient) * conjugator⁻¹ = element at hconjugate
    exact mul_inv_eq_iff_eq_mul.mp hconjugate
  apply Subgroup.ne_bot_iff_exists_ne_one.mpr
  refine ⟨⟨element, element.property, hcentral⟩, ?_⟩
  intro heq
  apply hne
  apply Subtype.ext
  exact (congrArg Subtype.val heq).symm

theorem pGroup_normal_center_prime {Ambient : Type groupUniverse} [Group Ambient] [Finite Ambient]
    {prime : ℕ} (hprime : prime.Prime) (hpgroup : IsPGroup prime Ambient)
    (Normal : Subgroup Ambient) [Normal.Normal] (hnontrivial : Normal ≠ ⊥) :
    ∃ Central : Subgroup Ambient,
      Central.Normal ∧ Central ≤ Normal ∧ Central ≤ Subgroup.center Ambient ∧
        Nat.card Central = prime := by
  let : Fact prime.Prime := ⟨hprime⟩
  have hintersection : Normal ⊓ Subgroup.center Ambient ≠ ⊥ :=
    pGroup_normal_center_nontrivial hprime hpgroup Normal hnontrivial
  have hdivides : prime ∣ Nat.card ↥(Normal ⊓ Subgroup.center Ambient) := by
    rcases (hpgroup.to_subgroup (Normal ⊓ Subgroup.center Ambient)).card_eq_or_dvd with
      htrivial | hdivides
    · exact False.elim (hintersection (Subgroup.card_eq_one.mp htrivial))
    · exact hdivides
  obtain ⟨element, horder⟩ := exists_prime_orderOf_dvd_card' prime hdivides
  let Central := (Subgroup.zpowers element).map (Normal ⊓ Subgroup.center Ambient).subtype
  have hle : Central ≤ Normal ⊓ Subgroup.center Ambient := Subgroup.map_subtype_le _
  refine ⟨Central, subgroup_normal_of_central Central (hle.trans inf_le_right),
    hle.trans inf_le_left, hle.trans inf_le_right, ?_⟩
  rw [Subgroup.card_map_of_injective Subtype.val_injective, Nat.card_zpowers, horder]

theorem card_comap_of_surjective {Source : Type groupUniverse} [Group Source]
    {Target : Type targetUniverse} [Group Target] (quotient : Source →* Target)
    (hsurjective : Function.Surjective quotient) (Image : Subgroup Target) :
    Nat.card (Image.comap quotient) = Nat.card Image * Nat.card quotient.ker := by
  let restriction := quotient.subgroupComap Image
  have hrestriction : Function.Surjective restriction :=
    quotient.subgroupComap_surjective Image hsurjective
  have hkernel : restriction.ker = quotient.ker.subgroupOf (Image.comap quotient) := by
    ext element
    change restriction element = 1 ↔ quotient element = 1
    exact Subtype.ext_iff
  have hkerLe : quotient.ker ≤ Image.comap quotient := by
    intro element helement
    change quotient element ∈ Image
    rw [MonoidHom.mem_ker.mp helement]
    exact Image.one_mem
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup restriction.ker,
    Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective restriction hrestriction).toEquiv,
    hkernel, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hkerLe).toEquiv]

theorem pGroup_normal_subgroup_order (rank : ℕ) {Ambient : Type groupUniverse} [Group Ambient]
    [Finite Ambient] {prime : ℕ} (hprime : prime.Prime) (hpgroup : IsPGroup prime Ambient)
    (Normal : Subgroup Ambient) [Normal.Normal] (hcard : prime ^ rank ≤ Nat.card Normal) :
    ∃ Smaller : Subgroup Ambient,
      Smaller.Normal ∧ Smaller ≤ Normal ∧ Nat.card Smaller = prime ^ rank := by
  induction rank generalizing Ambient with
  | zero =>
    exact ⟨⊥, inferInstance, bot_le, by simp⟩
  | succ rank induction =>
    have hnontrivial : Normal ≠ ⊥ := by
      intro htrivial
      rw [htrivial, Subgroup.card_bot] at hcard
      exact (not_le_of_gt (Nat.one_lt_pow (by omega) hprime.one_lt)) hcard
    obtain ⟨Central, hcentralNormal, hcentralLe, _, hcentralCard⟩ :=
      pGroup_normal_center_prime hprime hpgroup Normal hnontrivial
    let : Central.Normal := hcentralNormal
    let quotient := QuotientGroup.mk' Central
    let image := Normal.map quotient
    let : image.Normal := Subgroup.Normal.map inferInstance quotient
      (QuotientGroup.mk'_surjective Central)
    have hpreimage : image.comap quotient = Normal := by
      apply Subgroup.comap_map_eq_self
      rw [QuotientGroup.ker_mk']
      exact hcentralLe
    have hcardProduct : Nat.card Normal = Nat.card image * prime := by
      rw [← hpreimage, card_comap_of_surjective quotient (QuotientGroup.mk'_surjective Central),
        QuotientGroup.ker_mk', hcentralCard]
    have himageCard : prime ^ rank ≤ Nat.card image := by
      rw [Nat.pow_succ, hcardProduct] at hcard
      exact Nat.le_of_mul_le_mul_right hcard hprime.pos
    obtain ⟨Smaller, hsmallerNormal, hsmallerLe, hsmallerCard⟩ :=
      induction (hpgroup.to_quotient Central) image himageCard
    let : Smaller.Normal := hsmallerNormal
    refine ⟨Smaller.comap quotient, inferInstance, ?_, ?_⟩
    · rw [← hpreimage]
      exact Subgroup.comap_mono hsmallerLe
    · rw [card_comap_of_surjective quotient (QuotientGroup.mk'_surjective Central),
        hsmallerCard, QuotientGroup.ker_mk', hcentralCard, Nat.pow_succ]

theorem elementary_subgroup_of_le {Ambient : Type groupUniverse} [Group Ambient] {prime : ℕ}
    (Elementary Smaller : Subgroup Ambient) (helementary : IsElemAbelian prime Elementary)
    (hle : Smaller ≤ Elementary) : IsElemAbelian prime Smaller :=
  CFSG.Open.IsElemAbelian.mono helementary hle

theorem normal_elementary_subgroup_order (rank : ℕ) {Ambient : Type groupUniverse} [Group Ambient]
    [Finite Ambient] {prime : ℕ} (hprime : prime.Prime) (hpgroup : IsPGroup prime Ambient)
    (Elementary : Subgroup Ambient) [Elementary.Normal]
    (helementary : IsElemAbelian prime Elementary) (hcard : prime ^ rank ≤ Nat.card Elementary) :
    ∃ Smaller : Subgroup Ambient,
      Smaller.Normal ∧ Smaller ≤ Elementary ∧ IsElemAbelian prime Smaller ∧
        Nat.card Smaller = prime ^ rank := by
  obtain ⟨Smaller, hnormal, hle, hcard⟩ :=
    pGroup_normal_subgroup_order rank hprime hpgroup Elementary hcard
  exact ⟨Smaller, hnormal, hle, elementary_subgroup_of_le Elementary Smaller helementary hle, hcard⟩

end CFSG.LargeEvenClassification.Helpers
