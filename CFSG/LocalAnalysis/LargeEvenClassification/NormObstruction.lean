module

public import CFSG.LocalAnalysis.LargeEvenClassification.MaximalAbelian
public import CFSG.LocalAnalysis.LargeEvenClassification.AbelianNormalRank

public section

open CFSG.Open

namespace CFSG.LargeEvenClassification.Helpers

universe groupUniverse

theorem commuting_involutions_product {Ambient : Type groupUniverse} [Group Ambient]
    {first second : Ambient} (hfirst : first ^ 2 = 1) (hsecond : second ^ 2 = 1)
    (hcommute : Commute first second) : (first * second) ^ 2 = 1 := by
  rw [hcommute.mul_pow, hfirst, hsecond, mul_one]

@[expose] def normalSquareOneSubgroup {Ambient : Type groupUniverse} [Group Ambient]
    (Normal : Subgroup Ambient)
    (hcommute : ∀ first ∈ Normal, ∀ second ∈ Normal,
      first ^ 2 = 1 → second ^ 2 = 1 → Commute first second) : Subgroup Ambient where
  carrier := {element | element ∈ Normal ∧ element ^ 2 = 1}
  one_mem' := ⟨Normal.one_mem, by simp⟩
  mul_mem' := by
    intro first second hfirst hsecond
    exact ⟨Normal.mul_mem hfirst.1 hsecond.1,
      commuting_involutions_product hfirst.2 hsecond.2
        (hcommute first hfirst.1 second hsecond.1 hfirst.2 hsecond.2)⟩
  inv_mem' := by
    intro element helement
    exact ⟨Normal.inv_mem helement.1, by rw [inv_pow, helement.2, inv_one]⟩

theorem normalSquareOneSubgroup_normal {Ambient : Type groupUniverse} [Group Ambient]
    (Normal : Subgroup Ambient) [Normal.Normal]
    (hcommute : ∀ first ∈ Normal, ∀ second ∈ Normal,
      first ^ 2 = 1 → second ^ 2 = 1 → Commute first second) :
    (normalSquareOneSubgroup Normal hcommute).Normal := by
  constructor
  intro element helement conjugator
  refine ⟨Subgroup.Normal.conj_mem inferInstance element helement.1 conjugator, ?_⟩
  have hpow := congrArg (MulAut.conj conjugator) helement.2
  rw [map_pow, map_one] at hpow
  exact hpow

theorem normalSquareOneSubgroup_elementary {Ambient : Type groupUniverse} [Group Ambient]
    (Normal : Subgroup Ambient)
    (hcommute : ∀ first ∈ Normal, ∀ second ∈ Normal,
      first ^ 2 = 1 → second ^ 2 = 1 → Commute first second) :
    IsElemAbelian 2 (normalSquareOneSubgroup Normal hcommute) := by
  constructor
  · apply isMulCommutative_iff.mpr
    intro first second
    apply Subtype.ext
    exact (hcommute first first.property.1 second second.property.1
      first.property.2 second.property.2).eq
  · intro element helement
    exact helement.2

theorem normal_four_involution_extension_eight {Ambient : Type groupUniverse} [Group Ambient]
    [Finite Ambient] (Normal Elementary : Subgroup Ambient) [Normal.Normal]
    (helementary : IsElemAbelian 2 Elementary) (hcard : Nat.card Elementary = 4)
    (hle : Elementary ≤ Normal) (involution : Ambient) (hinvolution : involution ∈ Normal)
    (hsquare : involution ^ 2 = 1) (houtside : involution ∉ Elementary)
    (hcentral : ∀ element ∈ Elementary, Commute involution element)
    (hshape : ∀ element ∈ Normal, element ^ 2 = 1 ↔
      element ∈ Elementary ∨ ∃ entry ∈ Elementary, element = involution * entry) :
    ∃ Eight : Subgroup Ambient, Eight.Normal ∧ IsElemAbelian 2 Eight ∧ Nat.card Eight = 8 := by
  have helementaryComm : ∀ first ∈ Elementary, ∀ second ∈ Elementary, Commute first second := by
    intro first hfirst second hsecond
    exact congrArg (fun entry : Elementary => (entry : Ambient))
      (@mul_comm' Elementary _ helementary.1 ⟨first, hfirst⟩ ⟨second, hsecond⟩)
  have hcommute : ∀ first ∈ Normal, ∀ second ∈ Normal,
      first ^ 2 = 1 → second ^ 2 = 1 → Commute first second := by
    intro first hfirst second hsecond hsquareFirst hsquareSecond
    rcases (hshape first hfirst).mp hsquareFirst with hfirstElementary | ⟨firstEntry, hfirstEntry, rfl⟩
    · rcases (hshape second hsecond).mp hsquareSecond with
        hsecondElementary | ⟨secondEntry, hsecondEntry, rfl⟩
      · exact helementaryComm first hfirstElementary second hsecondElementary
      · exact (hcentral first hfirstElementary).symm.mul_right
          (helementaryComm first hfirstElementary secondEntry hsecondEntry)
    · rcases (hshape second hsecond).mp hsquareSecond with
        hsecondElementary | ⟨secondEntry, hsecondEntry, rfl⟩
      · exact (hcentral second hsecondElementary).mul_left
          (helementaryComm firstEntry hfirstEntry second hsecondElementary)
      · exact ((Commute.refl involution).mul_right (hcentral secondEntry hsecondEntry)).mul_left
          ((hcentral firstEntry hfirstEntry).symm.mul_right
            (helementaryComm firstEntry hfirstEntry secondEntry hsecondEntry))
  let Eight := normalSquareOneSubgroup Normal hcommute
  let inclusion : Elementary × Bool → Eight := fun pair =>
    if pair.2 then
      ⟨involution * pair.1, Normal.mul_mem hinvolution (hle pair.1.property),
        commuting_involutions_product hsquare (helementary.2 pair.1 pair.1.property)
          (hcentral pair.1 pair.1.property)⟩
    else ⟨pair.1, hle pair.1.property, helementary.2 pair.1 pair.1.property⟩
  have hinjective : Function.Injective inclusion := by
    rintro ⟨first, firstFlag⟩ ⟨second, secondFlag⟩ heq
    have helements := congrArg (fun element : Eight => (element : Ambient)) heq
    cases firstFlag <;> cases secondFlag
    · have heqEntries : first = second := Subtype.ext helements
      exact congrArg (fun entry => (entry, false)) heqEntries
    · have hprod : (first : Ambient) = involution * second := helements
      have heqInv : involution = (first : Ambient) * (second : Ambient)⁻¹ := by
        rw [hprod]
        group
      exact False.elim (houtside (heqInv ▸ Elementary.mul_mem first.property
        (Elementary.inv_mem second.property)))
    · have hprod : involution * (first : Ambient) = second := helements
      have heqInv : involution = (second : Ambient) * (first : Ambient)⁻¹ := by
        rw [← hprod]
        group
      exact False.elim (houtside (heqInv ▸ Elementary.mul_mem second.property
        (Elementary.inv_mem first.property)))
    · have heqEntries : first = second := Subtype.ext (mul_left_cancel helements)
      exact congrArg (fun entry => (entry, true)) heqEntries
  have hsurjective : Function.Surjective inclusion := by
    intro element
    rcases (hshape element element.property.1).mp element.property.2 with
      helement | ⟨entry, hentry, heq⟩
    · exact ⟨(⟨element, helement⟩, false), Subtype.ext rfl⟩
    · exact ⟨(⟨entry, hentry⟩, true), Subtype.ext heq.symm⟩
  refine ⟨Eight, normalSquareOneSubgroup_normal Normal hcommute,
    normalSquareOneSubgroup_elementary Normal hcommute, ?_⟩
  rw [← Nat.card_congr (Equiv.ofBijective inclusion ⟨hinjective, hsurjective⟩), Nat.card_prod, hcard]
  norm_num

theorem zpowers_involution_cases {Ambient : Type groupUniverse} [Group Ambient]
    (involution : Ambient) (hsquare : involution ^ 2 = 1) {element : Ambient}
    (helement : element ∈ Subgroup.zpowers involution) : element = 1 ∨ element = involution := by
  obtain ⟨exponent, rfl⟩ := Subgroup.mem_zpowers_iff.mp helement
  rw [zpow_eq_zpow_emod' exponent hsquare]
  norm_num only [Nat.cast_ofNat]
  have hoptions : exponent % (2 : ℤ) = 0 ∨ exponent % (2 : ℤ) = 1 := by omega
  rcases hoptions with hzero | hone
  · rw [hzero, zpow_zero]
    exact Or.inl rfl
  · rw [hone, zpow_one]
    exact Or.inr rfl

set_option maxHeartbeats 600000 in
theorem central_action_involution_norm_obstruction {Ambient : Type groupUniverse} [Group Ambient]
    [Finite Ambient] (Normal : Subgroup Ambient) [Normal.Normal]
    (hcommutative : IsMulCommutative Normal)
    (hselfCentralizing : Subgroup.centralizer (Normal : Set Ambient) = Normal)
    (hnoEight : ∀ Eight : Subgroup Ambient, Eight.Normal → IsElemAbelian 2 Eight → Nat.card Eight ≠ 8)
    (automorphism : MulAut Normal) (hsquare : automorphism ^ 2 = 1) (hnontrivial : automorphism ≠ 1)
    (hcentral : ∀ element : Ambient, Commute automorphism (MulAut.conjNormal element))
    (hnormKernel : ∀ entry : Normal, automorphism entry * entry = 1 ↔ entry ^ 2 = 1)
    (hcard : Nat.card (normalElementarySquareKernel Normal hcommutative) = 4)
    (lift : Ambient) (hlift : MulAut.conjNormal lift = automorphism) :
    lift ^ 2 ∈ Normal ∧
      ∀ entry : Normal, lift ^ 2 ≠ (automorphism entry : Ambient) * entry := by
  let : CommGroup Normal := { (inferInstance : Group Normal) with
    mul_comm := @mul_comm' Normal _ hcommutative }
  let action : Ambient →* MulAut Normal := MulAut.conjNormal
  have hkernel : action.ker = Normal := (conjNormal_ker_eq_centralizer Normal).trans hselfCentralizing
  have hliftSquare : lift ^ 2 ∈ Normal := by
    rw [← hkernel]
    change action (lift ^ 2) = 1
    rw [map_pow, hlift, hsquare]
  refine ⟨hliftSquare, ?_⟩
  intro entry hadjustable
  let involution := (entry : Ambient)⁻¹ * lift
  have hentryConjugate : lift * (entry : Ambient)⁻¹ = (automorphism entry : Ambient)⁻¹ * lift := by
    have heq := MulAut.conjNormal_apply lift entry
    rw [hlift] at heq
    have hcommutation : lift * (entry : Ambient) = (automorphism entry : Ambient) * lift := by
      rw [heq]
      group
    calc
      lift * (entry : Ambient)⁻¹ = (automorphism entry : Ambient)⁻¹ *
          ((automorphism entry : Ambient) * lift) * (entry : Ambient)⁻¹ := by group
      _ = (automorphism entry : Ambient)⁻¹ * (lift * (entry : Ambient)) * (entry : Ambient)⁻¹ := by
        rw [hcommutation]
      _ = (automorphism entry : Ambient)⁻¹ * lift := by group
  have hinvolutionSquare : involution ^ 2 = 1 := by
    change ((entry : Ambient)⁻¹ * lift) ^ 2 = 1
    calc
      ((entry : Ambient)⁻¹ * lift) ^ 2 = (entry : Ambient)⁻¹ *
          (lift * (entry : Ambient)⁻¹) * lift := by simp only [pow_two, mul_assoc]
      _ = (entry : Ambient)⁻¹ * (automorphism entry : Ambient)⁻¹ * lift ^ 2 := by
        rw [hentryConjugate]
        simp only [pow_two, mul_assoc]
      _ = 1 := by rw [hadjustable]; group
  have hnormalAction : ∀ element : Normal, action element = 1 := by
    intro element
    have hmem : (element : Ambient) ∈ action.ker := hkernel.symm ▸ element.property
    exact hmem
  have hinvolutionAction : action involution = automorphism := by
    change action ((entry : Ambient)⁻¹ * lift) = automorphism
    rw [map_mul, map_inv, hnormalAction entry, inv_one, one_mul, hlift]
  let centralElement : action.range := ⟨automorphism, ⟨lift, hlift⟩⟩
  let Cyclic := Subgroup.zpowers centralElement
  have hcyclicCentral : Cyclic ≤ Subgroup.center action.range := by
    apply Subgroup.zpowers_le.mpr
    apply Subgroup.mem_center_iff.mpr
    intro element
    apply Subtype.ext
    change (element : MulAut Normal) * automorphism = automorphism * element
    obtain ⟨source, hsource⟩ := element.property
    rw [← hsource]
    exact (hcentral source).eq.symm
  let : Cyclic.Normal := subgroup_normal_of_central Cyclic hcyclicCentral
  let Extension := Cyclic.comap action.rangeRestrict
  let : Extension.Normal := inferInstance
  let Elementary := normalElementarySquareKernel Normal hcommutative
  have helementary := normalElementarySquareKernel_elementary Normal hcommutative
  have helementaryLe : Elementary ≤ Normal := Subgroup.map_subtype_le _
  have hnormalExtension : Normal ≤ Extension := by
    intro element helement
    have heq : action.rangeRestrict element = 1 := Subtype.ext (hnormalAction ⟨element, helement⟩)
    change action.rangeRestrict element ∈ Cyclic
    rw [heq]
    exact Cyclic.one_mem
  have hinvolutionExtension : involution ∈ Extension := by
    change action.rangeRestrict involution ∈ Cyclic
    have heq : action.rangeRestrict involution = centralElement := Subtype.ext hinvolutionAction
    rw [heq]
    exact Subgroup.mem_zpowers_iff.mpr ⟨1, by simp⟩
  have hinvolutionOutside : involution ∉ Elementary := by
    intro helement
    have heq : action involution = 1 := hnormalAction ⟨involution, helementaryLe helement⟩
    exact hnontrivial (hinvolutionAction.symm.trans heq)
  have helementaryMembership : ∀ element : Normal, (element : Ambient) ∈ Elementary ↔ element ^ 2 = 1 := by
    intro element
    change (element : Ambient) ∈
      (powMonoidHom 2 : Normal →* Normal).ker.map Normal.subtype ↔ element ^ 2 = 1
    constructor
    · intro hmem
      obtain ⟨other, hother, heq⟩ := Subgroup.mem_map.mp hmem
      have hsame : other = element := Subtype.ext heq
      change other ^ 2 = 1 at hother
      exact hsame ▸ hother
    · intro hpower
      exact Subgroup.mem_map.mpr ⟨element, hpower, rfl⟩
  have hcentralElementary : ∀ element ∈ Elementary, Commute involution element := by
    intro element helement
    let normalElement : Normal := ⟨element, helementaryLe helement⟩
    have hpower : normalElement ^ 2 = 1 := (helementaryMembership normalElement).mp helement
    have hnorm : automorphism normalElement * normalElement = 1 := (hnormKernel normalElement).mpr hpower
    have hfixed : automorphism normalElement = normalElement := by
      have hfirst := mul_eq_one_iff_eq_inv.mp hnorm
      have hsecond : normalElement⁻¹ = normalElement := by
        have heq : normalElement * normalElement = 1 := by simpa only [pow_two] using hpower
        exact (mul_eq_one_iff_eq_inv.mp heq).symm
      exact hfirst.trans hsecond
    have hconjugate := MulAut.conjNormal_apply involution normalElement
    rw [hinvolutionAction, hfixed] at hconjugate
    exact mul_inv_eq_iff_eq_mul.mp hconjugate.symm
  have hshape : ∀ element ∈ Extension, element ^ 2 = 1 ↔
      element ∈ Elementary ∨ ∃ entry ∈ Elementary, element = involution * entry := by
    intro element helement
    constructor
    · intro hpower
      have hcyclic : action.rangeRestrict element ∈ Cyclic := helement
      have hcentralSquare : centralElement ^ 2 = 1 := Subtype.ext hsquare
      rcases zpowers_involution_cases centralElement hcentralSquare hcyclic with htrivial | hnontrivial
      · have hnormal : element ∈ Normal := by
          rw [← hkernel]
          exact congrArg Subtype.val htrivial
        apply Or.inl
        apply (helementaryMembership ⟨element, hnormal⟩).mpr
        exact Subtype.ext hpower
      · have helementAction : action element = automorphism := congrArg Subtype.val hnontrivial
        have hnormal : involution⁻¹ * element ∈ Normal := by
          rw [← hkernel]
          change action (involution⁻¹ * element) = 1
          rw [map_mul, map_inv, hinvolutionAction, helementAction, inv_mul_cancel]
        let normalElement : Normal := ⟨involution⁻¹ * element, hnormal⟩
        have helementShape : element = involution * (normalElement : Ambient) := by
          dsimp only [normalElement]
          group
        have hinvolutionInverse : involution⁻¹ = involution := by
          exact (mul_eq_one_iff_eq_inv.mp (by simpa only [pow_two] using hinvolutionSquare)).symm
        have hconjugate := MulAut.conjNormal_apply involution normalElement
        rw [hinvolutionAction, hinvolutionInverse] at hconjugate
        have hnorm : automorphism normalElement * normalElement = 1 := by
          apply Subtype.ext
          change (automorphism normalElement : Ambient) * (normalElement : Ambient) = 1
          rw [hconjugate]
          calc
            involution * (normalElement : Ambient) * involution * (normalElement : Ambient) =
                (involution * (normalElement : Ambient)) ^ 2 := by simp only [pow_two, mul_assoc]
            _ = 1 := by rw [← helementShape]; exact hpower
        exact Or.inr ⟨normalElement, (helementaryMembership normalElement).mpr
          ((hnormKernel normalElement).mp hnorm), helementShape⟩
    · rintro (helement | ⟨normalElement, hnormalElement, rfl⟩)
      · exact helementary.2 element helement
      · exact commuting_involutions_product hinvolutionSquare
          (helementary.2 normalElement hnormalElement) (hcentralElementary normalElement hnormalElement)
  obtain ⟨Eight, hnormal, helementaryEight, hcardEight⟩ :=
    normal_four_involution_extension_eight Extension Elementary helementary hcard
      (helementaryLe.trans hnormalExtension) involution hinvolutionExtension hinvolutionSquare
      hinvolutionOutside hcentralElementary hshape
  exact hnoEight Eight hnormal helementaryEight hcardEight

end CFSG.LargeEvenClassification.Helpers
