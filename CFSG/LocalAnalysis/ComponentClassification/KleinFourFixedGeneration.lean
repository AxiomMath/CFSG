module

public import CFSG.LocalAnalysis.ComponentClassification.CoprimeInvariantSylow
public import CFSG.LocalAnalysis.ComponentClassification.OddKernelFixedLifting
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.ComponentClassification.KleinFourFixedGeneration

theorem square_mem_implies_mem {G : Type*} [Group G] [Finite G]
    (hodd : Odd (Nat.card G)) (subgroup : Subgroup G) (member : G)
    (hsquare : member ^ 2 ∈ subgroup) : member ∈ subgroup := by
  let equivalence := powCoprime hodd.coprime_two_right
  have hrecover : equivalence.symm (member ^ 2) = member := by
    rw [← powCoprime_apply hodd.coprime_two_right member]
    exact equivalence.symm_apply_apply member
  rw [← hrecover, powCoprime_symm_apply]
  exact subgroup.zpow_mem hsquare _

theorem fixed_inverted_generation {G : Type*} [CommGroup G] [Finite G]
    (hodd : Odd (Nat.card G)) (automorphism : MulAut G)
    (hinvolutive : Function.Involutive automorphism) (subgroup : Subgroup G)
    (hfixed : ∀ member : G, automorphism member = member → member ∈ subgroup)
    (hinverted : ∀ member : G, automorphism member = member⁻¹ → member ∈ subgroup) :
    subgroup = ⊤ := by
  apply top_unique
  intro member _
  have hfixedMember : member * automorphism member ∈ subgroup := by
    apply hfixed
    rw [map_mul, hinvolutive, mul_comm]
  have hinvertedMember : member * (automorphism member)⁻¹ ∈ subgroup := by
    apply hinverted
    rw [map_mul, map_inv, hinvolutive, mul_inv_rev, inv_inv, mul_comm]
  apply square_mem_implies_mem hodd subgroup member
  have hproduct := subgroup.mul_mem hfixedMember hinvertedMember
  have heq : (member * automorphism member) * (member * (automorphism member)⁻¹) = member ^ 2 := by
    rw [mul_mul_mul_comm, mul_inv_cancel, mul_one, pow_two]
  rwa [heq] at hproduct

theorem abelian_generation {G : Type*} [CommGroup G] [Finite G]
    (hodd : Odd (Nat.card G)) (first second : MulAut G)
    (hfirst : Function.Involutive first) (hsecond : Function.Involutive second)
    (hcommutes : Commute first second) :
    FixedCommutingProduct.fixedSubgroup first ⊔ FixedCommutingProduct.fixedSubgroup second ⊔
      FixedCommutingProduct.fixedSubgroup (first * second) = ⊤ := by
  let generated := FixedCommutingProduct.fixedSubgroup first ⊔
    FixedCommutingProduct.fixedSubgroup second ⊔ FixedCommutingProduct.fixedSubgroup (first * second)
  apply fixed_inverted_generation hodd first hfirst generated
  · intro member hmember
    exact (show FixedCommutingProduct.fixedSubgroup first ≤ generated from
      le_sup_left.trans le_sup_left) hmember
  · intro member hmember
    have hfirstSecond : first (second member) = (second member)⁻¹ := by
      have heq := congrArg (fun automorphism : MulAut G => automorphism member) hcommutes.eq
      change first (second member) = second (first member) at heq
      rw [heq, hmember, map_inv]
    have hfixedSecond : member * second member ∈ generated := by
      apply (show FixedCommutingProduct.fixedSubgroup second ≤ generated from
        le_sup_right.trans le_sup_left)
      change second (member * second member) = member * second member
      rw [map_mul, hsecond, mul_comm]
    have hfixedProduct : member * (second member)⁻¹ ∈ generated := by
      apply (show FixedCommutingProduct.fixedSubgroup (first * second) ≤ generated from le_sup_right)
      change first (second (member * (second member)⁻¹)) = member * (second member)⁻¹
      rw [map_mul, map_inv, hsecond, map_mul, map_inv, hfirstSecond, hmember]
      simp only [inv_inv]
      exact mul_comm _ _
    apply square_mem_implies_mem hodd generated member
    have hproduct := generated.mul_mem hfixedSecond hfixedProduct
    have heq : (member * second member) * (member * (second member)⁻¹) = member ^ 2 := by
      rw [mul_mul_mul_comm, mul_inv_cancel, mul_one, pow_two]
    rwa [heq] at hproduct

theorem mul_involutive {G : Type*} [Group G] (first second : MulAut G)
    (hfirst : Function.Involutive first) (hsecond : Function.Involutive second)
    (hcommutes : Commute first second) : Function.Involutive (first * second) := by
  intro member
  have heq := congrArg (fun automorphism : MulAut G => automorphism (second member)) hcommutes.eq
  change first (second (second member)) = second (first (second member)) at heq
  change first (second (first (second member))) = member
  rw [← heq, hsecond, hfirst]

theorem action_involutive {A G : Type*} [Group A] [Group G]
    (homomorphism : A →* MulAut G) (actor : A) (hsquare : actor * actor = 1) :
    Function.Involutive (homomorphism actor) := by
  intro member
  have heq := congrArg homomorphism hsquare
  rw [homomorphism.map_mul, homomorphism.map_one] at heq
  exact congrArg (fun automorphism : MulAut G => automorphism member) heq

theorem nilpotent_generation {G : Type*} [Group G] [Finite G] [Group.IsNilpotent G]
    (hodd : Odd (Nat.card G)) (first second : MulAut G)
    (hfirst : Function.Involutive first) (hsecond : Function.Involutive second)
    (hcommutes : Commute first second) :
    FixedCommutingProduct.fixedSubgroup first ⊔ FixedCommutingProduct.fixedSubgroup second ⊔
      FixedCommutingProduct.fixedSubgroup (first * second) = ⊤ := by
  induction hclass : Group.nilpotencyClass G using Nat.strong_induction_on generalizing G with
  | h complexity hinduction =>
      by_cases hzero : Group.nilpotencyClass G = 0
      · let : Subsingleton G := Group.nilpotencyClass_zero_iff_subsingleton.mp hzero
        exact Subsingleton.elim _ _
      let generated := FixedCommutingProduct.fixedSubgroup first ⊔
        FixedCommutingProduct.fixedSubgroup second ⊔ FixedCommutingProduct.fixedSubgroup (first * second)
      let center := Subgroup.center G
      let projection := QuotientGroup.mk' center
      let quotientFirst := PerfectAutomorphisms.onCenterQuotient first
      let quotientSecond := PerfectAutomorphisms.onCenterQuotient second
      have hquotientFirst : Function.Involutive quotientFirst := by
        intro member
        obtain ⟨lift, rfl⟩ := QuotientGroup.mk'_surjective center member
        change PerfectAutomorphisms.onCenterQuotient first
          (PerfectAutomorphisms.onCenterQuotient first ((QuotientGroup.mk' center) lift)) = _
        rw [PerfectAutomorphisms.onCenterQuotient_apply_mk,
          PerfectAutomorphisms.onCenterQuotient_apply_mk, hfirst]
      have hquotientSecond : Function.Involutive quotientSecond := by
        intro member
        obtain ⟨lift, rfl⟩ := QuotientGroup.mk'_surjective center member
        change PerfectAutomorphisms.onCenterQuotient second
          (PerfectAutomorphisms.onCenterQuotient second ((QuotientGroup.mk' center) lift)) = _
        rw [PerfectAutomorphisms.onCenterQuotient_apply_mk,
          PerfectAutomorphisms.onCenterQuotient_apply_mk, hsecond]
      have hquotientCommutes : Commute quotientFirst quotientSecond := by
        change quotientFirst * quotientSecond = quotientSecond * quotientFirst
        ext member
        obtain ⟨lift, rfl⟩ := QuotientGroup.mk'_surjective center member
        change PerfectAutomorphisms.onCenterQuotient first
          (PerfectAutomorphisms.onCenterQuotient second (projection lift)) =
            PerfectAutomorphisms.onCenterQuotient second
              (PerfectAutomorphisms.onCenterQuotient first (projection lift))
        rw [PerfectAutomorphisms.onCenterQuotient_apply_mk,
          PerfectAutomorphisms.onCenterQuotient_apply_mk,
          PerfectAutomorphisms.onCenterQuotient_apply_mk,
          PerfectAutomorphisms.onCenterQuotient_apply_mk]
        exact congrArg projection (congrArg
          (fun automorphism : MulAut G => automorphism lift) hcommutes.eq)
      have hquotientOdd : Odd (Nat.card (G ⧸ center)) := hodd.of_dvd_nat center.index_dvd_card
      have hsmaller : Group.nilpotencyClass (G ⧸ center) < complexity := by
        rw [Group.nilpotencyClass_quotient_center, ← hclass]
        omega
      have hquotientGenerated := hinduction _ hsmaller hquotientOdd quotientFirst quotientSecond
        hquotientFirst hquotientSecond hquotientCommutes rfl
      have hkernelOdd : Odd (Nat.card projection.ker) := by
        rw [QuotientGroup.ker_mk']
        exact hodd.of_dvd_nat (Subgroup.card_subgroup_dvd_card center)
      have hfirstImage := OddKernelFixedLifting.fixed_image_eq projection (QuotientGroup.mk'_surjective _)
        hkernelOdd first quotientFirst hfirst
        (PerfectAutomorphisms.onCenterQuotient_apply_mk first)
      have hsecondImage := OddKernelFixedLifting.fixed_image_eq projection (QuotientGroup.mk'_surjective _)
        hkernelOdd second quotientSecond hsecond
        (PerfectAutomorphisms.onCenterQuotient_apply_mk second)
      have hproductImage := OddKernelFixedLifting.fixed_image_eq projection (QuotientGroup.mk'_surjective _)
        hkernelOdd (first * second) (quotientFirst * quotientSecond)
        (mul_involutive first second hfirst hsecond hcommutes) (by
          intro member
          change projection (first (second member)) = quotientFirst (quotientSecond (projection member))
          rw [PerfectAutomorphisms.onCenterQuotient_apply_mk,
            PerfectAutomorphisms.onCenterQuotient_apply_mk])
      have hmap : generated.map projection = ⊤ := by
        rw [Subgroup.map_sup, Subgroup.map_sup, hfirstImage, hsecondImage, hproductImage]
        exact hquotientGenerated
      have hcover : generated ⊔ center = ⊤ := by
        have hcomap := Subgroup.comap_map_eq projection generated
        rw [hmap, Subgroup.comap_top, QuotientGroup.ker_mk'] at hcomap
        exact hcomap.symm
      let centerFirst : MulAut center :=
        (first.subgroupMap center).trans (MulEquiv.subgroupCongr
          (Subgroup.characteristic_iff_map_eq.mp inferInstance first))
      let centerSecond : MulAut center :=
        (second.subgroupMap center).trans (MulEquiv.subgroupCongr
          (Subgroup.characteristic_iff_map_eq.mp inferInstance second))
      have hcenterFirst : Function.Involutive centerFirst :=
        fun member => Subtype.ext (hfirst member.val)
      have hcenterSecond : Function.Involutive centerSecond :=
        fun member => Subtype.ext (hsecond member.val)
      have hcenterCommutes : Commute centerFirst centerSecond := by
        change centerFirst * centerSecond = centerSecond * centerFirst
        ext member
        exact congrArg (fun automorphism : MulAut G => automorphism member.val) hcommutes.eq
      let : CommGroup center :=
        { (inferInstance : Group center) with
          mul_comm := fun left right => Subtype.ext
            (Subgroup.mem_center_iff.mp left.property right.val).symm }
      have hcenterGenerated := abelian_generation
        (hodd.of_dvd_nat (Subgroup.card_subgroup_dvd_card center)) centerFirst centerSecond
        hcenterFirst hcenterSecond hcenterCommutes
      have hcenterLe : center ≤ generated := by
        intro member hmember
        let centerMember : center := ⟨member, hmember⟩
        have hlocalLe : FixedCommutingProduct.fixedSubgroup centerFirst ⊔
            FixedCommutingProduct.fixedSubgroup centerSecond ⊔
              FixedCommutingProduct.fixedSubgroup (centerFirst * centerSecond) ≤
                generated.comap center.subtype := by
          apply sup_le
          · apply sup_le
            · intro fixed hfixed
              exact (show FixedCommutingProduct.fixedSubgroup first ≤ generated from
                le_sup_left.trans le_sup_left) (congrArg Subtype.val hfixed)
            · intro fixed hfixed
              exact (show FixedCommutingProduct.fixedSubgroup second ≤ generated from
                le_sup_right.trans le_sup_left) (congrArg Subtype.val hfixed)
          · intro fixed hfixed
            exact (show FixedCommutingProduct.fixedSubgroup (first * second) ≤ generated from
              le_sup_right) (congrArg Subtype.val hfixed)
        rw [hcenterGenerated] at hlocalLe
        exact hlocalLe (Subgroup.mem_top centerMember)
      have hsup : generated ⊔ center = generated := sup_eq_left.mpr hcenterLe
      exact hsup.symm.trans hcover

theorem odd_group_generation {A G : Type*} [Group A] [Group G] [Finite G]
    (htwo : IsPGroup 2 A) (hodd : Odd (Nat.card G)) (homomorphism : A →* MulAut G)
    (firstActor secondActor : A) (hfirst : firstActor * firstActor = 1)
    (hsecond : secondActor * secondActor = 1) (hcommutes : Commute firstActor secondActor) :
    FixedCommutingProduct.fixedSubgroup (homomorphism firstActor) ⊔
      FixedCommutingProduct.fixedSubgroup (homomorphism secondActor) ⊔
        FixedCommutingProduct.fixedSubgroup (homomorphism (firstActor * secondActor)) = ⊤ := by
  let generated := FixedCommutingProduct.fixedSubgroup (homomorphism firstActor) ⊔
    FixedCommutingProduct.fixedSubgroup (homomorphism secondActor) ⊔
      FixedCommutingProduct.fixedSubgroup (homomorphism (firstActor * secondActor))
  have hsylow : ∀ prime : ℕ, prime.Prime → ∃ sylow : Sylow prime G, (sylow : Subgroup G) ≤ generated := by
    intro prime hprime
    let : Fact prime.Prime := ⟨hprime⟩
    obtain ⟨sylow, hinvariant⟩ := CoprimeInvariantSylow.exists_invariant 2 prime htwo
      (by simpa only [Nat.even_iff, Nat.dvd_iff_mod_eq_zero, Nat.odd_iff] using
        (Nat.not_even_iff_odd.mpr hodd)) homomorphism
    let subgroup := (sylow : Subgroup G)
    let restriction := CoprimeInvariantSylow.restriction homomorphism subgroup hinvariant
    let : Group.IsNilpotent subgroup := sylow.isPGroup'.isNilpotent
    have hsubgroupOdd : Odd (Nat.card subgroup) :=
      hodd.of_dvd_nat (Subgroup.card_subgroup_dvd_card subgroup)
    have hrestrictedCommutes : Commute (restriction firstActor) (restriction secondActor) := by
      change restriction firstActor * restriction secondActor = restriction secondActor * restriction firstActor
      have heq := congrArg restriction hcommutes.eq
      simpa only [map_mul] using heq
    have hgenerated := nilpotent_generation hsubgroupOdd (restriction firstActor) (restriction secondActor)
      (action_involutive restriction firstActor hfirst) (action_involutive restriction secondActor hsecond)
      hrestrictedCommutes
    have hlocalLe : FixedCommutingProduct.fixedSubgroup (restriction firstActor) ⊔
        FixedCommutingProduct.fixedSubgroup (restriction secondActor) ⊔
          FixedCommutingProduct.fixedSubgroup (restriction firstActor * restriction secondActor) ≤
            generated.comap subgroup.subtype := by
      apply sup_le
      · apply sup_le
        · intro member hmember
          exact (show FixedCommutingProduct.fixedSubgroup (homomorphism firstActor) ≤ generated from
            le_sup_left.trans le_sup_left) (congrArg Subtype.val hmember)
        · intro member hmember
          exact (show FixedCommutingProduct.fixedSubgroup (homomorphism secondActor) ≤ generated from
            le_sup_right.trans le_sup_left) (congrArg Subtype.val hmember)
      · intro member hmember
        apply (show FixedCommutingProduct.fixedSubgroup (homomorphism (firstActor * secondActor)) ≤ generated from
          le_sup_right)
        change (homomorphism (firstActor * secondActor)) member.val = member.val
        rw [homomorphism.map_mul]
        exact congrArg Subtype.val hmember
    rw [hgenerated] at hlocalLe
    refine ⟨sylow, fun member hmember => ?_⟩
    exact hlocalLe (Subgroup.mem_top (⟨member, hmember⟩ : subgroup))
  have hindex : generated.index = 1 := by
    by_contra hne
    obtain ⟨prime, hprime, hdivides⟩ := Nat.exists_prime_and_dvd hne
    let : Fact prime.Prime := ⟨hprime⟩
    obtain ⟨sylow, hle⟩ := hsylow prime hprime
    exact sylow.not_dvd_index (hdivides.trans (Subgroup.index_dvd_of_le hle))
  exact Subgroup.index_eq_one.mp hindex

end CFSG.ComponentClassification.KleinFourFixedGeneration
