module

public import CFSG.LocalAnalysis.ComponentClassification.FixedCentralPreimage

public section

open CFSG.Open

namespace CFSG.ComponentClassification.InvolutionFixedPoints

theorem exists_nontrivial_fixed {G : Type*} [Group G] [Finite G]
    (hnoncommutative : ¬ IsMulCommutative G) (automorphism : MulAut G)
    (hinvolutive : Function.Involutive automorphism) :
    ∃ element : G, element ≠ 1 ∧ automorphism element = element := by
  classical
  by_contra hnone
  have hfixedPointFree : MonoidHom.FixedPointFree automorphism := by
    intro element hfixed
    by_contra hne
    exact hnone ⟨element, hne, hfixed⟩
  apply hnoncommutative
  exact isMulCommutative_iff.mpr fun left right =>
    (hfixedPointFree.commute_all_of_involutive hinvolutive left right).eq

theorem exists_noncentral_lifted_fixed {G : Type*} [Group G] [Finite G]
    (hquasisimple : IsQuasisimple G) (automorphism : MulAut G)
    (hinvolutive : Function.Involutive automorphism) :
    ∃ element : G, element ∉ Subgroup.center G ∧
      element ∈ FixedCentralPreimage.subgroup automorphism := by
  let projection := QuotientGroup.mk' (Subgroup.center G)
  let : IsSimpleGroup (G ⧸ Subgroup.center G) := hquasisimple.2
  let : Group.IsPerfect G := ⟨hquasisimple.1⟩
  let : Group.IsPerfect (G ⧸ Subgroup.center G) := inferInstance
  have hnoncommutative : ¬ IsMulCommutative (G ⧸ Subgroup.center G) :=
    Group.IsPerfect.not_isMulCommutative _
  have hquotientInvolutive : Function.Involutive
      (PerfectAutomorphisms.onCenterQuotient automorphism) := by
    intro element
    obtain ⟨lift, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center G) element
    rw [PerfectAutomorphisms.onCenterQuotient_apply_mk,
      PerfectAutomorphisms.onCenterQuotient_apply_mk, hinvolutive]
  obtain ⟨element, hne, hfixed⟩ := exists_nontrivial_fixed hnoncommutative
    (PerfectAutomorphisms.onCenterQuotient automorphism) hquotientInvolutive
  obtain ⟨lift, hlift⟩ := QuotientGroup.mk'_surjective (Subgroup.center G) element
  refine ⟨lift, ?_, ?_⟩
  · intro hcentral
    have hone : projection lift = 1 := (QuotientGroup.eq_one_iff lift).mpr hcentral
    exact hne (hlift.symm.trans hone)
  · change PerfectAutomorphisms.onCenterQuotient automorphism (projection lift) = projection lift
    rwa [hlift]

theorem fixed_card_mod_two {I : Type*} [Finite I] (permutation : Equiv.Perm I)
    (hinvolutive : Function.Involutive permutation) :
    Nat.card {member : I // permutation member = member} % 2 = Nat.card I % 2 := by
  classical
  let : Fintype I := Fintype.ofFinite I
  have hcongruence := Equiv.Perm.card_fixedPoints_modEq
    (f := (fun member : I => permutation member)) (p := 2) (n := 1) (by
      funext member
      exact hinvolutive member)
  have heq : Fintype.card I % 2 = Fintype.card {member : I // permutation member = member} % 2 := by
    exact hcongruence
  simpa only [Nat.card_eq_fintype_card] using heq.symm

theorem exists_fixed_involution {G : Type*} [Group G] [Finite G]
    (heven : 2 ∣ Nat.card G) (automorphism : MulAut G)
    (hinvolutive : Function.Involutive automorphism) :
    ∃ element : G, orderOf element = 2 ∧ automorphism element = element := by
  let fixed := FixedCommutingProduct.fixedSubgroup automorphism
  have hcard : 2 ∣ Nat.card fixed := by
    apply Nat.dvd_of_mod_eq_zero
    have hparity := fixed_card_mod_two automorphism.toEquiv hinvolutive
    change Nat.card {member : G // automorphism member = member} % 2 = Nat.card G % 2 at hparity
    have heq : Nat.card fixed = Nat.card {member : G // automorphism member = member} := rfl
    rw [heq, hparity]
    exact Nat.mod_eq_zero_of_dvd heven
  obtain ⟨element, horder⟩ := exists_prime_orderOf_dvd_card' 2 hcard
  exact ⟨element.val, (orderOf_injective fixed.subtype fixed.subtype_injective element).trans horder,
    element.property⟩

end CFSG.ComponentClassification.InvolutionFixedPoints
