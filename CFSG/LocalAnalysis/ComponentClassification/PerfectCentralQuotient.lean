module

public import Mathlib
public import Mathlib.GroupTheory.SpecificGroups.Cyclic
public import CFSG.LocalAnalysis.ComponentClassification.Quasisimple
public import CFSG.LocalAnalysis.ComponentClassification.PerfectAutomorphisms
public import CFSG.LocalAnalysis.ComponentClassification.InvolutionDiagonal

public section

namespace CFSG.ComponentClassification.PerfectCentralQuotient

@[expose] noncomputable def equivalence {G H : Type*} [Group G] [Group H] [Group.IsPerfect G]
    (homomorphism : G →* H) (hsurjective : Function.Surjective homomorphism)
    (hkernel : homomorphism.ker ≤ Subgroup.center G) :
    G ⧸ Subgroup.center G ≃* H ⧸ Subgroup.center H := by
  let quotient := (QuotientGroup.mk' (Subgroup.center H)).comp homomorphism
  have hquotient : Function.Surjective quotient :=
    (QuotientGroup.mk'_surjective _).comp hsurjective
  have hquotientKernel : quotient.ker = Subgroup.center G := by
    rw [← Quasisimple.center_comap_of_central_kernel homomorphism hsurjective hkernel]
    ext member
    change (QuotientGroup.mk' (Subgroup.center H)) (homomorphism member) = 1 ↔
      homomorphism member ∈ Subgroup.center H
    exact QuotientGroup.eq_one_iff _
  exact QuotientGroup.liftEquiv (Subgroup.center G) hquotient hquotientKernel.symm

theorem even_central_quotient {G : Type*} [Group G] [Finite G] [Group.IsPerfect G]
    (heven : Even (Nat.card G)) : Even (Nat.card (G ⧸ Subgroup.center G)) := by
  by_contra hnotEven
  have hnotTwo : ¬ 2 ∣ Nat.card (G ⧸ Subgroup.center G) :=
    fun hdivides => hnotEven (even_iff_two_dvd.mpr hdivides)
  let sylow : Sylow 2 G := Classical.choice inferInstance
  let quotient := QuotientGroup.mk' (Subgroup.center G)
  have himage := sylow.isPGroup'.map quotient
  have himageCard : Nat.card ↥((sylow : Subgroup G).map quotient) = 1 := by
    rcases himage.card_eq_or_dvd with hone | hdivides
    · exact hone
    · exact (hnotTwo (hdivides.trans (Subgroup.card_subgroup_dvd_card _))).elim
  have himageBot := ((sylow : Subgroup G).map quotient).eq_bot_iff_card.mpr himageCard
  have hsylowCentral : (sylow : Subgroup G) ≤ Subgroup.center G := by
    have hle := ((sylow : Subgroup G).map_eq_bot_iff.mp himageBot)
    rwa [QuotientGroup.ker_mk'] at hle
  let : IsMulCommutative (sylow : Subgroup G) := isMulCommutative_iff.mpr
    fun first second => Subtype.ext
      ((Subgroup.mem_center_iff.mp (hsylowCentral first.property)) second).symm
  have hnormalizer : Subgroup.normalizer (sylow : Set G) ≤
      Subgroup.centralizer (sylow : Set G) := by
    intro member _
    apply Subgroup.mem_centralizer_iff.mpr
    intro central hcentral
    exact ((Subgroup.mem_center_iff.mp (hsylowCentral hcentral)) member).symm
  let transfer := MonoidHom.transferSylow sylow hnormalizer
  have htransfer : transfer = 1 := PerfectAutomorphisms.hom_eq_one_of_commutative transfer
  have htransferKernel : transfer.ker = ⊤ := MonoidHom.ker_eq_top_iff.mpr htransfer
  have hnot := MonoidHom.not_dvd_card_ker_transferSylow sylow hnormalizer
  change ¬ 2 ∣ Nat.card transfer.ker at hnot
  rw [htransferKernel, Subgroup.card_top] at hnot
  exact hnot (even_iff_two_dvd.mp heven)

theorem even_image {G H : Type*} [Group G] [Group H] [Finite G] [Finite H]
    [Group.IsPerfect G] (homomorphism : G →* H)
    (hsurjective : Function.Surjective homomorphism)
    (hkernel : homomorphism.ker ≤ Subgroup.center G) (heven : Even (Nat.card G)) :
    Even (Nat.card H) := by
  have hquotient : Even (Nat.card (H ⧸ Subgroup.center H)) := by
    rw [← Nat.card_congr (equivalence homomorphism hsurjective hkernel).toEquiv]
    exact even_central_quotient heven
  exact even_iff_two_dvd.mpr ((even_iff_two_dvd.mp hquotient).trans
    (Subgroup.card_quotient_dvd_card _))

end CFSG.ComponentClassification.PerfectCentralQuotient
