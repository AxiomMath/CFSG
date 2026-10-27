module

public import CFSG.LocalAnalysis.RankThreeEvenClassification.ThetaPlaneQuotient
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

open CFSG.Open

namespace CFSG.RankThreeEvenClassification.Helpers

universe u v

theorem subgroupMap_kernel_eq {G : Type u} {H : Type v} [Group G] [Group H]
    (homomorphism : G →* H) (subgroup : Subgroup G) :
    (homomorphism.subgroupMap subgroup).ker = homomorphism.ker.subgroupOf subgroup := by
  ext element
  change (homomorphism.subgroupMap subgroup) element = 1 ↔ homomorphism (element : G) = 1
  exact Subtype.ext_iff

theorem card_map_mul_card_subgroupOf_kernel {G : Type u} {H : Type v} [Group G] [Group H]
    (homomorphism : G →* H) (subgroup : Subgroup G) :
    Nat.card (subgroup.map homomorphism) * Nat.card (homomorphism.ker.subgroupOf subgroup) =
      Nat.card subgroup := by
  let restriction := homomorphism.subgroupMap subgroup
  have hcard := restriction.ker.card_eq_card_quotient_mul_card_subgroup
  have hquotientCard := Nat.card_congr
    (QuotientGroup.quotientKerEquivOfSurjective restriction
      (homomorphism.subgroupMap_surjective subgroup)).toEquiv
  rw [hquotientCard] at hcard
  simpa only [restriction, subgroupMap_kernel_eq] using hcard.symm

theorem card_map_mul_card_kernel_of_kernel_le {G : Type u} {H : Type v} [Group G] [Group H]
    (homomorphism : G →* H) (subgroup : Subgroup G) (hkernelLe : homomorphism.ker ≤ subgroup) :
    Nat.card (subgroup.map homomorphism) * Nat.card homomorphism.ker = Nat.card subgroup := by
  have hcard := card_map_mul_card_subgroupOf_kernel homomorphism subgroup
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hkernelLe).toEquiv] at hcard
  exact hcard

theorem card_map_eq_of_injOn {G : Type u} {H : Type v} [Group G] [Group H]
    (homomorphism : G →* H) (subgroup : Subgroup G)
    (hinjective : Set.InjOn homomorphism (subgroup : Set G)) :
    Nat.card (subgroup.map homomorphism) = Nat.card subgroup := by
  have hrestrictionInjective : Function.Injective (homomorphism.subgroupMap subgroup) := by
    intro first second heq
    exact Subtype.ext (hinjective first.property second.property (congrArg Subtype.val heq))
  exact (Nat.card_congr (MulEquiv.ofBijective (homomorphism.subgroupMap subgroup)
    ⟨hrestrictionInjective, homomorphism.subgroupMap_surjective subgroup⟩).toEquiv).symm

theorem rank_three_actor_map_card {G : Type u} {H : Type v} [Group G] [Group H]
    (prime : ℕ) (hprime : prime.Prime) (homomorphism : G →* H) (actor : Subgroup G)
    (hkernelLe : homomorphism.ker ≤ actor) (hkernelCard : Nat.card homomorphism.ker = prime)
    (hactorCard : Nat.card actor = prime ^ 3) :
    Nat.card (actor.map homomorphism) = prime ^ 2 := by
  have hcard := card_map_mul_card_kernel_of_kernel_le homomorphism actor hkernelLe
  rw [hkernelCard, hactorCard, pow_succ] at hcard
  exact Nat.eq_of_mul_eq_mul_right hprime.pos hcard

theorem plane_map_eq_rank_three_actor_map_of_disjoint_kernel
    {G : Type u} {H : Type v} [Group G] [Group H] [Finite H]
    (prime : ℕ) (hprime : prime.Prime) (homomorphism : G →* H) (plane actor : Subgroup G)
    (hplaneLe : plane ≤ actor) (hkernelLe : homomorphism.ker ≤ actor)
    (hkernelCard : Nat.card homomorphism.ker = prime)
    (hplaneCard : Nat.card plane = prime ^ 2) (hactorCard : Nat.card actor = prime ^ 3)
    (hdisjoint : Disjoint plane homomorphism.ker) :
    plane.map homomorphism = actor.map homomorphism := by
  apply Subgroup.eq_of_le_of_card_ge (Subgroup.map_mono hplaneLe)
  rw [rank_three_actor_map_card prime hprime homomorphism actor hkernelLe hkernelCard hactorCard,
    card_map_eq_of_injOn homomorphism plane (injOn_of_disjoint_kernel homomorphism plane hdisjoint),
    hplaneCard]

theorem thetaPlaneAlpha_le_of_rank_three_quotient_actor
    {G : Type u} {H : Type v} [Group G] [Group H] [Finite G] [Finite H]
    (prime : ℕ) (hprime : prime.Prime) (homomorphism : G →* H)
    (hsurjective : Function.Surjective homomorphism)
    (hcentral : homomorphism.ker ≤ Subgroup.center G)
    (hkernelCard : Nat.card homomorphism.ker = prime) (plane actor : Subgroup G)
    (hplaneLe : plane ≤ actor) (hkernelLe : homomorphism.ker ≤ actor)
    (hcomm : IsMulCommutative plane) (hplaneCard : Nat.card plane = prime ^ 2)
    (hactorCard : Nat.card actor = prime ^ 3)
    (halpha : thetaPlaneAlpha prime (actor.map homomorphism) ≤ solvablePrimeComplementCore H prime) :
    thetaPlaneAlpha prime plane ≤ solvablePrimeComplementCore G prime := by
  rcases prime_order_subgroup_le_or_disjoint prime hprime plane homomorphism.ker hkernelCard
    with hkernelPlane | hdisjoint
  · have hkernelNe : homomorphism.ker ≠ ⊥ := by
      intro heq
      have hone := Subgroup.card_eq_one.mpr heq
      rw [hkernelCard] at hone
      exact hprime.ne_one hone
    obtain ⟨centralElement, hne⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hkernelNe
    exact thetaPlaneAlpha_le_of_central_line_generators prime hprime plane homomorphism.ker
      hcentral (fun element hmem houtside =>
        plane_generated_by_prime_line_and_element prime hprime plane homomorphism.ker
          hcomm hkernelPlane hplaneCard hkernelCard element hmem houtside)
      centralElement (hkernelPlane centralElement.property) centralElement.property
      (fun heq => hne (Subtype.ext heq))
  · apply thetaPlaneAlpha_le_of_quotient_alpha_le_central_prime_kernel prime hprime homomorphism
      hsurjective hcentral hkernelCard plane hcomm hplaneCard
    rw [plane_map_eq_rank_three_actor_map_of_disjoint_kernel prime hprime homomorphism
      plane actor hplaneLe hkernelLe hkernelCard hplaneCard hactorCard hdisjoint]
    exact halpha

theorem isElemAbelian_subgroupOf {G : Type u} [Group G] (prime : ℕ)
    (smaller larger : Subgroup G) (hab : IsElemAbelian prime smaller) :
    IsElemAbelian prime (smaller.subgroupOf larger) := CFSG.Open.IsElemAbelian.subgroupOf hab larger

theorem elementary_plane_commutative_of_le {G : Type u} [Group G] (prime : ℕ)
    (plane actor : Subgroup G) (hab : IsElemAbelian prime actor) (hle : plane ≤ actor) :
    IsMulCommutative plane := by
  refine ⟨⟨?_⟩⟩
  intro first second
  exact Subtype.ext (congrArg (fun value : actor => (value : G)) (isMulCommutative_iff.mp hab.1
    (⟨first, hle first.property⟩ : actor) (⟨second, hle second.property⟩ : actor)))

def elementInCentralizer {G : Type u} [Group G] (element : G) :
    Subgroup.centralizer ({element} : Set G) :=
  ⟨element, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩

theorem elementInCentralizer_central {G : Type u} [Group G] (element : G) :
    elementInCentralizer element ∈ Subgroup.center (Subgroup.centralizer ({element} : Set G)) := by
  apply Subgroup.mem_center_iff.mpr
  intro other
  exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp other.property)

theorem zpowers_elementInCentralizer_le_center {G : Type u} [Group G] (element : G) :
    Subgroup.zpowers (elementInCentralizer element) ≤
      Subgroup.center (Subgroup.centralizer ({element} : Set G)) := by
  exact Subgroup.zpowers_le.mpr (elementInCentralizer_central element)

theorem normal_of_le_center {G : Type u} [Group G] (subgroup : Subgroup G)
    (hle : subgroup ≤ Subgroup.center G) : subgroup.Normal := by
  apply Subgroup.normalizer_eq_top_iff.mp
  apply top_le_iff.mp
  apply Subgroup.le_normalizer_iff.mpr
  intro conjugator _ element helement
  rw [Subgroup.mem_center_iff.mp (hle helement) conjugator, mul_assoc, mul_inv_cancel, mul_one]
  exact helement

theorem rank_three_central_line_raw_plane_containment
    {G : Type u} [Group G] [Finite G] (prime : ℕ) (hprime : prime.Prime)
    (actor : Subgroup G) (hab : IsElemAbelian prime actor)
    (hactorCard : Nat.card actor = prime ^ 3) (element : G)
    (hmem : element ∈ actor) (hne : element ≠ 1) (plane : Subgroup G)
    (hplaneLe : plane ≤ actor) (hplaneCard : Nat.card plane = prime ^ 2)
    (halpha : ∀ (lineNormal : (Subgroup.zpowers (elementInCentralizer element)).Normal),
      let quotient := @QuotientGroup.mk' (Subgroup.centralizer ({element} : Set G))
        _ (Subgroup.zpowers (elementInCentralizer element)) lineNormal
      thetaPlaneAlpha prime ((actor.subgroupOf
        (Subgroup.centralizer ({element} : Set G))).map quotient) ≤
        solvablePrimeComplementCore
          ((Subgroup.centralizer ({element} : Set G)) ⧸
            Subgroup.zpowers (elementInCentralizer element)) prime) :
    thetaPlaneAlpha prime (plane.subgroupOf (Subgroup.centralizer ({element} : Set G))) ≤
      solvablePrimeComplementCore (Subgroup.centralizer ({element} : Set G)) prime := by
  have : Fact prime.Prime := ⟨hprime⟩
  let centralizer := Subgroup.centralizer ({element} : Set G)
  let line := Subgroup.zpowers (elementInCentralizer element)
  have hlineCentral : line ≤ Subgroup.center centralizer :=
    zpowers_elementInCentralizer_le_center element
  have hlineNormal : line.Normal := normal_of_le_center line hlineCentral
  have : line.Normal := hlineNormal
  let quotient := QuotientGroup.mk' line
  have hquotientKernel : quotient.ker = line := QuotientGroup.ker_mk' line
  have hkernelCentral : quotient.ker ≤ Subgroup.center centralizer := by
    simpa only [hquotientKernel] using hlineCentral
  have hlineCard : Nat.card line = prime := by
    rw [Nat.card_zpowers]
    apply orderOf_eq_prime
    · exact Subtype.ext (hab.2 element hmem)
    · exact fun heq => hne (congrArg Subtype.val heq)
  have hkernelCard : Nat.card quotient.ker = prime := by
    simpa only [hquotientKernel] using hlineCard
  have hactorLe := commutative_plane_le_element_centralizer actor hab.1 element hmem
  have hplaneCentralizer := hplaneLe.trans hactorLe
  have hrestrictedActorCard : Nat.card (actor.subgroupOf centralizer) = prime ^ 3 :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hactorLe).toEquiv).trans hactorCard
  have hrestrictedPlaneCard : Nat.card (plane.subgroupOf centralizer) = prime ^ 2 :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hplaneCentralizer).toEquiv).trans hplaneCard
  have hkernelLe : quotient.ker ≤ actor.subgroupOf centralizer := by
    rw [QuotientGroup.ker_mk']
    apply Subgroup.zpowers_le.mpr
    exact hmem
  apply thetaPlaneAlpha_le_of_rank_three_quotient_actor prime hprime quotient
    (QuotientGroup.mk'_surjective line) hkernelCentral hkernelCard
    (plane.subgroupOf centralizer) (actor.subgroupOf centralizer)
    (fun other hother => hplaneLe hother) hkernelLe
    (elementary_plane_commutative_of_le prime _ _
      (isElemAbelian_subgroupOf prime actor centralizer hab) (fun other hother => hplaneLe hother))
    hrestrictedPlaneCard hrestrictedActorCard
  exact halpha hlineNormal

end CFSG.RankThreeEvenClassification.Helpers
