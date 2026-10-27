module

public import CFSG.LocalAnalysis.RankThreeEvenClassification.ThetaPlane
public import CFSG.LocalAnalysis.RankThreeEvenClassification.CentralQuotient

public section

namespace CFSG.RankThreeEvenClassification.Helpers

universe u v

theorem prime_complement_le_normal_of_le_sup_pSubgroup
    {G : Type u} [Group G] [Finite G] (prime : ℕ) (hprime : prime.Prime)
    (subgroup normalSubgroup pSubgroup : Subgroup G) (hnormal : normalSubgroup.Normal)
    (hpgroup : IsPGroup prime pSubgroup) (hcomplement : ¬prime ∣ Nat.card subgroup)
    (hle : subgroup ≤ normalSubgroup ⊔ pSubgroup) : subgroup ≤ normalSubgroup := by
  have : normalSubgroup.Normal := hnormal
  have : Fact prime.Prime := ⟨hprime⟩
  let quotient := QuotientGroup.mk' normalSubgroup
  have hquotientKernel : quotient.ker = normalSubgroup := QuotientGroup.ker_mk' normalSubgroup
  have hquotientMap : normalSubgroup.map quotient = ⊥ := by
    exact (Subgroup.map_eq_bot_iff normalSubgroup).mpr hquotientKernel.ge
  have hmappedLe : subgroup.map quotient ≤ pSubgroup.map quotient := by
    have hmapped := Subgroup.map_mono (f := quotient) hle
    simpa only [Subgroup.map_sup, hquotientMap, bot_sup_eq] using hmapped
  have hmappedPGroup : IsPGroup prime (subgroup.map quotient) :=
    (hpgroup.map quotient).of_injective (Subgroup.inclusion hmappedLe)
      (Subgroup.inclusion_injective hmappedLe)
  have hcard : Nat.card (subgroup.map quotient) = 1 := by
    rcases hmappedPGroup.card_eq_or_dvd with hone | hdiv
    · exact hone
    · exact False.elim (hcomplement (hdiv.trans (Subgroup.card_map_dvd _ quotient)))
  have hmappedBot := Subgroup.card_eq_one.mp hcard
  have hkernelLe := (Subgroup.map_eq_bot_iff subgroup).mp hmappedBot
  simpa only [hquotientKernel] using hkernelLe

theorem prime_complement_le_theta_of_map_le_central_pKernel
    {G : Type u} {H : Type v} [Group G] [Group H] [Finite G] [Finite H]
    (prime : ℕ) (hprime : prime.Prime) (homomorphism : G →* H)
    (hsurjective : Function.Surjective homomorphism)
    (hcentral : homomorphism.ker ≤ Subgroup.center G)
    (hkernel : IsPGroup prime homomorphism.ker) (subgroup : Subgroup G)
    (hcomplement : ¬prime ∣ Nat.card subgroup)
    (hmappedLe : subgroup.map homomorphism ≤ solvablePrimeComplementCore H prime) :
    subgroup ≤ solvablePrimeComplementCore G prime := by
  have hle := Subgroup.map_le_iff_le_comap.mp hmappedLe
  rw [solvablePrimeComplementCore_comap_eq_of_central_kernel prime hprime homomorphism
    hsurjective hcentral] at hle
  exact prime_complement_le_normal_of_le_sup_pSubgroup prime hprime subgroup
    (solvablePrimeComplementCore G prime) homomorphism.ker
    (solvablePrimeComplementCore_properties G prime hprime).1 hkernel hcomplement hle

theorem thetaCoreOf_element_centralizer_map_eq_of_central_pKernel
    {G : Type u} {H : Type v} [Group G] [Group H] [Finite G] [Finite H]
    (prime : ℕ) (hprime : prime.Prime) (homomorphism : G →* H)
    (hsurjective : Function.Surjective homomorphism)
    (hcentral : homomorphism.ker ≤ Subgroup.center G)
    (hkernel : IsPGroup prime homomorphism.ker) (element : G) :
    (thetaCoreOf prime (Subgroup.centralizer ({element} : Set G))).map homomorphism =
      thetaCoreOf prime (Subgroup.centralizer ({homomorphism element} : Set H)) := by
  have hmap := thetaCoreOf_centralizer_map_eq_of_central_pKernel prime hprime homomorphism
    hsurjective hcentral hkernel (Subgroup.closure ({element} : Set G))
  simpa only [Subgroup.centralizer_closure, MonoidHom.map_closure, Set.image_singleton] using hmap

theorem thetaPlaneCommutator_le_element_theta {G : Type u} [Group G] [Finite G]
    (prime : ℕ) (hprime : prime.Prime) (plane : Subgroup G) (hcomm : IsMulCommutative plane)
    (element : G) (hmem : element ∈ plane) :
    ⁅thetaCoreOf prime (Subgroup.centralizer ({element} : Set G)), plane⁆ ≤
      thetaCoreOf prime (Subgroup.centralizer ({element} : Set G)) := by
  exact Subgroup.le_normalizer_iff_commutator_le_left.mp
    (commutative_plane_normalizes_element_theta prime hprime plane hcomm element hmem)

theorem thetaPlaneCommutator_prime_complement {G : Type u} [Group G] [Finite G]
    (prime : ℕ) (hprime : prime.Prime) (plane : Subgroup G) (hcomm : IsMulCommutative plane)
    (element : G) (hmem : element ∈ plane) :
    ¬prime ∣ Nat.card (⁅thetaCoreOf prime (Subgroup.centralizer ({element} : Set G)), plane⁆ :
      Subgroup G) := by
  exact fun hdiv => thetaCoreOf_prime_complement prime hprime
    (Subgroup.centralizer ({element} : Set G))
    (hdiv.trans (Subgroup.card_dvd_of_le
      (thetaPlaneCommutator_le_element_theta prime hprime plane hcomm element hmem)))

theorem thetaPlaneIntersection_map_le_of_central_pKernel
    {G : Type u} {H : Type v} [Group G] [Group H] [Finite G] [Finite H]
    (prime : ℕ) (hprime : prime.Prime) (homomorphism : G →* H)
    (hsurjective : Function.Surjective homomorphism)
    (hcentral : homomorphism.ker ≤ Subgroup.center G)
    (hkernel : IsPGroup prime homomorphism.ker) (plane : Subgroup G) :
    (thetaPlaneIntersection prime plane).map homomorphism ≤
      thetaPlaneIntersection prime (plane.map homomorphism) := by
  apply le_iInf
  intro element
  apply le_iInf
  intro hmem
  apply le_iInf
  intro hne
  obtain ⟨preimage, hpreimage, rfl⟩ := Subgroup.mem_map.mp hmem
  have hpreimageNe : preimage ≠ 1 := by
    intro heq
    exact hne (heq ▸ map_one homomorphism)
  rw [← thetaCoreOf_element_centralizer_map_eq_of_central_pKernel prime hprime homomorphism
    hsurjective hcentral hkernel preimage]
  exact Subgroup.map_mono (thetaPlaneIntersection_le prime plane preimage hpreimage hpreimageNe)

theorem thetaPlaneCommutators_map_le_of_central_pKernel
    {G : Type u} {H : Type v} [Group G] [Group H] [Finite G] [Finite H]
    (prime : ℕ) (hprime : prime.Prime) (homomorphism : G →* H)
    (hsurjective : Function.Surjective homomorphism)
    (hcentral : homomorphism.ker ≤ Subgroup.center G)
    (hkernel : IsPGroup prime homomorphism.ker) (plane : Subgroup G)
    (hinjective : Set.InjOn homomorphism (plane : Set G)) :
    (thetaPlaneCommutators prime plane).map homomorphism ≤
      thetaPlaneCommutators prime (plane.map homomorphism) := by
  simp only [thetaPlaneCommutators, Subgroup.map_iSup]
  apply iSup_le
  intro element
  apply iSup_le
  intro hmem
  apply iSup_le
  intro hne
  have hmappedNe : homomorphism element ≠ 1 := by
    intro heq
    exact hne (hinjective hmem plane.one_mem (heq.trans (map_one homomorphism).symm))
  rw [Subgroup.map_commutator,
    thetaCoreOf_element_centralizer_map_eq_of_central_pKernel prime hprime homomorphism
      hsurjective hcentral hkernel]
  exact le_iSup_of_le (homomorphism element)
    (le_iSup_of_le (Subgroup.mem_map_of_mem homomorphism hmem) (le_iSup_of_le hmappedNe le_rfl))

theorem thetaPlaneAlpha_map_le_of_central_pKernel
    {G : Type u} {H : Type v} [Group G] [Group H] [Finite G] [Finite H]
    (prime : ℕ) (hprime : prime.Prime) (homomorphism : G →* H)
    (hsurjective : Function.Surjective homomorphism)
    (hcentral : homomorphism.ker ≤ Subgroup.center G)
    (hkernel : IsPGroup prime homomorphism.ker) (plane : Subgroup G)
    (hinjective : Set.InjOn homomorphism (plane : Set G)) :
    (thetaPlaneAlpha prime plane).map homomorphism ≤
      thetaPlaneAlpha prime (plane.map homomorphism) := by
  rw [thetaPlaneAlpha, Subgroup.map_sup, thetaPlaneAlpha]
  exact sup_le_sup
    (thetaPlaneCommutators_map_le_of_central_pKernel prime hprime homomorphism hsurjective
      hcentral hkernel plane hinjective)
    (thetaPlaneIntersection_map_le_of_central_pKernel prime hprime homomorphism hsurjective
      hcentral hkernel plane)

theorem thetaPlaneAlpha_le_of_quotient_alpha_le_of_injective_plane
    {G : Type u} {H : Type v} [Group G] [Group H] [Finite G] [Finite H]
    (prime : ℕ) (hprime : prime.Prime) (homomorphism : G →* H)
    (hsurjective : Function.Surjective homomorphism)
    (hcentral : homomorphism.ker ≤ Subgroup.center G)
    (hkernel : IsPGroup prime homomorphism.ker) (plane : Subgroup G)
    (hcomm : IsMulCommutative plane) (hinjective : Set.InjOn homomorphism (plane : Set G))
    (element : G) (hmem : element ∈ plane) (hne : element ≠ 1)
    (halpha : thetaPlaneAlpha prime (plane.map homomorphism) ≤ solvablePrimeComplementCore H prime) :
    thetaPlaneAlpha prime plane ≤ solvablePrimeComplementCore G prime := by
  have hmap := (thetaPlaneAlpha_map_le_of_central_pKernel prime hprime homomorphism
    hsurjective hcentral hkernel plane hinjective).trans halpha
  apply sup_le
  · apply iSup_le
    intro actor
    apply iSup_le
    intro hactor
    apply iSup_le
    intro _
    apply prime_complement_le_theta_of_map_le_central_pKernel prime hprime homomorphism
      hsurjective hcentral hkernel _
      (thetaPlaneCommutator_prime_complement prime hprime plane hcomm actor hactor)
    apply le_trans (Subgroup.map_mono (f := homomorphism) _) hmap
    exact le_sup_of_le_left (le_iSup_of_le actor
      (le_iSup_of_le hactor (le_iSup_of_le ‹actor ≠ 1› le_rfl)))
  · apply prime_complement_le_theta_of_map_le_central_pKernel prime hprime homomorphism
      hsurjective hcentral hkernel _
      (thetaPlaneIntersection_prime_complement prime hprime plane element hmem hne)
    exact (Subgroup.map_mono (f := homomorphism) le_sup_right).trans hmap

theorem thetaCoreOf_top {G : Type u} [Group G] [Finite G]
    (prime : ℕ) (hprime : prime.Prime) :
    thetaCoreOf prime (⊤ : Subgroup G) = solvablePrimeComplementCore G prime := by
  apply le_antisymm
  · exact le_solvablePrimeComplementCore prime _
      (thetaCoreOf_normal_of_normal prime hprime ⊤ inferInstance)
      (thetaCoreOf_solvable prime hprime ⊤) (thetaCoreOf_prime_complement prime hprime ⊤)
  · exact normal_solvable_primeComplement_le_thetaCoreOf prime _ ⊤ le_top
      ((solvablePrimeComplementCore_properties G prime hprime).1.subgroupOf ⊤)
      (solvablePrimeComplementCore_properties G prime hprime).2.1
      (solvablePrimeComplementCore_properties G prime hprime).2.2

theorem thetaCoreOf_element_centralizer_eq_of_central {G : Type u} [Group G] [Finite G]
    (prime : ℕ) (hprime : prime.Prime) (element : G) (hcentral : element ∈ Subgroup.center G) :
    thetaCoreOf prime (Subgroup.centralizer ({element} : Set G)) =
      solvablePrimeComplementCore G prime := by
  have hcentralizer : Subgroup.centralizer ({element} : Set G) = ⊤ := by
    apply Subgroup.centralizer_eq_top_iff_subset.mpr
    intro other hother
    exact (Set.mem_singleton_iff.mp hother) ▸ hcentral
  rw [hcentralizer, thetaCoreOf_top prime hprime]

theorem thetaPlaneAlpha_le_of_central_line_generators {G : Type u} [Group G] [Finite G]
    (prime : ℕ) (hprime : prime.Prime) (plane line : Subgroup G)
    (hlineCentral : line ≤ Subgroup.center G)
    (hgenerate : ∀ element ∈ plane, element ∉ line →
      plane ≤ line ⊔ Subgroup.closure ({element} : Set G))
    (centralElement : G) (hmem : centralElement ∈ plane)
    (hlineMem : centralElement ∈ line) (hne : centralElement ≠ 1) :
    thetaPlaneAlpha prime plane ≤ solvablePrimeComplementCore G prime := by
  apply sup_le
  · apply iSup_le
    intro element
    apply iSup_le
    intro helement
    apply iSup_le
    intro _
    by_cases hline : element ∈ line
    · rw [thetaCoreOf_element_centralizer_eq_of_central prime hprime element (hlineCentral hline)]
      have : (solvablePrimeComplementCore G prime).Normal :=
        (solvablePrimeComplementCore_properties G prime hprime).1
      exact Subgroup.commutator_le_left _ _
    · have hplaneCentralizes : plane ≤ Subgroup.centralizer
          (thetaCoreOf prime (Subgroup.centralizer ({element} : Set G)) : Set G) := by
        apply le_trans (hgenerate element helement hline)
        apply sup_le
        · exact hlineCentral.trans (Subgroup.center_le_centralizer _)
        · exact (Subgroup.closure_le_centralizer_centralizer ({element} : Set G)).trans
            (Subgroup.centralizer_le (thetaCoreOf_le prime _))
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
        (Subgroup.le_centralizer_iff.mpr hplaneCentralizes)]
      exact bot_le
  · have hle := thetaPlaneIntersection_le prime plane centralElement hmem hne
    rw [thetaCoreOf_element_centralizer_eq_of_central prime hprime centralElement
      (hlineCentral hlineMem)] at hle
    exact hle

theorem plane_generated_by_prime_line_and_element {G : Type u} [Group G] [Finite G]
    (prime : ℕ) (hprime : prime.Prime) (plane line : Subgroup G)
    (hcomm : IsMulCommutative plane) (hlineLe : line ≤ plane)
    (hplaneCard : Nat.card plane = prime ^ 2) (hlineCard : Nat.card line = prime)
    (element : G) (hmem : element ∈ plane) (houtside : element ∉ line) :
    plane ≤ line ⊔ Subgroup.closure ({element} : Set G) := by
  have : Fact prime.Prime := ⟨hprime⟩
  have : IsMulCommutative plane := hcomm
  let restrictedLine := line.subgroupOf plane
  have hrestrictedNormal : restrictedLine.Normal := by
    apply (Subgroup.normal_subgroupOf_iff_le_normalizer hlineLe).mpr
    exact (Subgroup.le_centralizer_iff_isMulCommutative.mpr hcomm).trans
      ((Subgroup.centralizer_le hlineLe).trans (Subgroup.centralizer_le_normalizer _))
  have : restrictedLine.Normal := hrestrictedNormal
  have hrestrictedCard : Nat.card restrictedLine = prime :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hlineLe).toEquiv).trans hlineCard
  have hquotientCard : Nat.card (plane ⧸ restrictedLine) = prime := by
    have hcard := restrictedLine.card_eq_card_quotient_mul_card_subgroup
    rw [hplaneCard, hrestrictedCard, pow_two] at hcard
    exact Nat.eq_of_mul_eq_mul_right hprime.pos hcard.symm
  have : Fact (Nat.card (plane ⧸ restrictedLine)).Prime := ⟨hquotientCard ▸ hprime⟩
  let quotient := QuotientGroup.mk' restrictedLine
  let internalElement : plane := ⟨element, hmem⟩
  have hquotientNe : quotient internalElement ≠ 1 := by
    intro heq
    exact houtside ((QuotientGroup.eq_one_iff internalElement).mp heq)
  have hgenerated := zpowers_eq_top_of_prime_card hquotientCard hquotientNe
  have hmapped : (Subgroup.zpowers internalElement).map quotient = ⊤ := by
    simpa only [Subgroup.zpowers_eq_closure, MonoidHom.map_closure, Set.image_singleton]
      using hgenerated
  have hcomap := congrArg (Subgroup.comap quotient) hmapped
  rw [Subgroup.comap_map_eq, QuotientGroup.ker_mk', Subgroup.comap_top] at hcomap
  have hmappedBack := congrArg (Subgroup.map plane.subtype) hcomap
  have hcyclicMap : (Subgroup.zpowers internalElement).map plane.subtype =
      Subgroup.closure ({element} : Set G) := by
    rw [Subgroup.zpowers_eq_closure, MonoidHom.map_closure, Set.image_singleton]
    rfl
  have hlineMap : restrictedLine.map plane.subtype = line :=
    Subgroup.map_subgroupOf_eq_of_le hlineLe
  have htopMap : (⊤ : Subgroup plane).map plane.subtype = plane := by
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
  rw [Subgroup.map_sup, hcyclicMap, hlineMap, htopMap, sup_comm] at hmappedBack
  exact hmappedBack.ge

theorem prime_order_subgroup_le_or_disjoint {G : Type u} [Group G]
    (prime : ℕ) (hprime : prime.Prime) (subgroup line : Subgroup G)
    (hcard : Nat.card line = prime) : line ≤ subgroup ∨ Disjoint subgroup line := by
  have : Fact (Nat.card line).Prime := ⟨hcard ▸ hprime⟩
  rcases (subgroup.subgroupOf line).eq_bot_or_eq_top_of_prime_card with hbot | htop
  · right
    apply Subgroup.disjoint_def.mpr
    intro element hsubgroup hline
    have hinternal : (⟨element, hline⟩ : line) ∈ subgroup.subgroupOf line := hsubgroup
    rw [hbot] at hinternal
    exact congrArg Subtype.val (Subgroup.mem_bot.mp hinternal)
  · left
    intro element hline
    have hinternal : (⟨element, hline⟩ : line) ∈ subgroup.subgroupOf line := by
      rw [htop]
      exact Subgroup.mem_top _
    exact hinternal

theorem injOn_of_disjoint_kernel {G : Type u} {H : Type v} [Group G] [Group H]
    (homomorphism : G →* H) (subgroup : Subgroup G)
    (hdisjoint : Disjoint subgroup homomorphism.ker) :
    Set.InjOn homomorphism (subgroup : Set G) := by
  intro first hfirst second hsecond heq
  apply mul_inv_eq_one.mp
  apply Subgroup.disjoint_def.mp hdisjoint
    (subgroup.mul_mem hfirst (subgroup.inv_mem hsecond))
  apply MonoidHom.mem_ker.mpr
  rw [map_mul, map_inv, heq, mul_inv_cancel]

theorem thetaPlaneAlpha_le_of_quotient_alpha_le_central_prime_kernel
    {G : Type u} {H : Type v} [Group G] [Group H] [Finite G] [Finite H]
    (prime : ℕ) (hprime : prime.Prime) (homomorphism : G →* H)
    (hsurjective : Function.Surjective homomorphism)
    (hcentral : homomorphism.ker ≤ Subgroup.center G)
    (hkernelCard : Nat.card homomorphism.ker = prime) (plane : Subgroup G)
    (hcomm : IsMulCommutative plane) (hplaneCard : Nat.card plane = prime ^ 2)
    (halpha : thetaPlaneAlpha prime (plane.map homomorphism) ≤ solvablePrimeComplementCore H prime) :
    thetaPlaneAlpha prime plane ≤ solvablePrimeComplementCore G prime := by
  have : Fact prime.Prime := ⟨hprime⟩
  have hkernel : IsPGroup prime homomorphism.ker :=
    IsPGroup.iff_card.mpr ⟨1, by simpa only [pow_one] using hkernelCard⟩
  rcases prime_order_subgroup_le_or_disjoint prime hprime plane homomorphism.ker hkernelCard
    with hkernelLe | hdisjoint
  · have hkernelNe : homomorphism.ker ≠ ⊥ := by
      intro heq
      have hone := Subgroup.card_eq_one.mpr heq
      rw [hkernelCard] at hone
      exact hprime.ne_one hone
    obtain ⟨centralElement, hcentralElementNe⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hkernelNe
    exact thetaPlaneAlpha_le_of_central_line_generators prime hprime plane homomorphism.ker
      hcentral (fun element hmem houtside =>
        plane_generated_by_prime_line_and_element prime hprime plane homomorphism.ker
          hcomm hkernelLe hplaneCard hkernelCard element hmem houtside)
      centralElement (hkernelLe centralElement.property) centralElement.property
      (fun heq => hcentralElementNe (Subtype.ext heq))
  · have hplaneNe : plane ≠ ⊥ := by
      intro heq
      have hone := Subgroup.card_eq_one.mpr heq
      rw [hplaneCard] at hone
      have hlarge : 1 < prime ^ 2 := by nlinarith [hprime.two_le]
      omega
    obtain ⟨element, helementNe⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hplaneNe
    exact thetaPlaneAlpha_le_of_quotient_alpha_le_of_injective_plane prime hprime homomorphism
      hsurjective hcentral hkernel plane hcomm (injOn_of_disjoint_kernel homomorphism plane hdisjoint)
      element element.property (fun heq => helementNe (Subtype.ext heq)) halpha

end CFSG.RankThreeEvenClassification.Helpers
