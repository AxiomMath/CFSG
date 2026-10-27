module

public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.PrimeComplementCore
import CFSG.LocalAnalysis.SectionRank.SubgroupRank

public section

open CFSG.Open
open CFSG.Open

namespace CFSG.RankThreeCoreUniqueness.Helpers

theorem coprime_kernel_injective_on_pGroup
    {Source Target : Type*} [Group Source] [Finite Source] [Group Target]
    (prime : ℕ) (hprime : prime.Prime) (homomorphism : Source →* Target)
    (hkernel : prime.Coprime (Nat.card homomorphism.ker))
    (subgroup : Subgroup Source) (hgroup : IsPGroup prime subgroup) :
    Function.Injective (homomorphism.comp subgroup.subtype) := by
  let : Fact prime.Prime := ⟨hprime⟩
  obtain ⟨exponent, hcard⟩ := IsPGroup.iff_card.mp hgroup
  have hcoprime : (Nat.card subgroup).Coprime (Nat.card homomorphism.ker) := by
    rw [hcard]
    exact hkernel.pow_left exponent
  have hdisjoint : Disjoint subgroup homomorphism.ker :=
    Subgroup.disjoint_of_coprime_natCard hcoprime
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply le_bot_iff.mp
  intro element helement
  have hintersection : (element : Source) ∈ subgroup ⊓ homomorphism.ker :=
    ⟨element.property, helement⟩
  rw [hdisjoint.eq_bot] at hintersection
  exact Subgroup.mem_bot.mpr (Subtype.ext (Subgroup.mem_bot.mp hintersection))

theorem coprime_kernel_pGroup_equiv_image
    {Source Target : Type*} [Group Source] [Finite Source] [Group Target]
    (prime : ℕ) (hprime : prime.Prime) (homomorphism : Source →* Target)
    (hkernel : prime.Coprime (Nat.card homomorphism.ker))
    (subgroup : Subgroup Source) (hgroup : IsPGroup prime subgroup) :
    Nonempty (subgroup ≃* Subgroup.map homomorphism subgroup) := by
  let restrictedMap := homomorphism.comp subgroup.subtype
  let codomainMap : subgroup →* Subgroup.map homomorphism subgroup :=
    restrictedMap.codRestrict _ (fun element => Subgroup.mem_map_of_mem _ element.property)
  have hinjective : Function.Injective codomainMap := by
    intro first second hequal
    exact coprime_kernel_injective_on_pGroup prime hprime homomorphism hkernel subgroup hgroup
      (congrArg Subtype.val hequal)
  have hsurjective : Function.Surjective codomainMap := by
    rintro ⟨element, ⟨preimage, hpreimage, hequal⟩⟩
    refine ⟨⟨preimage, hpreimage⟩, ?_⟩
    exact Subtype.ext hequal
  exact ⟨MulEquiv.ofBijective codomainMap ⟨hinjective, hsurjective⟩⟩

theorem coprime_kernel_lifts_pSubgroup
    {Source Target : Type*} [Group Source] [Finite Source] [Group Target]
    (prime : ℕ) (hprime : prime.Prime) (homomorphism : Source →* Target)
    (hsurjective : Function.Surjective homomorphism)
    (hkernel : prime.Coprime (Nat.card homomorphism.ker))
    (subgroup : Subgroup Target) (hgroup : IsPGroup prime subgroup) :
    ∃ liftGroup : Subgroup Source, IsPGroup prime liftGroup ∧
      Nonempty (liftGroup ≃* subgroup) := by
  let : Fact prime.Prime := ⟨hprime⟩
  let preimageGroup := Subgroup.comap homomorphism subgroup
  let restrictedMap : preimageGroup →* subgroup :=
    (homomorphism.comp preimageGroup.subtype).codRestrict subgroup
      (fun element => element.property)
  have hrestrictedSurjective : Function.Surjective restrictedMap := by
    intro element
    obtain ⟨preimage, hpreimage⟩ := hsurjective element.val
    have hmem : preimage ∈ preimageGroup := by
      change homomorphism preimage ∈ subgroup
      rw [hpreimage]
      exact element.property
    exact ⟨⟨preimage, hmem⟩, Subtype.ext hpreimage⟩
  let targetSylow : Sylow prime subgroup := Classical.choice inferInstance
  obtain ⟨sourceSylow, hsourceSylow⟩ :=
    Sylow.mapSurjective_surjective hrestrictedSurjective prime targetSylow
  have htargetTop : (targetSylow : Subgroup subgroup) = ⊤ := by
    exact top_le_iff.mp ((hgroup.to_subgroup (⊤ : Subgroup subgroup)).le_sylow_of_normal
      targetSylow)
  have himageTop : Subgroup.map restrictedMap (sourceSylow : Subgroup preimageGroup) = ⊤ := by
    rw [← Sylow.coe_mapSurjective hrestrictedSurjective, hsourceSylow, htargetTop]
  let liftGroup := Subgroup.map preimageGroup.subtype (sourceSylow : Subgroup preimageGroup)
  have hliftPGroup : IsPGroup prime liftGroup := sourceSylow.isPGroup'.map preimageGroup.subtype
  have himage : Subgroup.map homomorphism liftGroup = subgroup := by
    have hmapped := congrArg (Subgroup.map subgroup.subtype) himageTop
    rw [Subgroup.map_map, ← MonoidHom.range_eq_map, subgroup.subtype_range] at hmapped
    have hmaps : subgroup.subtype.comp restrictedMap = homomorphism.comp preimageGroup.subtype := by
      ext element
      rfl
    rw [hmaps, ← Subgroup.map_map] at hmapped
    exact hmapped
  obtain ⟨liftEquiv⟩ := coprime_kernel_pGroup_equiv_image prime hprime homomorphism hkernel
    liftGroup hliftPGroup
  exact ⟨liftGroup, hliftPGroup, ⟨liftEquiv.trans (MulEquiv.subgroupCongr himage)⟩⟩

theorem pRank_top_le_of_injective
    {Source Target : Type*} [Group Source] [Finite Source] [Group Target] [Finite Target]
    (prime : ℕ) (hprime : 1 < prime) (homomorphism : Source →* Target)
    (hinjective : Function.Injective homomorphism) :
    pRank prime (⊤ : Subgroup Source) ≤ pRank prime (⊤ : Subgroup Target) :=
  CFSG.SectionRank.pRank_top_le_of_injective hprime homomorphism hinjective

theorem pRank_top_eq_of_equiv
    {Source Target : Type*} [Group Source] [Finite Source] [Group Target] [Finite Target]
    (prime : ℕ) (hprime : 1 < prime) (equivalence : Source ≃* Target) :
    pRank prime (⊤ : Subgroup Source) = pRank prime (⊤ : Subgroup Target) :=
  CFSG.SectionRank.pRank_top_eq_of_mulEquiv hprime equivalence

theorem pRank_subgroup_eq_internal_top
    {G : Type*} [Group G] [Finite G] (prime : ℕ) (_hprime : 1 < prime)
    (subgroup : Subgroup G) :
    pRank prime subgroup = pRank prime (⊤ : Subgroup subgroup) :=
  CFSG.SectionRank.pRank_eq_pRank_top_subgroup subgroup

theorem pRank_top_eq_of_coprime_kernel
    {Source Target : Type*} [Group Source] [Finite Source] [Group Target] [Finite Target]
    (prime : ℕ) (hprime : prime.Prime) (homomorphism : Source →* Target)
    (hsurjective : Function.Surjective homomorphism)
    (hkernel : prime.Coprime (Nat.card homomorphism.ker)) :
    pRank prime (⊤ : Subgroup Source) = pRank prime (⊤ : Subgroup Target) := by
  apply le_antisymm
  · apply csSup_le'
    rintro exponent ⟨elementary, _, helementary, hcard⟩
    obtain ⟨equivalence⟩ := coprime_kernel_pGroup_equiv_image prime hprime homomorphism hkernel
      elementary (elementary_isPGroup prime elementary helementary)
    apply le_csSup (pRank_set_bddAbove prime hprime.one_lt (⊤ : Subgroup Target))
    refine ⟨Subgroup.map homomorphism elementary, le_top,
      elementary_transport prime elementary _ equivalence helementary, ?_⟩
    exact (Nat.card_congr equivalence.toEquiv).symm.trans hcard
  · apply csSup_le'
    rintro exponent ⟨elementary, _, helementary, hcard⟩
    obtain ⟨liftGroup, _, ⟨equivalence⟩⟩ := coprime_kernel_lifts_pSubgroup prime hprime
      homomorphism hsurjective hkernel elementary (elementary_isPGroup prime elementary helementary)
    apply le_csSup (pRank_set_bddAbove prime hprime.one_lt (⊤ : Subgroup Source))
    refine ⟨liftGroup, le_top, elementary_transport prime elementary liftGroup equivalence.symm
      helementary, ?_⟩
    exact (Nat.card_congr equivalence.toEquiv).trans hcard

theorem primeComplementCore_quotient_pRank_eq
    {G : Type*} [Group G] [Finite G] (prime : ℕ) (hprime : prime.Prime) :
    pRank prime (⊤ : Subgroup (G ⧸ primeComplementCore prime)) =
      pRank prime (⊤ : Subgroup G) := by
  apply (pRank_top_eq_of_coprime_kernel prime hprime
    (QuotientGroup.mk' (primeComplementCore (G := G) prime))
    (QuotientGroup.mk'_surjective _) ?_).symm
  rw [QuotientGroup.ker_mk']
  exact primeComplementCore_coprime prime

end CFSG.RankThreeCoreUniqueness.Helpers
