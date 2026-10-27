module

public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerSubgroups
public import CFSG.LocalAnalysis.RankThreeEvenClassification.InvariantSylow

public section

open CFSG.Open

namespace CFSG.RankThreeEvenClassification.Helpers

universe u

@[expose] def signalizerSpectrum {G : Type u} [Group G] (actor : Subgroup G)
    (signalizer : G → Subgroup G) : Set ℕ :=
  {prime | prime.Prime ∧ ∃ element ∈ actor, element ≠ 1 ∧ prime ∣ Nat.card (signalizer element)}

theorem acting_prime_not_mem_signalizerSpectrum {G : Type u} [Group G]
    (prime : ℕ) (hprime : prime.Prime) (actor : Subgroup G) (signalizer : G → Subgroup G)
    (hsignalizer : IsSolvableSignalizerFunctor prime actor signalizer) :
    prime ∉ signalizerSpectrum actor signalizer := by
  rintro ⟨_, element, hmem, hne, hdiv⟩
  exact hprime.coprime_iff_not_dvd.mp (hsignalizer.coprime element hmem hne) hdiv

theorem normalized_solvable_prime_subgroup_has_nontrivial_fixed
    {G : Type u} [Group G] [Finite G]
    (prime : ℕ) (hprime : prime.Prime) (plane subgroup : Subgroup G)
    (hpower : ∀ member : plane, member ^ prime = 1) (hplaneCard : Nat.card plane = prime ^ 2)
    (hsolvable : Group.IsSolvable subgroup) (hcomplement : ¬prime ∣ Nat.card subgroup)
    (hnormalized : plane ≤ Subgroup.normalizer (subgroup : Set G)) (hne : subgroup ≠ ⊥) :
    ∃ member : plane, member ≠ 1 ∧ subgroup ⊓ Subgroup.centralizer {(member : G)} ≠ ⊥ := by
  classical
  by_contra hexists
  have hfixed : ∀ member : plane, member ≠ 1 →
      subgroup ⊓ Subgroup.centralizer {(member : G)} = ⊥ := by
    intro member hmember
    by_contra hnontrivial
    exact hexists ⟨member, hmember, hnontrivial⟩
  have hbot : subgroup = ⊥ := by
    rw [solvable_centralizer_generation_of_plane prime hprime plane subgroup hpower hplaneCard
      hsolvable hcomplement hnormalized]
    apply bot_unique
    apply iSup_le
    intro member
    apply iSup_le
    intro hne
    rw [hfixed member hne]
  exact hne hbot

theorem SignalizerCompatible.prime_dvd_mem_spectrum
    {G : Type u} [Group G] [Finite G]
    (prime : ℕ) (hprime : prime.Prime) (actor plane : Subgroup G) (signalizer : G → Subgroup G)
    (hpgroup : IsPGroup prime actor) (hplaneLe : plane ≤ actor)
    (hpower : ∀ member : plane, member ^ prime = 1) (hplaneCard : Nat.card plane = prime ^ 2)
    (subgroup : Subgroup G) (hcompatible : SignalizerCompatible prime actor signalizer subgroup)
    (supportPrime : ℕ) (hsupportPrime : supportPrime.Prime) (hdiv : supportPrime ∣ Nat.card subgroup) :
    supportPrime ∈ signalizerSpectrum actor signalizer := by
  have : Fact supportPrime.Prime := ⟨hsupportPrime⟩
  obtain ⟨sylow, hsylowNormalized⟩ := exists_normalized_sylow_in_prime_complement_subgroup prime hprime
    actor subgroup hpgroup hcompatible.primeComplement hcompatible.normalized supportPrime hsupportPrime
  let ambientSylow := (sylow : Subgroup subgroup).map subgroup.subtype
  have hsylowLe : ambientSylow ≤ subgroup := Subgroup.map_subtype_le _
  have hsylowPGroup : IsPGroup supportPrime ambientSylow := sylow.isPGroup'.map subgroup.subtype
  have hsylowSolvable : Group.IsSolvable ambientSylow := by
    have : Group.IsSolvable subgroup := hcompatible.solvable
    exact Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hsylowLe)
      (Subgroup.inclusion_injective hsylowLe)
  have hsylowComplement : ¬prime ∣ Nat.card ambientSylow :=
    fun hdiv => hcompatible.primeComplement (hdiv.trans (Subgroup.card_dvd_of_le hsylowLe))
  have hsylowNe : ambientSylow ≠ ⊥ := by
    intro heq
    have hcard : Nat.card ambientSylow = Nat.card (sylow : Subgroup subgroup) :=
      Subgroup.card_map_of_injective subgroup.subtype_injective
    have hdivSylow := sylow.dvd_card_of_dvd_card hdiv
    rw [← hcard, heq, Subgroup.card_bot] at hdivSylow
    exact hsupportPrime.not_dvd_one hdivSylow
  obtain ⟨member, hmemberNe, hfixedNe⟩ := normalized_solvable_prime_subgroup_has_nontrivial_fixed
    prime hprime plane ambientSylow hpower hplaneCard hsylowSolvable hsylowComplement
      (hplaneLe.trans hsylowNormalized) hsylowNe
  have hfixedPGroup : IsPGroup supportPrime
      (ambientSylow ⊓ Subgroup.centralizer {(member : G)} : Subgroup G) :=
    hsylowPGroup.of_injective (Subgroup.inclusion inf_le_left)
      (Subgroup.inclusion_injective inf_le_left)
  have hfixedDiv : supportPrime ∣ Nat.card
      (ambientSylow ⊓ Subgroup.centralizer {(member : G)} : Subgroup G) := by
    rcases hfixedPGroup.card_eq_or_dvd with hone | hdiv
    · exact False.elim (hfixedNe (Subgroup.card_eq_one.mp hone))
    · exact hdiv
  have hmemberAmbientNe : (member : G) ≠ 1 := fun heq => hmemberNe (Subtype.ext heq)
  have hfixedLe : ambientSylow ⊓ Subgroup.centralizer {(member : G)} ≤ signalizer member :=
    (inf_le_inf hsylowLe le_rfl).trans
      (hcompatible.fixed_le member (hplaneLe member.property) hmemberAmbientNe)
  exact ⟨hsupportPrime, member, hplaneLe member.property, hmemberAmbientNe,
    hfixedDiv.trans (Subgroup.card_dvd_of_le hfixedLe)⟩

theorem signalizer_complete_of_spectrum_empty {G : Type u} [Group G]
    (prime : ℕ) (hprime : prime.Prime) (actor : Subgroup G) (signalizer : G → Subgroup G)
    (hempty : signalizerSpectrum actor signalizer = ∅) : SignalizerComplete prime actor signalizer := by
  have hvalues : ∀ element ∈ actor, element ≠ 1 → signalizer element = ⊥ := by
    intro element hmem hne
    apply Subgroup.card_eq_one.mp
    by_contra hcard
    obtain ⟨supportPrime, hsupportPrime, hdiv⟩ := Nat.exists_prime_and_dvd hcard
    have hspectrum : supportPrime ∈ signalizerSpectrum actor signalizer :=
      ⟨hsupportPrime, element, hmem, hne, hdiv⟩
    rw [hempty] at hspectrum
    exact hspectrum
  have hgenerated : signalizerGenerated actor signalizer = ⊥ := by
    apply bot_unique
    apply iSup_le
    intro element
    apply iSup_le
    intro hmem
    apply iSup_le
    intro hne
    rw [hvalues element hmem hne]
  change SignalizerCompatible prime actor signalizer _
  rw [hgenerated]
  exact SignalizerCompatible.bot prime hprime actor signalizer

end CFSG.RankThreeEvenClassification.Helpers
