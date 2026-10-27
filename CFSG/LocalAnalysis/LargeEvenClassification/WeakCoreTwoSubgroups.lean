module

public import CFSG.LocalAnalysis.LargeEvenClassification.NormalElementary
public import CFSG.LocalAnalysis.LargeEvenClassification.InvariantKernel
public import CFSG.LocalAnalysis.LargeEvenClassification.WeakCore
public import CFSG.LocalAnalysis.LargeEvenClassification.PGroupHyperplaneGeneration

public section

open CFSG.Open

namespace CFSG.LargeEvenClassification.Helpers

universe groupUniverse

theorem elementary_pRank_card {Ambient : Type groupUniverse} [Group Ambient] [Finite Ambient]
    {prime rank : ℕ} (hprime : 1 < prime) (Elementary : Subgroup Ambient)
    (helementary : IsElemAbelian prime Elementary) (hcard : Nat.card Elementary = prime ^ rank) :
    pRank prime Elementary = rank := by
  have hlower : rank ≤ pRank prime Elementary := by
    apply le_csSup
    · refine ⟨Nat.card Ambient, ?_⟩
      rintro otherRank ⟨OtherElementary, _, _, hotherCard⟩
      exact rank_exponent_le_card hprime OtherElementary hotherCard
    · exact ⟨Elementary, le_rfl, helementary, hcard⟩
  obtain ⟨Witness, hle, _, hwitnessCard⟩ := pRank_witness hprime Elementary
  have hcardBound := Nat.card_le_card_of_injective (Subgroup.inclusion hle)
    (Subgroup.inclusion_injective hle)
  rw [hwitnessCard, hcard] at hcardBound
  exact le_antisymm ((Nat.pow_le_pow_iff_right hprime).mp hcardBound) hlower

theorem elementary_hyperplane_rank_lower {Ambient : Type groupUniverse} [Group Ambient]
    [Finite Ambient] {prime rank : ℕ} (hprime : prime.Prime) (Elementary : Subgroup Ambient)
    (helementary : IsElemAbelian prime Elementary) (hcard : Nat.card Elementary = prime ^ rank)
    (Fixers : Subgroup Elementary) (hindex : Fixers.index ≤ prime) :
    rank ≤ pRank prime (Fixers.map Elementary.subtype) + 1 := by
  let : Fact prime.Prime := ⟨hprime⟩
  have hpgroup : IsPGroup prime Fixers := (IsPGroup.of_card hcard).to_subgroup Fixers
  obtain ⟨fixerRank, hfixerCard⟩ := hpgroup.exists_card_eq
  have hmapCard : Nat.card (Fixers.map Elementary.subtype) = prime ^ fixerRank :=
    (Nat.card_congr (Fixers.equivMapOfInjective Elementary.subtype Subtype.val_injective).toEquiv).symm.trans
      hfixerCard
  have hmapElementary : IsElemAbelian prime (Fixers.map Elementary.subtype) := by
    apply elementary_subgroup_of_le Elementary (Fixers.map Elementary.subtype) helementary
    intro element helement
    obtain ⟨source, _, rfl⟩ := helement
    exact source.property
  have hformula := Fixers.index_mul_card
  rw [hfixerCard, hcard] at hformula
  have hpower : prime ^ rank ≤ prime ^ (fixerRank + 1) := by
    rw [← hformula, pow_succ]
    exact (Nat.mul_le_mul_right (prime ^ fixerRank) hindex).trans_eq (mul_comm _ _)
  rw [elementary_pRank_card hprime.one_lt _ hmapElementary hmapCard]
  exact (Nat.pow_le_pow_iff_right hprime.one_lt).mp hpower

theorem normalized_two_subgroup_le_weak_core {Ambient : Type groupUniverse} [Group Ambient]
    [Finite Ambient] {prime rank : ℕ} (hprime : prime.Prime) (hodd : prime ≠ 2)
    (Parent Elementary TwoSubgroup : Subgroup Ambient)
    (helementary : IsElemAbelian prime Elementary) (hcard : Nat.card Elementary = prime ^ rank)
    (hrank : 4 ≤ rank) (helementaryLe : Elementary ≤ Parent)
    (hpgroup : IsPGroup 2 TwoSubgroup)
    (hstable : ∀ conjugator : Elementary, ∀ element : Ambient, element ∈ TwoSubgroup →
      conjugator.val * element * conjugator.val⁻¹ ∈ TwoSubgroup) :
    TwoSubgroup ≤ weakTwoGeneratedPCore prime Parent := by
  let : CommGroup Elementary := { (inferInstance : Group Elementary) with
    mul_comm := @mul_comm' Elementary _ helementary.1 }
  let action := invariantSubgroupConjugation Elementary.subtype TwoSubgroup hstable
  have hexponent : ∀ element : Elementary, element ^ prime = 1 := by
    intro element
    apply Subtype.ext
    exact helementary.2 element element.property
  have hgenerates := pGroup_hyperplane_fixed_generation hprime Nat.prime_two hodd
    (IsPGroup.of_card hcard) hexponent hpgroup action
  have helementaryRank : 3 ≤ pRank prime Elementary := by
    rw [elementary_pRank_card hprime.one_lt Elementary helementary hcard]
    omega
  have hspanLe : hyperplaneFixedSpan prime action ≤
      (weakTwoGeneratedPCore prime Parent).comap TwoSubgroup.subtype := by
    apply iSup_le
    intro Fixers element helement
    let Mapped := Fixers.val.map Elementary.subtype
    have hmappedLe : Mapped ≤ Elementary := by
      intro entry hentry
      obtain ⟨source, _, rfl⟩ := hentry
      exact source.property
    have hmappedRank : 2 ≤ pRank prime Mapped := by
      have hrankBound := elementary_hyperplane_rank_lower hprime Elementary helementary hcard
        Fixers.val Fixers.property
      change rank ≤ pRank prime Mapped + 1 at hrankBound
      omega
    have hnormalizer := elementary_normalizer_le_weak_core hprime.one_lt Parent Elementary Mapped
      helementary hmappedLe helementaryLe hmappedRank helementaryRank
    apply hnormalizer
    apply Subgroup.centralizer_le_normalizer
    apply Subgroup.mem_centralizer_iff.mpr
    intro fixer hfixer
    obtain ⟨source, hsource, rfl⟩ := hfixer
    have hfixed := congrArg (fun entry : TwoSubgroup => entry.val) (helement ⟨source, hsource⟩)
    change source.val * element.val * source.val⁻¹ = element.val at hfixed
    exact mul_inv_eq_iff_eq_mul.mp hfixed
  rw [hgenerates] at hspanLe
  intro element helement
  exact hspanLe (Subgroup.mem_top (⟨element, helement⟩ : TwoSubgroup))

end CFSG.LargeEvenClassification.Helpers
