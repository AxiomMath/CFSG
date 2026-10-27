module

public import CFSG.LocalAnalysis.RankThreeEvenClassification.SolvableSelfCentralizingCore
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SolvableZJCharacteristic
public import CFSG.LocalAnalysis.RankThreeEvenClassification.PrimeComplementNormalizerLift
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ThompsonInjectiveTransport

public section

open CFSG.Open

namespace CFSG.RankThreeEvenClassification.Helpers

universe u

theorem solvable_zj_normalizer_factorization_sup {G : Type u}
    [Group G] [Finite G] [Group.IsSolvable G]
    (prime : ℕ) (hprime : prime.Prime) (hlarge : 5 ≤ prime) (sylow : Sylow prime G) :
    primeComplementCore G prime ⊔ Subgroup.normalizer (thompsonCenterOf (sylow : Subgroup G) : Set G) = ⊤ := by
  have : Fact prime.Prime := ⟨hprime⟩
  have hodd : Odd prime := by
    rcases hprime.eq_two_or_odd' with heq | hodd
    · omega
    · exact hodd
  let normal := primeComplementCore G prime
  have : normal.Normal := (primeComplementCore_properties G prime hprime).1
  have hcomplement : ¬prime ∣ Nat.card normal := (primeComplementCore_properties G prime hprime).2
  let quotient := QuotientGroup.mk' normal
  let quotientSylow := Sylow.mapSurjective (QuotientGroup.mk'_surjective normal) sylow
  have hquotientCharacteristic :
      Subgroup.centralizer (pCore prime (G ⧸ normal) : Set (G ⧸ normal)) ≤ pCore prime (G ⧸ normal) :=
    solvable_trivial_primeComplementCore_self_centralizing prime hprime
      (primeComplementCore_quotient_eq_bot prime hprime)
  have hcenterCharacteristic := solvable_thompsonCenterOf_characteristic prime hprime hodd quotientSylow
    hquotientCharacteristic (Or.inl hlarge)
  have htransport : thompsonCenterOf (quotientSylow : Subgroup (G ⧸ normal)) =
      (thompsonCenterOf (sylow : Subgroup G)).map quotient := by
    rw [Sylow.coe_mapSurjective]
    exact thompsonCenterOf_map_of_injective_restriction quotient (sylow : Subgroup G)
      (prime_complement_quotient_injective_on_pSubgroup prime hprime normal (sylow : Subgroup G)
        hcomplement sylow.isPGroup')
  have himageNormal : ((thompsonCenterOf (sylow : Subgroup G)).map quotient).Normal := by
    rw [← htransport]
    have : (thompsonCenterOf (quotientSylow : Subgroup (G ⧸ normal))).Characteristic := hcenterCharacteristic
    infer_instance
  exact prime_complement_normal_image_normalizer_sup prime hprime normal
    (thompsonCenterOf (sylow : Subgroup G)) hcomplement
    (sylow.isPGroup'.to_le (Subgroup.map_subtype_le _)) himageNormal

theorem solvable_zj_normalizer_factorization {G : Type u}
    [Group G] [Finite G] [Group.IsSolvable G]
    (prime : ℕ) (hprime : prime.Prime) (hlarge : 5 ≤ prime) (sylow : Sylow prime G) :
    ∀ member : G, ∃ first ∈ primeComplementCore G prime,
      ∃ second ∈ Subgroup.normalizer (thompsonCenterOf (sylow : Subgroup G) : Set G),
        first * second = member := by
  have : (primeComplementCore G prime).Normal := (primeComplementCore_properties G prime hprime).1
  have hsup := solvable_zj_normalizer_factorization_sup prime hprime hlarge sylow
  intro member
  apply Subgroup.mem_sup_of_normal_left.mp
  rw [hsup]
  exact Subgroup.mem_top member

end CFSG.RankThreeEvenClassification.Helpers
