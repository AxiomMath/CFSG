module

public import CFSG.LocalAnalysis.RankThreeEvenClassification.ReplacementProduct

public section

namespace CFSG.RankThreeEvenClassification.Helpers

universe u

theorem normalized_intersection_index_dvd {G : Type u} [Group G] [Finite G]
    (first second : Subgroup G) (hnormalizes : first ≤ Subgroup.normalizer (second : Set G)) :
    (first.subgroupOf second).index ∣ first.index := by
  have hproduct := normalized_sup_card_mul_inf second first hnormalizes
  rw [sup_comm second first, inf_comm second first] at hproduct
  have hintersection : Nat.card (first.subgroupOf second) = Nat.card (first ⊓ second : Subgroup G) := by
    rw [← Subgroup.subgroupOf_map_subtype first second]
    exact (Subgroup.card_map_of_injective second.subtype_injective).symm
  have hsecondCard := (first.subgroupOf second).card_mul_index
  rw [hintersection] at hsecondCard
  have hcancel : Nat.card (first ⊔ second : Subgroup G) =
      Nat.card first * (first.subgroupOf second).index := by
    apply mul_right_cancel₀ (Nat.card_pos.ne' : Nat.card (first ⊓ second : Subgroup G) ≠ 0)
    rw [hproduct]
    calc
      Nat.card second * Nat.card first = Nat.card first *
          (Nat.card (first ⊓ second : Subgroup G) * (first.subgroupOf second).index) := by
        rw [hsecondCard, mul_comm]
      _ = Nat.card first * (first.subgroupOf second).index * Nat.card (first ⊓ second : Subgroup G) := by ring
  have hsupCard := (first ⊔ second : Subgroup G).card_mul_index
  rw [hcancel, mul_assoc] at hsupCard
  have hindices : (first.subgroupOf second).index * (first ⊔ second : Subgroup G).index = first.index :=
    mul_left_cancel₀ (Nat.card_pos.ne') (hsupCard.trans first.card_mul_index.symm)
  exact ⟨(first ⊔ second : Subgroup G).index, hindices.symm⟩

@[expose] noncomputable def sylowNormalIntersection {G : Type u} [Group G] [Finite G]
    (prime : ℕ) (hprime : prime.Prime) (sylow : Sylow prime G)
    (normal : Subgroup G) [normal.Normal] : Sylow prime normal := by
  have : Fact prime.Prime := ⟨hprime⟩
  have hpgroup : IsPGroup prime ((sylow : Subgroup G).subgroupOf normal) :=
    sylow.isPGroup'.comap_subtype
  apply hpgroup.toSylow
  have hnormalizes : (sylow : Subgroup G) ≤ Subgroup.normalizer (normal : Set G) := by
    rw [Subgroup.normalizer_eq_top]
    exact le_top
  intro hdivisor
  have hindices : ((sylow : Subgroup G).subgroupOf normal).index ∣ (sylow : Subgroup G).index :=
    normalized_intersection_index_dvd (sylow : Subgroup G) normal hnormalizes
  exact sylow.not_dvd_index (hdivisor.trans hindices)

theorem sylowNormalIntersection_coe {G : Type u} [Group G] [Finite G]
    (prime : ℕ) (hprime : prime.Prime) (sylow : Sylow prime G)
    (normal : Subgroup G) [normal.Normal] :
    (sylowNormalIntersection prime hprime sylow normal : Subgroup normal) =
      (sylow : Subgroup G).subgroupOf normal := by
  have : Fact prime.Prime := ⟨hprime⟩
  unfold sylowNormalIntersection
  exact IsPGroup.toSylow_coe _ _

end CFSG.RankThreeEvenClassification.Helpers
