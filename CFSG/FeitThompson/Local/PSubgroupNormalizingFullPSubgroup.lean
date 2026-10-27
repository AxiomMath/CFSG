module

public import Mathlib.GroupTheory.Sylow
import CFSG.FeitThompson.Foundations.ProductSubgroupsCardinality
import CFSG.FeitThompson.Foundations.SubgroupOrderAndIndex

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Pointwise Subgroup

namespace CFSG.FeitThompson

variable {L : Type*} [Group L] {p : ℕ}

theorem natCard_sup_mul_natCard_inf_of_le_normalizer {S T : Subgroup L}
    (hTS : T ≤ normalizer (S : Set L)) :
    Nat.card (S ⊔ T : Subgroup L) * Nat.card (S ⊓ T : Subgroup L) = Nat.card S * Nat.card T := by
  have h : ((S ⊔ T : Subgroup L) : Set L) = (S : Set L) * (T : Set L) :=
    Subgroup.coe_mul_of_right_le_normalizer_left S T hTS
  have h2 : Nat.card (S ⊔ T : Subgroup L) = Nat.card ((S : Set L) * (T : Set L)) := by
    simpa using Nat.card_congr (Set.equivOfEq h)
  rw [h2, natCard_mul_mul_natCard_inf]

theorem le_of_isPGroup_of_le_normalizer_of_natCard_eq [Finite L] (hp : p.Prime) {S T : Subgroup L}
    (hS : Nat.card S = p ^ (Nat.card L).factorization p) (hT : IsPGroup p T)
    (hTS : T ≤ normalizer (S : Set L)) : T ≤ S := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := p) (G := T)).1 hT
  have hdvd : Nat.card (S ⊔ T : Subgroup L) ∣ p ^ ((Nat.card L).factorization p + n) := by
    refine Dvd.intro (Nat.card (S ⊓ T : Subgroup L)) ?_
    rw [pow_add, ← hS, ← hn, ← natCard_sup_mul_natCard_inf_of_le_normalizer hTS]
  obtain ⟨k, hk, hcard⟩ := (Nat.dvd_prime_pow hp).1 hdvd
  have hLdvd : Nat.card (S ⊔ T : Subgroup L) ∣ Nat.card L :=
    ⟨Nat.card (Set.range fun g : L => g • ((S ⊔ T : Subgroup L) : Set L)),
      by rw [natCard_eq_natCard_range_leftCoset_mul_natCard (S ⊔ T), mul_comm]⟩
  have hkle : k ≤ (Nat.card L).factorization p := by
    rw [← hp.pow_dvd_iff_le_factorization Nat.card_pos.ne']
    exact hcard ▸ hLdvd
  have hSST : S = S ⊔ T := by
    refine Subgroup.eq_of_le_of_card_ge le_sup_left ?_
    rw [hS, hcard]
    exact Nat.pow_le_pow_right hp.one_lt.le hkle
  exact le_sup_right.trans hSST.ge

theorem sup_eq_left_of_isPGroup_of_le_normalizer_of_natCard_eq [Finite L] (hp : p.Prime)
    {S T : Subgroup L} (hS : Nat.card S = p ^ (Nat.card L).factorization p) (hT : IsPGroup p T)
    (hTS : T ≤ normalizer (S : Set L)) : S ⊔ T = S :=
  sup_eq_left.2 (le_of_isPGroup_of_le_normalizer_of_natCard_eq hp hS hT hTS)

theorem le_sylow_of_isPGroup_of_le_normalizer [Finite L] [Fact p.Prime] (P : Sylow p L)
    {T : Subgroup L} (hT : IsPGroup p T) (hTP : T ≤ normalizer ((P : Subgroup L) : Set L)) :
    T ≤ (P : Subgroup L) :=
  le_of_isPGroup_of_le_normalizer_of_natCard_eq Fact.out P.card_eq_multiplicity hT hTP

end CFSG.FeitThompson
