module

public import Mathlib.GroupTheory.PGroup
public import CFSG.FeitThompson.Foundations.SubgroupOrderAndIndex
import Mathlib.GroupTheory.Nilpotent
import CFSG.FeitThompson.Foundations.QuotientOrderByNormal
import CFSG.FeitThompson.Foundations.PGroupNontrivialCenter

open Pointwise

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

variable {p : ℕ} {P : Type*} [Group P] {D : Subgroup P}

theorem isSimpleGroup_quotient_of_isCoatom (hD : IsCoatom D) [D.Normal] :
    IsSimpleGroup (P ⧸ D) := by
  obtain ⟨x, hx⟩ : ∃ x : P, x ∉ D := by
    by_contra h
    exact hD.1 (Subgroup.eq_top_iff' D |>.2 (by simpa using h))
  have : Nontrivial (P ⧸ D) :=
    ⟨⟨QuotientGroup.mk x, 1, by simpa [QuotientGroup.eq_one_iff] using hx⟩⟩
  refine ⟨fun H _ => ?_⟩
  rcases eq_or_lt_of_le (QuotientGroup.le_comap_mk' D H) with h | h
  · refine Or.inl (Subgroup.comap_injective (QuotientGroup.mk'_surjective D) ?_)
    simp [← h]
  · refine Or.inr (Subgroup.comap_injective (QuotientGroup.mk'_surjective D) ?_)
    simp [hD.2 _ h]

theorem normal_of_isCoatom_of_isPGroup (hp : p.Prime) [Finite P] (hP : IsPGroup p P)
    (hD : IsCoatom D) : D.Normal :=
  have := Fact.mk hp
  Subgroup.NormalizerCondition.normal_of_coatom D
    (Group.normalizerCondition_of_isNilpotent (h := hP.isNilpotent)) hD

theorem index_eq_of_isCoatom_of_isPGroup (hp : p.Prime) [Finite P] (hP : IsPGroup p P)
    (hD : IsCoatom D) : D.index = p := by
  have := Fact.mk hp
  have hnormal : D.Normal := normal_of_isCoatom_of_isPGroup hp hP hD
  obtain ⟨n, hn⟩ := (hP.to_quotient D).exists_card_eq
  have h2 : 2 ≤ Nat.card (P ⧸ D) :=
    two_le_natCard_quotient_of_lt_top D (lt_top_iff_ne_top.2 hD.1)
  have hn1 : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · rw [h, pow_zero] at hn; omega
    · exact h
  have hcenter : Nontrivial (Subgroup.center (P ⧸ D)) := center_nontrivial hp hn hn1
  have hsimple : IsSimpleGroup (P ⧸ D) := isSimpleGroup_quotient_of_isCoatom hD
  have htop : Subgroup.center (P ⧸ D) = ⊤ := by
    rcases hsimple.eq_bot_or_eq_top_of_normal (Subgroup.center (P ⧸ D)) with h | h
    · exact absurd h ((Subgroup.nontrivial_iff_ne_bot _).1 hcenter)
    · exact h
  have : IsMulCommutative (P ⧸ D) := Subgroup.center_eq_top_iff.1 htop
  have hprime : (Nat.card (P ⧸ D)).Prime := Group.is_simple_iff_prime_card.1 hsimple
  rw [hn] at hprime
  rcases hprime.eq_one_or_self_of_dvd p (dvd_pow_self p (Nat.one_le_iff_ne_zero.1 hn1)) with h | h
  · exact absurd h hp.one_lt.ne'
  · rw [Subgroup.index_eq_card, hn, ← h]

theorem normal_and_index_eq_of_maximal (hp : p.Prime) [Finite P] (hP : IsPGroup p P)
    (hne : D ≠ ⊤) (hmax : ∀ E : Subgroup P, D < E → E = ⊤) : D.Normal ∧ D.index = p :=
  have hD : IsCoatom D := ⟨hne, hmax⟩
  ⟨normal_of_isCoatom_of_isPGroup hp hP hD, index_eq_of_isCoatom_of_isPGroup hp hP hD⟩

theorem natCard_range_leftCoset_eq_of_isCoatom_of_isPGroup (hp : p.Prime) [Finite P]
    (hP : IsPGroup p P) (hD : IsCoatom D) :
    Nat.card (Set.range fun g : P => g • (D : Set P)) = p := by
  rw [natCard_range_leftCoset, index_eq_of_isCoatom_of_isPGroup hp hP hD]

theorem natCard_eq_mul_natCard_of_isCoatom_of_isPGroup (hp : p.Prime) [Finite P]
    (hP : IsPGroup p P) (hD : IsCoatom D) : Nat.card P = p * Nat.card D := by
  rw [← index_eq_of_isCoatom_of_isPGroup hp hP hD, Subgroup.index_mul_card]

end

end CFSG.FeitThompson
