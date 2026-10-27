module

public import Mathlib.GroupTheory.Sylow

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open Subgroup

variable {G : Type*} [Group G]

def maximalNormalizedPSubgroups (A : Subgroup G) (q : ℕ) : Set (Subgroup G) :=
  {Q | Maximal (fun R : Subgroup G => IsPGroup q R ∧ A ≤ normalizer (R : Set G)) Q}

variable {A Q R : Subgroup G} {q : ℕ}

theorem mem_maximalNormalizedPSubgroups_iff :
    Q ∈ maximalNormalizedPSubgroups A q ↔
      (IsPGroup q Q ∧ A ≤ normalizer (Q : Set G)) ∧
        ∀ R : Subgroup G, IsPGroup q R → A ≤ normalizer (R : Set G) → Q ≤ R → R = Q := by
  constructor
  · intro h
    exact ⟨h.1, fun R h1 h2 hQR => le_antisymm (h.2 ⟨h1, h2⟩ hQR) hQR⟩
  · intro h
    exact ⟨h.1, fun R hR hQR => (h.2 R hR.1 hR.2 hQR).le⟩

theorem mem_maximalNormalizedPSubgroups_of_forall
    (hQ : IsPGroup q Q) (hQA : A ≤ normalizer (Q : Set G))
    (hmax : ∀ R : Subgroup G, IsPGroup q R → A ≤ normalizer (R : Set G) → Q ≤ R → R = Q) :
    Q ∈ maximalNormalizedPSubgroups A q :=
  mem_maximalNormalizedPSubgroups_iff.2 ⟨⟨hQ, hQA⟩, hmax⟩

theorem isPGroup_of_mem (h : Q ∈ maximalNormalizedPSubgroups A q) : IsPGroup q Q :=
  (mem_maximalNormalizedPSubgroups_iff.1 h).1.1

theorem le_normalizer_of_mem (h : Q ∈ maximalNormalizedPSubgroups A q) :
    A ≤ normalizer (Q : Set G) :=
  (mem_maximalNormalizedPSubgroups_iff.1 h).1.2

theorem eq_of_mem_of_le (h : Q ∈ maximalNormalizedPSubgroups A q) (hR : IsPGroup q R)
    (hRA : A ≤ normalizer (R : Set G)) (hQR : Q ≤ R) : R = Q :=
  (mem_maximalNormalizedPSubgroups_iff.1 h).2 R hR hRA hQR

theorem exists_card_eq_pow_of_mem [Finite G] [Fact q.Prime]
    (h : Q ∈ maximalNormalizedPSubgroups A q) : ∃ n : ℕ, Nat.card Q = q ^ n :=
  (isPGroup_of_mem h).exists_card_eq

theorem exists_mem_maximalNormalizedPSubgroups_ge [Finite G] (hR : IsPGroup q R)
    (hRA : A ≤ normalizer (R : Set G)) : ∃ Q ∈ maximalNormalizedPSubgroups A q, R ≤ Q := by
  obtain ⟨Q, hRQ, hQ⟩ := Finite.exists_le_maximal
    (p := fun S : Subgroup G => IsPGroup q S ∧ A ≤ normalizer (S : Set G)) (a := R) ⟨hR, hRA⟩
  exact ⟨Q, hQ, hRQ⟩

theorem maximalNormalizedPSubgroups_nonempty [Finite G] (A : Subgroup G) (q : ℕ) :
    (maximalNormalizedPSubgroups A q).Nonempty := by
  obtain ⟨Q, hQ, -⟩ := exists_mem_maximalNormalizedPSubgroups_ge (A := A) (q := q)
    IsPGroup.of_bot (by rw [Subgroup.normalizer_eq_top (⊥ : Subgroup G)]; exact le_top)
  exact ⟨Q, hQ⟩

theorem mem_maximalNormalizedPSubgroups_bot_iff :
    Q ∈ maximalNormalizedPSubgroups (⊥ : Subgroup G) q ↔
      ∃ P : Sylow q G, (P : Subgroup G) = Q := by
  constructor
  · intro h
    exact ⟨⟨Q, isPGroup_of_mem h, fun hR hQR => eq_of_mem_of_le h hR bot_le hQR⟩, rfl⟩
  · rintro ⟨P, rfl⟩
    exact mem_maximalNormalizedPSubgroups_of_forall P.isPGroup' bot_le
      fun _ hR _ hPR => P.is_maximal' hR hPR

theorem inf_eq_bot_of_notMem_primeFactors [Finite G] (hq : q.Prime)
    (hqA : q ∉ (Nat.card A).primeFactors) (h : Q ∈ maximalNormalizedPSubgroups A q) :
    A ⊓ Q = ⊥ := by
  have hp : Fact q.Prime := ⟨hq⟩
  obtain ⟨n, hn⟩ := ((isPGroup_of_mem h).to_inf_right (H := A)).exists_card_eq
  have hdvd : Nat.card (A ⊓ Q : Subgroup G) ∣ Nat.card A := Subgroup.card_dvd_of_le inf_le_left
  rcases Nat.eq_zero_or_pos n with hn0 | hn0
  · refine Subgroup.eq_bot_of_card_eq _ ?_
    rw [hn, hn0, pow_zero]
  · refine absurd (Nat.mem_primeFactors.2 ⟨hq, ?_, Nat.card_pos.ne'⟩) hqA
    exact dvd_trans (hn ▸ dvd_pow_self q hn0.ne' : q ∣ Nat.card (A ⊓ Q : Subgroup G)) hdvd

end CFSG.FeitThompson
