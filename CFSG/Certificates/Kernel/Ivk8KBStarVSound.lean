module

public import Certificates.Data.Kernel.Ivk8KBStarV
public import CFSG.Certificates.Kernel.Ivk8NormSound

public section

namespace CFSG.KS.Ivk8KBStarV

open CFSG.Certificates.Kernel.PkEnum CFSG.KS.PK CFSG.KS.Ivk8Norm

variable {n : Nat}

theorem pkp_powV (a : VP n) (k : Nat) : pkp (powV a k) = pkp a ^ k := by
  induction k with
  | zero => exact pkp_oneV n
  | succ k ih =>
    change pkp (mulV (powV a k) a) = _
    rw [pkp_mulV, ih, pow_succ]

theorem difV_pow_one_iff (a : VP n) (p : Nat) :
    difV (powV a p) (oneV n) = true ↔ pkp a ^ p ≠ 1 := by
  rw [difV_eq_true_iff, pkp_powV, pkp_oneV]

theorem witAny_cons (p : Nat) (c : VP n) (W : List (VP n)) (z : VP n) :
    witAny p (c :: W) z = (difV (powV (mulV z (conjV c z)) p) (oneV n) || witAny p W z) := by
  change Bool.rec (motive := fun _ => Bool) (witAny p W z) true
    (difV (powV (mulV z (conjV c z)) p) (oneV n)) = _
  cases difV (powV (mulV z (conjV c z)) p) (oneV n) <;> rfl

theorem witAny_spec {p : Nat} {W : List (VP n)} {z : VP n} (h : witAny p W z = true) :
    ∃ c ∈ W, (pkp z * (pkp c * pkp z * (pkp c)⁻¹)) ^ p ≠ 1 := by
  induction W with
  | nil => exact absurd h Bool.false_ne_true
  | cons c W ih =>
    rw [witAny_cons, Bool.or_eq_true] at h
    rcases h with h | h
    · refine ⟨c, List.mem_cons_self .., ?_⟩
      rw [difV_pow_one_iff, pkp_mulV, pkp_conjV] at h
      exact h
    · obtain ⟨c', hc', hne⟩ := ih h
      exact ⟨c', List.mem_cons_of_mem _ hc', hne⟩

theorem rowZ_spec {p : Nat} {W : List (VP n)} {z : VP n} (h : rowZ p W z = true)
    (hp : pkp z ^ p = 1) (h1 : pkp z ≠ 1) :
    ∃ c ∈ W, (pkp z * (pkp c * pkp z * (pkp c)⁻¹)) ^ p ≠ 1 := by
  have cp : difV (powV z p) (oneV n) = false := by
    cases hc : difV (powV z p) (oneV n)
    · rfl
    · exact absurd hp ((difV_pow_one_iff z p).1 hc)
  have c1 : difV z (oneV n) = true := by
    rw [difV_eq_true_iff, pkp_oneV]
    exact h1
  rw [rowZ, cp, c1] at h
  exact witAny_spec h

theorem rowOK_cons (p : Nat) (W : List (VP n)) (z : VP n) (K : List (VP n)) :
    rowOK p W (z :: K) = (rowZ p W z && rowOK p W K) := by
  change Bool.rec (motive := fun _ => Bool) false (rowOK p W K) (rowZ p W z) = _
  cases rowZ p W z <;> rfl

theorem rowOK_spec {p : Nat} {W K : List (VP n)} (h : rowOK p W K = true) :
    ∀ σ ∈ K.map pkp, σ ^ p = 1 → σ ≠ 1 → ∃ c ∈ W, (σ * (pkp c * σ * (pkp c)⁻¹)) ^ p ≠ 1 := by
  induction K with
  | nil => intro σ hσ; simp at hσ
  | cons z K ih =>
    rw [rowOK_cons, Bool.and_eq_true] at h
    intro σ hσ
    rw [List.map_cons, List.mem_cons] at hσ
    rcases hσ with rfl | hσ
    · exact rowZ_spec h.1
    · exact ih h.2 σ hσ

theorem movesOK_cons (d z : VP n) (K : List (VP n)) :
    movesOK d (z :: K) = (movesZ d z && movesOK d K) := by
  change Bool.rec (motive := fun _ => Bool) false (movesOK d K) (movesZ d z) = _
  cases movesZ d z <;> rfl

theorem movesZ_spec {d z : VP n} (h : movesZ d z = true) (h1 : pkp z ≠ 1) :
    pkp d * pkp z * (pkp d)⁻¹ ≠ pkp z ∧ pkp d * pkp z * (pkp d)⁻¹ ≠ (pkp z)⁻¹ := by
  have c1 : difV z (oneV n) = true := by
    rw [difV_eq_true_iff, pkp_oneV]
    exact h1
  rw [movesZ, c1] at h
  exact moves_of_movesV h

theorem movesOK_spec {d : VP n} {K : List (VP n)} (h : movesOK d K = true) :
    ∀ σ ∈ K.map pkp, σ ≠ 1 → pkp d * σ * (pkp d)⁻¹ ≠ σ ∧ pkp d * σ * (pkp d)⁻¹ ≠ σ⁻¹ := by
  induction K with
  | nil => intro σ hσ; simp at hσ
  | cons z K ih =>
    rw [movesOK_cons, Bool.and_eq_true] at h
    intro σ hσ
    rw [List.map_cons, List.mem_cons] at hσ
    rcases hσ with rfl | hσ
    · exact movesZ_spec h.1
    · exact ih h.2 σ hσ

end CFSG.KS.Ivk8KBStarV

end
