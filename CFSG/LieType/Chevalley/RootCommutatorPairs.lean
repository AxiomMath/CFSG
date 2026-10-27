module

public import CFSG.LieType.Chevalley.WeylRoots

public section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint.Chevalley

variable {τ : Tag}

@[expose] def commCandidates : List (ℕ × ℕ) :=
  [(1, 1), (1, 2), (2, 1), (1, 3), (2, 2), (3, 1), (2, 3), (3, 2), (3, 3)]

theorem mem_commCandidates {p : ℕ × ℕ} :
    p ∈ commCandidates ↔ (1 ≤ p.1 ∧ p.1 ≤ 3) ∧ 1 ≤ p.2 ∧ p.2 ≤ 3 := by
  obtain ⟨a, b⟩ := p
  simp only [commCandidates, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false]
  omega

theorem commCandidates_pairwise :
    commCandidates.Pairwise fun p q : ℕ × ℕ =>
      p.1 + p.2 < q.1 + q.2 ∨ (p.1 + p.2 = q.1 + q.2 ∧ p.1 < q.1) := by
  decide

open _root_.Classical in
@[expose] noncomputable def commPairs (τ : Tag) (α β : Fin τ.rank → ℤ) : List (ℕ × ℕ) :=
  commCandidates.filter fun p => decide (IsRoot τ (p.1 • α + p.2 • β))

theorem mem_commPairs {α β : Fin τ.rank → ℤ} {p : ℕ × ℕ} :
    p ∈ commPairs τ α β ↔ p ∈ commCandidates ∧ IsRoot τ (p.1 • α + p.2 • β) := by
  classical
  rw [commPairs, List.mem_filter, decide_eq_true_iff]

theorem commPairs_pairwise (α β : Fin τ.rank → ℤ) :
    (commPairs τ α β).Pairwise fun p q : ℕ × ℕ =>
      p.1 + p.2 < q.1 + q.2 ∨ (p.1 + p.2 = q.1 + q.2 ∧ p.1 < q.1) :=
  commCandidates_pairwise.sublist List.filter_sublist

theorem commPairs_nodup (α β : Fin τ.rank → ℤ) : (commPairs τ α β).Nodup :=
  (commPairs_pairwise α β).imp fun {p q} h hpq => by subst hpq; omega

theorem smul_nsmul_add_nsmul_eq
    (w : WeylGroup τ) (a b : ℕ) (α β : Fin τ.rank → ℤ) :
    w • (a • α + b • β) = a • (w • α) + b • (w • β) := by
  rw [smul_add, smul_comm w a α, smul_comm w b β]

theorem commPairs_smul
    (w : WeylGroup τ) (α β : Fin τ.rank → ℤ) :
    commPairs τ (w • α) (w • β) = commPairs τ α β := by
  classical
  refine List.filter_congr fun p _ => ?_
  rw [decide_eq_decide, ← smul_nsmul_add_nsmul_eq, isRoot_smul_iff]

end CFSG.LieType.Chevalley
