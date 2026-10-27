module

public import Certificates.Data.Kernel.AE117Adj

public section

namespace Certificates.Kernel.AE117Adj

open Certificates.AE117 CFSG.ClassicalInvolution.Q3.AE CFSG.ClassicalInvolution.Q3.AE.Wr

variable {n : ℕ}

theorem perm_pow (x : Wr n) (m : ℕ) : (x ^ m).perm = x.perm ^ m := by
  induction m with
  | zero => rfl
  | succ m ih => rw [pow_succ, mul_perm, ih, pow_succ]

theorem perm_of_inPi {y : Wr n} (h : inPi y = true) : y.perm = 1 := by
  simp only [inPi, Bool.or_eq_true, decide_eq_true_eq] at h
  rcases h with rfl | rfl <;> rfl

theorem ord5G_eq (x : Wr n) : ord5G x = ord5Pi x := by
  unfold ord5G
  cases h : ord5Pi x
  · rw [Bool.and_false]
  · have h5 : inPi (x ^ 5) = true := by
      simp only [ord5Pi, Bool.and_eq_true] at h
      exact h.2
    rw [← perm_pow, perm_of_inPi h5]
    simp

theorem exists_quad {α : Finset (Fin n)}
    (hα : α ∈ (Finset.univ : Finset (Fin n)).powersetCard 4) :
    ∃ q ∈ quads n, α.sort (· ≤ ·) = [q.1, q.2.1, q.2.2.1, q.2.2.2] ∧ α = qset q := by
  have hcard := (Finset.mem_powersetCard.1 hα).2
  have hlen : (α.sort (· ≤ ·)).length = 4 := by rw [Finset.length_sort, hcard]
  have hsorted := Finset.sortedLT_sort α
  have hset := Finset.sort_toFinset (s := α) (r := (· ≤ ·))
  generalize α.sort (· ≤ ·) = l at hlen hsorted hset
  match l, hlen with
  | [a, b, c, d], _ =>
    rw [List.sortedLT_iff_pairwise] at hsorted
    simp only [List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq, List.Pairwise.nil, and_true] at hsorted
    refine ⟨(a, b, c, d), ?_, rfl, hset.symm⟩
    simp only [quads, List.mem_filter, List.mem_flatMap, List.mem_map, List.mem_finRange,
      true_and, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨⟨a, b, c, d, rfl⟩, ⟨hsorted.1.1, hsorted.2.1.1⟩, hsorted.2.2.1⟩

theorem memAtL_eq {α : Finset (Fin n)} {q : Fin n × Fin n × Fin n × Fin n}
    (h : α.sort (· ≤ ·) = [q.1, q.2.1, q.2.2.1, q.2.2.2]) (b : Bool) : memAtL α b = memQ q b := by
  unfold memAtL
  rw [h]
  rfl

theorem adjB_iff (q q' : Fin n × Fin n × Fin n × Fin n) :
    adjB q q' = true ↔ ∃ b ∈ [true, false], ∃ b' ∈ [true, false], ∃ k ∈ memQ q b,
      ∃ k' ∈ memQ q' b', ord5Pi (k * k') = true := by
  simp only [adjB, List.any_eq_true, ord5G_eq]

theorem adjCheck_of (h : adjCheckL n = true) : adjCheck n () = true := by
  refine decide_eq_true fun α hα α' hα' => ?_
  obtain ⟨q, hq, hs, rfl⟩ := exists_quad hα
  obtain ⟨q', hq', hs', rfl⟩ := exists_quad hα'
  have h1 := List.all_eq_true.1 (List.all_eq_true.1 h q hq) q' hq'
  simp only [memAtL_eq hs, memAtL_eq hs', ← adjB_iff]
  rw [beq_iff_eq] at h1
  rw [← h1, decide_eq_true_iff]

end Certificates.Kernel.AE117Adj
