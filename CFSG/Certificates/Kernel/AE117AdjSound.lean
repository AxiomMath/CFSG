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

theorem ord5Pi_of_perm_one {x : Wr n} (h : x.perm = 1) : ord5Pi x = false := by
  have hx : x * x = 1 := by
    refine Wr.ext (funext fun i => ?_) ?_
    · rw [mul_vec, h]
      exact zmod_two_add_self (x.vec i)
    · rw [mul_perm, h, mul_one]
      rfl
  have h5 : x ^ 5 = x := by
    rw [pow_succ, pow_mul' x 2 2, sq x, hx, one_pow, one_mul]
  unfold ord5Pi
  rw [h5]
  cases inPi x <;> rfl

theorem perm_mem_dQ {q : Fin n × Fin n × Fin n × Fin n} {b : Bool} {k : Wr n}
    (hk : k ∈ memQ q b) : k.perm = 1 ∨ k.perm ∈ dQ q := by
  obtain ⟨a, b₁, c, d⟩ := q
  cases b <;>
  · simp only [memQ, memLC, Bool.false_eq_true, ↓reduceIte, List.mem_cons, List.not_mem_nil,
      or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [dQ, dT, dP, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil,
        true_or, or_true]

theorem pow5_apply (σ : Equiv.Perm (Fin n)) (i : Fin n) : (σ ^ 5) i = σ (σ (σ (σ (σ i)))) := by
  simp only [pow_succ, pow_zero, one_mul, Equiv.Perm.mul_apply]

theorem dP_apply (t : Fin n × Fin n × Fin n × Fin n) (i : Fin n) : dP t i = dF t i := by
  simp only [dP, dF, sw, Equiv.Perm.mul_apply, Equiv.swap_apply_def]
  congr

theorem ne_one_of_moves5F {σ : Equiv.Perm (Fin n)} {f : Fin n → Fin n} (hf : ∀ i, σ i = f i)
    (h : moves5F f = true) : σ ^ 5 ≠ 1 := by
  intro h5
  obtain ⟨i, -, hi⟩ := List.any_eq_true.1 h
  have h1 : (σ ^ 5) i = i := by rw [h5, Equiv.Perm.one_apply]
  simp only [pow5_apply, hf] at h1
  rw [bne_iff_ne] at hi
  exact hi h1

theorem vec_pow5 (x : Wr n) (i : Fin n) : (x ^ 5).vec i = vec5 x i := by
  simp only [pow_succ, pow_zero, one_mul, mul_vec, mul_perm, Equiv.Perm.mul_def,
    Equiv.symm_trans_apply, vec5]

theorem ord5G_of_fast {x : Wr n} (h : ord5Fast x = true) : ord5G x = true := by
  simp only [ord5Fast, Bool.and_eq_true, Bool.or_eq_true, List.any_eq_true, List.all_eq_true,
    beq_iff_eq, bne_iff_ne, ne_eq] at h
  obtain ⟨⟨⟨i, -, hi⟩, h5⟩, hv⟩ := h
  have hp5 : x.perm ^ 5 = 1 :=
    Equiv.ext fun j => by
      rw [pow5_apply, h5 j (List.mem_finRange j)]
      rfl
  have hne : x.perm ≠ 1 := fun h1 => hi (by rw [h1]; rfl)
  have hx1 : x ≠ 1 := fun h1 => hne (by rw [h1]; rfl)
  have hxA : x ≠ allOnes n := fun h1 => hne (by rw [h1]; rfl)
  have hpp : (x ^ 5).perm = 1 := by rw [perm_pow, hp5]
  unfold ord5G ord5Pi inPi
  rcases hv with hv | hv
  · have h1 : x ^ 5 = 1 := Wr.ext (funext fun j => by rw [vec_pow5, hv j (List.mem_finRange j)]; rfl) hpp
    simp [hp5, hx1, hxA, h1]
  · have h1 : x ^ 5 = allOnes n :=
      Wr.ext (funext fun j => by rw [vec_pow5, hv j (List.mem_finRange j)]; rfl) hpp
    simp [hp5, hx1, hxA, h1]

theorem wit2_mem (q : Fin n × Fin n × Fin n × Fin n) : wit2 q ∈ memQ q true :=
  List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)

theorem wit4_mem (q : Fin n × Fin n × Fin n × Fin n) : wit4 q ∈ memQ q true :=
  List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
    (List.mem_cons_of_mem _ List.mem_cons_self)))

theorem adjPairW_sound {q q' : Fin n × Fin n × Fin n × Fin n} (hd : dOK q = true)
    (hd' : dOK q' = true) (h : adjPairW q q' = true) :
    (decide ((qset q ∩ qset q').card = 3) == adjB q q') = true := by
  unfold adjPairW at h
  cases hc : decide ((qset q ∩ qset q').card = 3)
  · rw [hc, Bool.cond_false] at h
    have hB : adjB q q' = false := by
      rw [Bool.eq_false_iff]
      intro hb
      simp only [adjB, List.any_eq_true] at hb
      obtain ⟨b, -, b', -, k, hk, k', hk', ho⟩ := hb
      unfold ord5G at ho
      rw [Bool.and_eq_true, decide_eq_true_iff, mul_perm] at ho
      have hp : k.perm * k'.perm = 1 := by
        rcases perm_mem_dQ hk with h1 | h1 <;> rcases perm_mem_dQ hk' with h2 | h2
        · rw [h1, h2, mul_one]
        · obtain ⟨t', ht', e'⟩ := List.mem_map.1 h2
          rw [h1, one_mul] at ho
          exact absurd ho.1 (ne_one_of_moves5F (fun i => by rw [← e', dP_apply])
            (List.all_eq_true.1 hd' _ ht'))
        · obtain ⟨t, ht, e⟩ := List.mem_map.1 h1
          rw [h2, mul_one] at ho
          exact absurd ho.1 (ne_one_of_moves5F (fun i => by rw [← e, dP_apply])
            (List.all_eq_true.1 hd _ ht))
        · obtain ⟨t, ht, e⟩ := List.mem_map.1 h1
          obtain ⟨t', ht', e'⟩ := List.mem_map.1 h2
          have h3 := List.all_eq_true.1 (List.all_eq_true.1 h _ ht) _ ht'
          rw [Bool.or_eq_true] at h3
          rcases h3 with h3 | h3
          · exact absurd ho.1 (ne_one_of_moves5F
              (fun i => by rw [Equiv.Perm.mul_apply, ← e, ← e', dP_apply, dP_apply]) h3)
          · rw [← e, ← e']
            exact of_decide_eq_true h3
      rw [ord5Pi_of_perm_one (by rw [mul_perm]; exact hp)] at ho
      exact Bool.false_ne_true ho.2
    rw [hB]
    rfl
  · rw [hc, Bool.cond_true, Bool.or_eq_true] at h
    have hB : adjB q q' = true := by
      simp only [adjB, List.any_eq_true]
      refine ⟨true, List.mem_cons_self, true, List.mem_cons_self, wit2 q, wit2_mem q, ?_⟩
      rcases h with h | h
      · exact ⟨wit4 q', wit4_mem q', ord5G_of_fast h⟩
      · exact ⟨wit2 q', wit2_mem q', ord5G_of_fast h⟩
    rw [hB]
    rfl

theorem adjCheckL_of_W (h : adjCheckLW n = true) : adjCheckL n = true := by
  unfold adjCheckLW at h
  rw [Bool.and_eq_true] at h
  unfold adjCheckL adjCheckOn
  refine List.all_eq_true.2 fun q hq => List.all_eq_true.2 fun q' hq' => ?_
  exact adjPairW_sound (List.all_eq_true.1 h.1 q hq) (List.all_eq_true.1 h.1 q' hq')
    (List.all_eq_true.1 (List.all_eq_true.1 h.2 q hq) q' hq')

end Certificates.Kernel.AE117Adj
