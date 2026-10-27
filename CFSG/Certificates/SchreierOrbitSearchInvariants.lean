module

public import CFSG.Certificates.SchreierChainData
public import Mathlib.Data.Fintype.Card

public section

namespace CFSG.Certificates.SchreierOrbitState

@[expose] def keys {n : ℕ} (q : SchreierOrbitState n) : List (Fin n) :=
  q.entries.map Prod.fst

theorem mem_points_iff_mem_keys {n : ℕ} (q : SchreierOrbitState n) (x : Fin n) :
    x ∈ q.points ↔ x ∈ q.keys := by
  simp only [points, Set.mem_ofPred_eq, transversal?, List.lookup_isSome_iff,
    beq_iff_eq, keys, List.mem_map]
  exact ⟨fun ⟨p, hp, hx⟩ => ⟨p, hp, hx.symm⟩,
    fun ⟨p, hp, hx⟩ => ⟨p, hp, hx.symm⟩⟩

theorem mem_entries_of_transversal {n : ℕ} (q : SchreierOrbitState n)
    (x : Fin n) (t : Equiv.Perm (Fin n)) (ht : q.transversal? x = some t) :
    (x, t) ∈ q.entries := by
  obtain ⟨before, after, heq, _⟩ := List.lookup_eq_some_iff.1 ht
  simp [heq]

theorem discover_mem_points {n : ℕ} (q : SchreierOrbitState n) (x : Fin n)
    (t : Equiv.Perm (Fin n)) : x ∈ (q.discover x t).points := by
  cases hx : q.transversal? x with
  | none =>
    change ((q.discover x t).transversal? x).isSome = true
    rw [discover_assigns_transversal q x t hx]
    rfl
  | some u =>
    rw [discover_of_assigned q x t (by simp [hx])]
    change (q.transversal? x).isSome = true
    simp [hx]

theorem discover_preserves_points {n : ℕ} (q : SchreierOrbitState n)
    (x y : Fin n) (t : Equiv.Perm (Fin n)) (hx : x ∈ q.points) :
    x ∈ (q.discover y t).points := by
  obtain ⟨u, hu⟩ := Option.isSome_iff_exists.1 hx
  change ((q.discover y t).transversal? x).isSome = true
  rw [discover_preserves_transversal q x y u t hu]
  rfl

structure SearchInvariant {n : ℕ} (steps : List (Equiv.Perm (Fin n)))
    (H : Subgroup (Equiv.Perm (Fin n))) (b : Fin n)
    (processed : List (Fin n)) (q : SchreierOrbitState n) : Prop where
  keys_nodup : q.keys.Nodup
  pending_suffix : q.keys = processed ++ q.queue
  processed_closed : ∀ x ∈ processed, ∀ s ∈ steps, s x ∈ q.points
  entries_sound : ∀ p ∈ q.entries, p.2 ∈ H ∧ p.2 b = p.1

theorem initial_invariant {n : ℕ} (steps : List (Equiv.Perm (Fin n)))
    (H : Subgroup (Equiv.Perm (Fin n))) (b : Fin n) :
    SearchInvariant steps H b [] (initial b) := by
  refine ⟨by simp [keys, initial], by simp [keys, initial], ?_, ?_⟩
  · simp
  · intro p hp
    have hp' : p = (b, 1) := by simpa [initial] using hp
    subst p
    exact ⟨H.one_mem, rfl⟩

theorem discover_invariant {n : ℕ} (steps : List (Equiv.Perm (Fin n)))
    (H : Subgroup (Equiv.Perm (Fin n))) (b : Fin n)
    (processed : List (Fin n)) (q : SchreierOrbitState n)
    (hq : SearchInvariant steps H b processed q) (y : Fin n)
    (t : Equiv.Perm (Fin n)) (htH : t ∈ H) (htb : t b = y) :
    SearchInvariant steps H b processed (q.discover y t) := by
  cases hy : q.transversal? y with
  | some u =>
    rw [discover_of_assigned q y t (by simp [hy])]
    exact hq
  | none =>
    have hykey : y ∉ q.keys := by
      intro hyk
      have hsome := (mem_points_iff_mem_keys q y).2 hyk
      change (q.transversal? y).isSome = true at hsome
      simp [hy] at hsome
    rw [discover_of_unassigned q y t hy]
    refine ⟨?_, ?_, ?_, ?_⟩
    · have hnew : (q.keys ++ [y]).Nodup := by
        apply List.nodup_append.2
        refine ⟨hq.keys_nodup, by simp, ?_⟩
        intro a ha c hc
        have hc' : c = y := by simpa using hc
        subst c
        intro hay
        exact hykey (hay ▸ ha)
      simpa only [keys, List.map_append, List.map_cons, List.map_nil] using hnew
    · simpa [keys, List.map_append, List.append_assoc] using
        congrArg (fun l => l ++ [y]) hq.pending_suffix
    · intro x hx s hs
      have hxq := hq.processed_closed x hx s hs
      have hxnew := discover_preserves_points q (s x) y t hxq
      simpa [discover_of_unassigned q y t hy] using hxnew
    · intro p hp
      have hp' : p ∈ q.entries ∨ p = (y, t) := by simpa using hp
      rcases hp' with hp' | rfl
      · exact hq.entries_sound p hp'
      · exact ⟨htH, htb⟩

theorem discoveries_invariant {n : ℕ} (steps todo : List (Equiv.Perm (Fin n)))
    (H : Subgroup (Equiv.Perm (Fin n))) (b : Fin n)
    (processed : List (Fin n)) (q : SchreierOrbitState n)
    (hq : SearchInvariant steps H b processed q) (x : Fin n)
    (tx : Equiv.Perm (Fin n)) (htH : tx ∈ H) (htb : tx b = x)
    (hsteps : ∀ s ∈ todo, s ∈ H) :
    SearchInvariant steps H b processed
      (todo.foldl (fun state s => state.discover (s x) (s * tx)) q) := by
  induction todo generalizing q with
  | nil => exact hq
  | cons s todo ih =>
    apply ih
    · exact discover_invariant steps H b processed q hq (s x) (s * tx)
        (H.mul_mem (hsteps s (by simp)) htH) (by simp [Equiv.Perm.mul_apply, htb])
    · intro u hu
      exact hsteps u (by simp [hu])

theorem discoveries_preserve_points {n : ℕ} (steps : List (Equiv.Perm (Fin n)))
    (q : SchreierOrbitState n) (x y : Fin n) (tx : Equiv.Perm (Fin n))
    (hy : y ∈ q.points) :
    y ∈ (steps.foldl (fun state s => state.discover (s x) (s * tx)) q).points := by
  induction steps generalizing q with
  | nil => exact hy
  | cons s steps ih =>
    exact ih (q.discover (s x) (s * tx)) (discover_preserves_points q y (s x) (s * tx) hy)

theorem discoveries_step_images {n : ℕ} (steps : List (Equiv.Perm (Fin n)))
    (q : SchreierOrbitState n) (x : Fin n) (tx : Equiv.Perm (Fin n)) :
    ∀ s ∈ steps,
      s x ∈ (steps.foldl (fun state u => state.discover (u x) (u * tx)) q).points := by
  induction steps generalizing q with
  | nil => simp
  | cons s steps ih =>
    intro u hu
    rcases List.mem_cons.1 hu with hu | hu
    · subst u
      exact discoveries_preserve_points steps (q.discover (s x) (s * tx)) x (s x) tx
        (discover_mem_points q (s x) (s * tx))
    · exact ih (q.discover (s x) (s * tx)) u hu

theorem step_invariant_nonempty {n : ℕ} (steps : List (Equiv.Perm (Fin n)))
    (H : Subgroup (Equiv.Perm (Fin n))) (b : Fin n)
    (processed : List (Fin n)) (q : SchreierOrbitState n)
    (hq : SearchInvariant steps H b processed q)
    (hsteps : ∀ s ∈ steps, s ∈ H) (x : Fin n) (pending : List (Fin n))
    (hqueue : q.queue = x :: pending) :
    SearchInvariant steps H b (processed ++ [x]) (step steps q) := by
  have hxkey : x ∈ q.keys := by
    rw [hq.pending_suffix, hqueue]
    simp
  obtain ⟨tx, htx⟩ := Option.isSome_iff_exists.1
    ((mem_points_iff_mem_keys q x).2 hxkey)
  have hsound := hq.entries_sound (x, tx) (mem_entries_of_transversal q x tx htx)
  let popped : SchreierOrbitState n := ⟨q.entries, pending⟩
  have hpop : SearchInvariant [] H b (processed ++ [x]) popped := by
    refine ⟨hq.keys_nodup, ?_, by simp, hq.entries_sound⟩
    simpa [popped, keys, hqueue, List.append_assoc] using hq.pending_suffix
  have hout := discoveries_invariant [] steps H b (processed ++ [x]) popped
    hpop x tx hsound.1 hsound.2 hsteps
  simp only [step, hqueue, htx, Option.getD_some]
  refine ⟨hout.keys_nodup, hout.pending_suffix, ?_, hout.entries_sound⟩
  intro y hy s hs
  rcases List.mem_append.1 hy with hy | hy
  · exact discoveries_preserve_points steps popped x (s y) tx
      (hq.processed_closed y hy s hs)
  · have hy' : y = x := by simpa using hy
    subst y
    exact discoveries_step_images steps popped x tx s hs

theorem run_of_queue_empty {n : ℕ} (steps : List (Equiv.Perm (Fin n)))
    (fuel : ℕ) (q : SchreierOrbitState n) (hq : q.queue = []) :
    run steps fuel q = q := by
  induction fuel with
  | zero => rfl
  | succ fuel ih =>
    rw [run_succ, step_of_queue_empty steps q hq]
    exact ih

theorem run_append_iterations {n : ℕ} (steps : List (Equiv.Perm (Fin n)))
    (fuel extra : ℕ) (q : SchreierOrbitState n) :
    run steps (fuel + extra) q = run steps extra (run steps fuel q) := by
  induction fuel generalizing q with
  | zero => simp only [Nat.zero_add, run_zero]
  | succ fuel ih => simpa only [Nat.succ_add, run_succ] using ih (step steps q)

theorem run_preserves_intermediate_transversal {n : ℕ}
    (steps : List (Equiv.Perm (Fin n))) (fuel extra : ℕ) (q : SchreierOrbitState n)
    (x : Fin n) (t : Equiv.Perm (Fin n))
    (ht : (run steps fuel q).transversal? x = some t) :
    (run steps (fuel + extra) q).transversal? x = some t := by
  rw [run_append_iterations]
  exact run_preserves_transversal steps extra (run steps fuel q) x t ht

theorem run_invariant {n : ℕ} (steps : List (Equiv.Perm (Fin n)))
    (H : Subgroup (Equiv.Perm (Fin n))) (b : Fin n)
    (hsteps : ∀ s ∈ steps, s ∈ H) (fuel : ℕ)
    (processed : List (Fin n)) (q : SchreierOrbitState n)
    (hq : SearchInvariant steps H b processed q) :
    ∃ processed', SearchInvariant steps H b processed' (run steps fuel q) ∧
      ((run steps fuel q).queue ≠ [] → processed.length + fuel = processed'.length) := by
  induction fuel generalizing processed q with
  | zero => exact ⟨processed, hq, by simp⟩
  | succ fuel ih =>
    cases hqueue : q.queue with
    | nil =>
      rw [run_of_queue_empty steps (fuel + 1) q hqueue]
      exact ⟨processed, hq, by simp [hqueue]⟩
    | cons x pending =>
      obtain ⟨processed', hfinal, hlength⟩ := ih (processed ++ [x]) (step steps q)
        (step_invariant_nonempty steps H b processed q hq hsteps x pending hqueue)
      refine ⟨processed', hfinal, ?_⟩
      intro hne
      have hlen := hlength hne
      simp only [List.length_append, List.length_singleton] at hlen
      omega

theorem run_initial_queue_empty {n : ℕ} (steps : List (Equiv.Perm (Fin n)))
    (b : Fin n) : (run steps n (initial b)).queue = [] := by
  obtain ⟨processed, hfinal, hlength⟩ := run_invariant steps ⊤ b
    (by simp) n [] (initial b) (initial_invariant steps ⊤ b)
  by_contra hne
  have hlen : n = processed.length := by simpa using hlength hne
  have hbound : (run steps n (initial b)).keys.length ≤ n := by
    simpa using hfinal.keys_nodup.length_le_card
  have hsplit := congrArg List.length hfinal.pending_suffix
  have hpos := List.length_pos_iff.2 hne
  simp only [List.length_append] at hsplit
  omega

theorem run_initial_keys_nodup {n : ℕ} (steps : List (Equiv.Perm (Fin n)))
    (fuel : ℕ) (b : Fin n) : (run steps fuel (initial b)).keys.Nodup := by
  obtain ⟨processed, hfinal, _⟩ := run_invariant steps ⊤ b
    (by simp) fuel [] (initial b) (initial_invariant steps ⊤ b)
  exact hfinal.keys_nodup

theorem run_initial_queue_nodup {n : ℕ} (steps : List (Equiv.Perm (Fin n)))
    (fuel : ℕ) (b : Fin n) : (run steps fuel (initial b)).queue.Nodup := by
  obtain ⟨processed, hfinal, _⟩ := run_invariant steps ⊤ b
    (by simp) fuel [] (initial b) (initial_invariant steps ⊤ b)
  have hnodup := hfinal.keys_nodup
  rw [hfinal.pending_suffix] at hnodup
  exact hnodup.of_append_right

theorem run_initial_closed {n : ℕ} (steps : List (Equiv.Perm (Fin n)))
    (b : Fin n) (x : Fin n) (hx : x ∈ (run steps n (initial b)).points)
    (s : Equiv.Perm (Fin n)) (hs : s ∈ steps) :
    s x ∈ (run steps n (initial b)).points := by
  obtain ⟨processed, hfinal, _⟩ := run_invariant steps ⊤ b
    (by simp) n [] (initial b) (initial_invariant steps ⊤ b)
  have hxkey := (mem_points_iff_mem_keys _ x).1 hx
  rw [hfinal.pending_suffix, run_initial_queue_empty steps b, List.append_nil] at hxkey
  exact hfinal.processed_closed x hxkey s hs

theorem run_initial_transversal_sound {n : ℕ} (steps : List (Equiv.Perm (Fin n)))
    (H : Subgroup (Equiv.Perm (Fin n))) (b : Fin n)
    (hsteps : ∀ s ∈ steps, s ∈ H) (fuel : ℕ) (x : Fin n)
    (t : Equiv.Perm (Fin n)) (ht : (run steps fuel (initial b)).transversal? x = some t) :
    t ∈ H ∧ t b = x := by
  obtain ⟨processed, hfinal, _⟩ := run_invariant steps H b hsteps
    fuel [] (initial b) (initial_invariant steps H b)
  exact hfinal.entries_sound (x, t) (mem_entries_of_transversal _ x t ht)

end CFSG.Certificates.SchreierOrbitState
