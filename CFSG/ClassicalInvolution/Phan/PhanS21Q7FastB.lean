module

public import CFSG.ClassicalInvolution.Phan.PhanS19Q7Inputs

public section

namespace CFSG.ClassicalInvolution.PhanB3.S.Std.Q7

section Walks

variable {α : Type} (adj : α → α → Bool)

inductive Wk (P : α → Prop) : Nat → α → α → Prop
  | nil (x : α) : Wk P 0 x x
  | cons {n : Nat} {x v y : α} : adj x v = true → P v → Wk P n v y → Wk P (n + 1) x y

variable {adj} {P Q : α → Prop}

theorem Wk.trans {n m : Nat} {x y z : α} (h : Wk adj P n x y) (h' : Wk adj P m y z) :
    Wk adj P (n + m) x z := by
  induction h with
  | nil => simpa using h'
  | cons hadj hv _ ih =>
    rw [Nat.add_right_comm]
    exact Wk.cons hadj hv (ih h')

theorem Wk.single {x y : α} (h : adj x y = true) (hy : P y) : Wk adj P 1 x y :=
  Wk.cons h hy (Wk.nil y)

theorem Wk.snoc {n : Nat} {x y z : α} (w : Wk adj P n x y) (h : adj y z = true) (hz : P z) :
    Wk adj P (n + 1) x z :=
  w.trans (Wk.single h hz)

theorem Wk.mono {n : Nat} {x y : α} (hPQ : ∀ v, P v → Q v) (w : Wk adj P n x y) :
    Wk adj Q n x y := by
  induction w with
  | nil => exact Wk.nil _
  | cons h hv _ ih => exact Wk.cons h (hPQ _ hv) ih

theorem Wk.symm (hs : ∀ a b, adj a b = true → adj b a = true) {n : Nat} {x y : α}
    (w : Wk adj P n x y) (hx : P x) : Wk adj P n y x := by
  induction w with
  | nil => exact Wk.nil _
  | cons h hv _ ih => exact (ih hv).snoc (hs _ _ h) hx

theorem Wk.avoid_aux (x : α) : ∀ n : Nat,
    (∀ u, Wk adj P n x u → u ≠ x →
      ∃ k, 1 ≤ k ∧ k ≤ n ∧ Wk adj (fun v => P v ∧ v ≠ x) k x u) ∧
    (∀ v u, Wk adj P n v u → v ≠ x → u ≠ x →
      Wk adj (fun w => P w ∧ w ≠ x) n v u ∨
        ∃ k, 1 ≤ k ∧ k ≤ n ∧ Wk adj (fun w => P w ∧ w ≠ x) k x u) := by
  intro n
  induction n with
  | zero =>
    refine ⟨?_, ?_⟩
    · intro u w hu
      cases w
      exact absurd rfl hu
    · intro v u w _ _
      cases w
      exact Or.inl (Wk.nil _)
  | succ n ih =>
    obtain ⟨ihS, ihU⟩ := ih
    refine ⟨?_, ?_⟩
    · intro u w hu
      rcases w with _ | ⟨hadj, hv, w'⟩
      rename_i v
      by_cases hvx : v = x
      · subst hvx
        obtain ⟨k, hk1, hkn, hw⟩ := ihS u w' hu
        exact ⟨k, hk1, by omega, hw⟩
      · rcases ihU v u w' hvx hu with h | ⟨k, hk1, hkn, hw⟩
        · exact ⟨n + 1, by omega, Nat.le_refl _, Wk.cons hadj ⟨hv, hvx⟩ h⟩
        · exact ⟨k, hk1, by omega, hw⟩
    · intro v u w hv hu
      rcases w with _ | ⟨hadj, hw0, w'⟩
      rename_i w0
      by_cases hwx : w0 = x
      · subst hwx
        obtain ⟨k, hk1, hkn, hw⟩ := ihS u w' hu
        exact Or.inr ⟨k, hk1, by omega, hw⟩
      · rcases ihU w0 u w' hwx hu with h | ⟨k, hk1, hkn, hw⟩
        · exact Or.inl (Wk.cons hadj ⟨hw0, hwx⟩ h)
        · exact Or.inr ⟨k, hk1, by omega, hw⟩

theorem Wk.avoid {n : Nat} {x u : α} (w : Wk adj P n x u) (hu : u ≠ x) :
    ∃ k, 1 ≤ k ∧ k ≤ n ∧ Wk adj (fun v => P v ∧ v ≠ x) k x u :=
  (Wk.avoid_aux x n).1 u w hu

end Walks

section Bfs

variable {α : Type} (adj : α → α → Bool)

theorem mem_partition_fst {p : α → Bool} {R : List α} {u : α} :
    u ∈ (R.partition p).1 ↔ u ∈ R ∧ p u = true := by
  rw [List.partition_eq_filter_filter, List.mem_filter]

theorem mem_partition_snd {p : α → Bool} {R : List α} {u : α} :
    u ∈ (R.partition p).2 ↔ u ∈ R ∧ p u = false := by
  rw [List.partition_eq_filter_filter, List.mem_filter]
  simp

theorem walk_restart (R : List α) (p : α → Bool) : ∀ k : Nat,
    (∀ v u, Wk adj (· ∈ R) k v u → v ∈ R → p v = true → u ∈ R → p u = false →
      ∃ f, (f ∈ R ∧ p f = true) ∧ ∃ k', 1 ≤ k' ∧ k' ≤ k ∧
        Wk adj (fun w => w ∈ R ∧ p w = false) k' f u) ∧
    (∀ w u, Wk adj (· ∈ R) k w u → p w = false → u ∈ R → p u = false →
      Wk adj (fun w => w ∈ R ∧ p w = false) k w u ∨
        ∃ f, (f ∈ R ∧ p f = true) ∧ ∃ k', 1 ≤ k' ∧ k' ≤ k ∧
          Wk adj (fun w => w ∈ R ∧ p w = false) k' f u) := by
  intro k
  induction k with
  | zero =>
    refine ⟨?_, ?_⟩
    · intro v u w _ hpv _ hpu
      cases w
      rw [hpv] at hpu
      exact absurd hpu (by decide)
    · intro w u wk _ _ _
      cases wk
      exact Or.inl (Wk.nil _)
  | succ k ih =>
    obtain ⟨ihT, ihV⟩ := ih
    refine ⟨?_, ?_⟩
    · intro v u wk hvR hpv huR hpu
      rcases wk with _ | ⟨hadj, hw, wk'⟩
      rename_i w
      cases hpw : p w
      · rcases ihV w u wk' hpw huR hpu with h | ⟨f, hf, k', hk1, hk', hw'⟩
        · exact ⟨v, ⟨hvR, hpv⟩, k + 1, by omega, Nat.le_refl _,
            Wk.cons hadj ⟨hw, hpw⟩ h⟩
        · exact ⟨f, hf, k', hk1, by omega, hw'⟩
      · obtain ⟨f, hf, k', hk1, hk', hw'⟩ := ihT w u wk' hw hpw huR hpu
        exact ⟨f, hf, k', hk1, by omega, hw'⟩
    · intro w u wk hpw huR hpu
      rcases wk with _ | ⟨hadj, hw', wk'⟩
      rename_i w'
      cases hpw' : p w'
      · rcases ihV w' u wk' hpw' huR hpu with h | ⟨f, hf, k', hk1, hk', hw''⟩
        · exact Or.inl (Wk.cons hadj ⟨hw', hpw'⟩ h)
        · exact Or.inr ⟨f, hf, k', hk1, by omega, hw''⟩
      · obtain ⟨f, hf, k', hk1, hk', hw''⟩ := ihT w' u wk' hw' hpw' huR hpu
        exact Or.inr ⟨f, hf, k', hk1, by omega, hw''⟩

theorem bfsAux_complete : ∀ (n : Nat) (F R : List α),
    (∀ u ∈ R, ∃ f ∈ F, ∃ k, 1 ≤ k ∧ k ≤ n ∧ Wk adj (· ∈ R) k f u) → bfsAux adj n F R = true := by
  intro n
  induction n with
  | zero =>
    intro F R h
    rcases R with _ | ⟨u, R'⟩
    · rfl
    · obtain ⟨f, _, k, hk1, hk0, _⟩ := h u List.mem_cons_self
      omega
  | succ n ih =>
    intro F R h
    by_cases hR : R = []
    · subst hR
      rfl
    · simp only [bfsAux, Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_iff]
      refine Or.inr ⟨?_, ?_⟩
      · rw [Bool.eq_false_iff]
        intro hne0
        have hne := List.isEmpty_iff.1 hne0
        obtain ⟨u, hu⟩ := List.exists_mem_of_ne_nil R hR
        obtain ⟨f, hf, k, hk1, hkn, wk⟩ := h u hu
        rcases wk with _ | ⟨hadj, hv, wk'⟩
        · omega
        · rename_i v
          have hv1 : v ∈ (R.partition fun u => F.any fun f => adj f u).1 :=
            mem_partition_fst.2 ⟨hv, List.any_eq_true.2 ⟨f, hf, hadj⟩⟩
          rw [hne] at hv1
          exact List.not_mem_nil hv1
      · apply ih
        intro u hu
        obtain ⟨huR, hpu⟩ := mem_partition_snd.1 hu
        obtain ⟨f, hf, k, hk1, hkn, wk⟩ := h u huR
        rcases wk with _ | ⟨hadj, hv, wk'⟩
        · omega
        · rename_i v
          have hpv : (F.any fun f => adj f v) = true := List.any_eq_true.2 ⟨f, hf, hadj⟩
          obtain ⟨f', hf', k', hk1', hk', hw⟩ :=
            (walk_restart adj R (fun u => F.any fun f => adj f u) _).1 v u wk' hv hpv huR hpu
          refine ⟨f', mem_partition_fst.2 hf', k', hk1', by omega, hw.mono ?_⟩
          intro w hw
          exact mem_partition_snd.2 hw

theorem bfsOk_of_walks {r : α} {rest : List α} (hnd : r ∉ rest)
    (h : ∀ u ∈ rest, ∃ n, n ≤ 12 ∧ Wk adj (· ∈ r :: rest) n r u) :
    bfsOk adj (r :: rest) = true := by
  show bfsAux adj 12 [r] rest = true
  apply bfsAux_complete
  intro u hu
  obtain ⟨n, hn, w⟩ := h u hu
  have hur : u ≠ r := fun e => hnd (e ▸ hu)
  obtain ⟨k, hk1, hkn, w'⟩ := w.avoid hur
  refine ⟨r, List.mem_singleton_self _, k, hk1, by omega, w'.mono ?_⟩
  intro v ⟨hv, hvr⟩
  rcases List.mem_cons.1 hv with e | hv'
  · exact absurd e hvr
  · exact hv'

end Bfs

end CFSG.ClassicalInvolution.PhanB3.S.Std.Q7
