module

public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Data.Matrix.Basic

public section

namespace CFSG.LieType.TitsSimplicity

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

@[expose] def IsIndecomposable (A : Matrix ι ι ℤ) : Prop :=
  ¬ ∃ I J : Finset ι, I.Nonempty ∧ J.Nonempty ∧ Disjoint I J ∧ I ∪ J = Finset.univ ∧
    ∀ i ∈ I, ∀ j ∈ J, A i j = 0

theorem isIndecomposable_iff {A : Matrix ι ι ℤ} :
    IsIndecomposable A ↔
      ∀ S : Finset ι, (∀ i ∈ S, ∀ j ∉ S, A i j = 0) → S = ∅ ∨ S = Finset.univ := by
  constructor
  · intro h S hS
    by_contra hne
    rw [not_or] at hne
    refine h ⟨S, Sᶜ, Finset.nonempty_iff_ne_empty.2 hne.1, ?_, disjoint_compl_right,
      Finset.union_compl S, fun i hi j hj => hS i hi j (Finset.mem_compl.1 hj)⟩
    rw [Finset.nonempty_iff_ne_empty, Ne, Finset.compl_eq_empty_iff]
    exact hne.2
  · rintro h ⟨I, J, hI, hJ, hIJ, hU, h0⟩
    have hJI : ∀ j, j ∈ J ↔ j ∉ I := fun j =>
      ⟨fun hj hi => Finset.disjoint_left.1 hIJ hi hj, fun hi => by
        have := Finset.mem_univ j
        rw [← hU, Finset.mem_union] at this
        exact this.resolve_left hi⟩
    rcases h I fun i hi j hj => h0 i hi j ((hJI j).2 hj) with rfl | rfl
    · exact Finset.not_nonempty_empty hI
    · obtain ⟨j, hj⟩ := hJ
      exact (hJI j).1 hj (Finset.mem_univ j)

instance (A : Matrix ι ι ℤ) : Decidable (IsIndecomposable A) :=
  have : DecidablePred fun S : Finset ι =>
      (∀ i ∈ S, ∀ j ∉ S, A i j = 0) → S = ∅ ∨ S = Finset.univ := fun S =>
    have : DecidablePred fun i => ∀ j ∉ S, A i j = 0 := fun _ => inferInstance
    inferInstance
  decidable_of_iff _ isIndecomposable_iff.symm

@[expose] def dynkinGraph (A : Matrix ι ι ℤ) : SimpleGraph ι where
  Adj i j := i ≠ j ∧ A i j ≠ 0 ∧ A j i ≠ 0
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.2, h.2.1⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

theorem isIndecomposable_of_connected {A : Matrix ι ι ℤ} (h : (dynkinGraph A).Connected) :
    IsIndecomposable A := by
  rintro ⟨I, J, ⟨i, hi⟩, ⟨j, hj⟩, hIJ, hU, h0⟩
  obtain ⟨p⟩ := h.preconnected i j
  obtain ⟨d, -, hd1, hd2⟩ := p.exists_boundary_dart (I : Set ι) hi
    fun hjI => Finset.disjoint_left.1 hIJ hjI hj
  have hd2' : d.snd ∈ J := by
    have := Finset.mem_univ d.snd
    rw [← hU, Finset.mem_union] at this
    exact this.resolve_left hd2
  exact d.adj.2.1 (h0 _ hd1 _ hd2')

theorem connected_of_isIndecomposable [Nonempty ι] {A : Matrix ι ι ℤ}
    (hA : ∀ i j, A i j = 0 → A j i = 0) (h : IsIndecomposable A) : (dynkinGraph A).Connected := by
  classical
  obtain ⟨i₀⟩ := ‹Nonempty ι›
  let S : Finset ι := Finset.univ.filter fun j => (dynkinGraph A).Reachable i₀ j
  have hS : ∀ i ∈ S, ∀ j ∉ S, A i j = 0 := by
    intro i hi j hj
    by_contra hne
    apply hj
    refine Finset.mem_filter.2 ⟨Finset.mem_univ _, (Finset.mem_filter.1 hi).2.trans
      (SimpleGraph.Adj.reachable ⟨?_, hne, fun h' => hne (hA _ _ h')⟩)⟩
    rintro rfl
    exact hj hi
  have hall : ∀ j, (dynkinGraph A).Reachable i₀ j := by
    rcases isIndecomposable_iff.1 h S hS with h' | h'
    · have : i₀ ∈ S := Finset.mem_filter.2 ⟨Finset.mem_univ _, SimpleGraph.Reachable.refl _⟩
      rw [h'] at this
      exact absurd this (Finset.notMem_empty _)
    · intro j
      have : j ∈ S := h' ▸ Finset.mem_univ j
      exact (Finset.mem_filter.1 this).2
  exact (SimpleGraph.connected_iff_exists_forall_reachable _).2 ⟨i₀, hall⟩

theorem connected_of_chain {r : ℕ} [NeZero r] {A : Matrix (Fin r) (Fin r) ℤ}
    (h : ∀ k l : Fin r, (l : ℕ) = k + 1 → A k l ≠ 0 ∧ A l k ≠ 0) :
    (dynkinGraph A).Connected := by
  refine (SimpleGraph.connected_iff_exists_forall_reachable _).2 ⟨0, fun j => ?_⟩
  obtain ⟨m, hm⟩ := j
  induction m with
  | zero =>
    rw [show (⟨0, hm⟩ : Fin r) = 0 from Fin.ext (by simp)]
  | succ m ih =>
    have hm' : m < r := by omega
    obtain ⟨h1, h2⟩ := h ⟨m, hm'⟩ ⟨m + 1, hm⟩ rfl
    refine (ih hm').trans (SimpleGraph.Adj.reachable ⟨fun heq => ?_, h1, h2⟩)
    rw [Fin.ext_iff] at heq
    simp at heq

theorem isIndecomposable_of_chain {r : ℕ} {A : Matrix (Fin r) (Fin r) ℤ}
    (h : ∀ k l : Fin r, (l : ℕ) = k + 1 → A k l ≠ 0 ∧ A l k ≠ 0) : IsIndecomposable A := by
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · rintro ⟨I, -, ⟨i, -⟩, -⟩
    exact i.elim0
  · have : NeZero r := ⟨hr.ne'⟩
    exact isIndecomposable_of_connected (connected_of_chain h)

end CFSG.LieType.TitsSimplicity
