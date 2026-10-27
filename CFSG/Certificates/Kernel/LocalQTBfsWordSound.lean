module

public import CFSG.Certificates.Kernel.LocalQTBfsKSound
import all CFSG.Certificates.Kernel.LocalQTBfsKSound
import all CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListPermEnc

public section

namespace CFSG.KC.LQT.CM

open CFSG.KC.LQT.L CFSG.QuasithinUnique.Vol2Native.A312L.PermLat

section Round

variable {R : Type} [DecidableEq R] [Hashable R]

theorem hstep_sub (A : Std.HashSet R × List R) (y z : R) (h : z ∈ A.1) : z ∈ (hstep A y).1 := by
  unfold hstep
  split
  · exact h
  · exact Std.HashSet.mem_insert.2 (Or.inr h)

theorem hstep_mem (A : Std.HashSet R × List R) (y : R) : y ∈ (hstep A y).1 := by
  unfold hstep
  split
  · rename_i hc
    exact Std.HashSet.contains_iff_mem.1 hc
  · exact Std.HashSet.mem_insert.2 (Or.inl (beq_self_eq_true y))

theorem hstep_front (A : Std.HashSet R × List R) (y z : R) (h : z ∈ A.2) : z ∈ (hstep A y).2 := by
  unfold hstep
  split
  · exact h
  · exact List.mem_cons_of_mem _ h

theorem hstep_new (A : Std.HashSet R × List R) (y z : R) (h : z ∈ (hstep A y).1) :
    z ∈ A.1 ∨ z ∈ (hstep A y).2 := by
  unfold hstep at h ⊢
  by_cases hc : A.1.contains y = true
  · simp only [hc, ↓reduceIte] at h
    exact Or.inl h
  · rw [Bool.not_eq_true] at hc
    simp only [hc, Bool.false_eq_true, ↓reduceIte] at h ⊢
    rcases Std.HashSet.mem_insert.1 h with e | h
    · rw [beq_iff_eq] at e
      subst e
      exact Or.inr List.mem_cons_self
    · exact Or.inl h

theorem fold_facts : ∀ (ys : List R) (A : Std.HashSet R × List R),
    (∀ z ∈ A.1, z ∈ (ys.foldl hstep A).1) ∧ (∀ y ∈ ys, y ∈ (ys.foldl hstep A).1) ∧
      (∀ z ∈ A.2, z ∈ (ys.foldl hstep A).2) ∧
      (∀ z ∈ (ys.foldl hstep A).1, z ∈ A.1 ∨ z ∈ (ys.foldl hstep A).2)
  | [], A => ⟨fun _ h => h, fun _ h => absurd h List.not_mem_nil, fun _ h => h, fun _ h => Or.inl h⟩
  | y :: ys, A => by
    obtain ⟨h1, h2, h3, h4⟩ := fold_facts ys (hstep A y)
    rw [List.foldl_cons]
    refine ⟨fun z hz => h1 z (hstep_sub A y z hz), fun z hz => ?_, fun z hz => h3 z (hstep_front A y z hz),
      fun z hz => ?_⟩
    · rcases List.mem_cons.1 hz with rfl | hz
      · exact h1 _ (hstep_mem A _)
      · exact h2 z hz
    · rcases h4 z hz with hz | hz
      · rcases hstep_new A y z hz with hz | hz
        · exact Or.inl hz
        · exact Or.inr (h3 z hz)
      · exact Or.inr hz

variable [Mul R]

def roundProds (gens F : List R) : List R := F.flatMap fun x => gens.map fun g => x * g

theorem bfsStep_fold (gens : List R) (S : Std.HashSet R) (F : List R) :
    bfsStep gens S F = (roundProds gens F).foldl hstep (S, []) := by
  rw [bfsStep_eq]
  unfold roundProds
  generalize (S, ([] : List R)) = A
  induction F generalizing A with
  | nil => rfl
  | cons x F ih =>
    rw [List.foldl_cons, List.flatMap_cons, List.foldl_append, ← ih, List.foldl_map]

theorem round_facts (gens : List R) (S : Std.HashSet R) (F : List R) :
    (∀ z ∈ S, z ∈ (bfsStep gens S F).1) ∧
      (∀ x ∈ F, ∀ g ∈ gens, x * g ∈ (bfsStep gens S F).1) ∧
      (∀ z ∈ (bfsStep gens S F).1, z ∈ S ∨ z ∈ (bfsStep gens S F).2) := by
  rw [bfsStep_fold]
  obtain ⟨h1, h2, -, h4⟩ := fold_facts (roundProds gens F) (S, [])
  refine ⟨h1, fun x hx g hg => h2 _ ?_, h4⟩
  unfold roundProds
  exact List.mem_flatMap.2 ⟨x, hx, List.mem_map.2 ⟨g, hg, rfl⟩⟩

end Round

section Words

variable {G : Type} [Group G] {R : Type} [Mul R] [One R] [DecidableEq R] [Hashable R]
  {enc : G → R} (hmul : ∀ a b, enc (a * b) = enc a * enc b) (h1 : enc 1 = 1) (gens : List G)
include hmul h1

theorem bfs_inv : ∀ t : ℕ,
    (∀ l : List G, (∀ g ∈ l, g ∈ gens) → l.length ≤ t →
      enc l.prod ∈ (bfsRun (gens.map enc) t ((∅ : Std.HashSet R).insert 1, [1])).1) ∧
    (∀ x ∈ (bfsRun (gens.map enc) t ((∅ : Std.HashSet R).insert 1, [1])).1,
      x ∉ (bfsRun (gens.map enc) t ((∅ : Std.HashSet R).insert 1, [1])).2 →
      ∀ g ∈ gens.map enc, x * g ∈ (bfsRun (gens.map enc) t ((∅ : Std.HashSet R).insert 1, [1])).1)
  | 0 => by
    refine ⟨fun l _ hl => ?_, fun x hx hxF => ?_⟩
    · rw [List.length_eq_zero_iff.1 (Nat.le_zero.1 hl), List.prod_nil, h1]
      exact Std.HashSet.mem_insert.2 (Or.inl (beq_self_eq_true _))
    · change x ∈ (∅ : Std.HashSet R).insert 1 at hx
      change x ∉ [(1 : R)] at hxF
      rcases Std.HashSet.mem_insert.1 hx with e | hx
      · rw [beq_iff_eq] at e
        exact absurd (e ▸ List.mem_singleton_self _) hxF
      · exact absurd hx (Std.HashSet.not_mem_empty)
  | t + 1 => by
    obtain ⟨i1, i2⟩ := bfs_inv t
    rw [bfsRun_succ]
    set st := bfsRun (gens.map enc) t ((∅ : Std.HashSet R).insert 1, [1])
    obtain ⟨r1, r2, r3⟩ := round_facts (gens.map enc) st.1 st.2
    have ext : ∀ x ∈ st.1, ∀ g ∈ gens.map enc, x * g ∈ (bfsStep (gens.map enc) st.1 st.2).1 :=
      fun x hx g hg => by
        by_cases hxF : x ∈ st.2
        · exact r2 x hxF g hg
        · exact r1 _ (i2 x hx hxF g hg)
    refine ⟨fun l hl hlen => ?_, fun x hx hxF g hg => ?_⟩
    · by_cases hlt : l.length ≤ t
      · exact r1 _ (i1 l hl hlt)
      · obtain ⟨l', g, rfl⟩ : ∃ l' g, l = l' ++ [g] := by
          rcases List.eq_nil_or_concat l with rfl | ⟨l', g, rfl⟩
          · simp at hlt
          · exact ⟨l', g, List.concat_eq_append ..⟩
        rw [List.prod_append, List.prod_singleton, hmul]
        have hl' : ∀ g ∈ l', g ∈ gens := fun g hg => hl g (List.mem_append_left _ hg)
        have hlen' : l'.length ≤ t := by simp at hlen; omega
        exact ext _ (i1 l' hl' hlen') _
          (List.mem_map_of_mem (hl g (List.mem_append_right _ (List.mem_singleton_self _))))
    · rcases r3 x hx with hx | hx
      · exact ext x hx g hg
      · exact absurd hx hxF

theorem mem_bfsSet_prod (d : ℕ) (l : List G) (hl : ∀ g ∈ l, g ∈ gens) (hlen : l.length ≤ d) :
    enc l.prod ∈ bfsSet (gens.map enc) d :=
  (bfs_inv hmul h1 gens d).1 l hl hlen

end Words

end CFSG.KC.LQT.CM

end
