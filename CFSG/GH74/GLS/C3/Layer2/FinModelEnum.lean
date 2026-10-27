module

public import CFSG.GH74.GLS.C3.Layer2.FinModelDefs
public import Mathlib.Data.List.Dedup
public meta import Mathlib.GroupTheory.SpecificGroups.Alternating
public meta import CFSG.GH74.GLS.C3.Layer2.FinModelDefs
public import CFSG.GH74.GLS.C3.Layer2.FinModelEnumInputs
public meta import CFSG.GH74.GLS.C3.Layer2.FinModelEnumInputs
public import Certificates.Certificate5039

public section

namespace CFSG.GH74.GLS.C3.Layer2.Model

open Equiv Perm Subgroup

theorem mem_closure_of_mem_closureList {G : Type*} [Group G] [DecidableEq G] (gens : List G)
    (k : ℕ) : ∀ g ∈ closureList gens k, g ∈ Subgroup.closure {x | x ∈ gens} := by
  induction k with
  | zero =>
    intro g hg
    simp only [closureList, Function.iterate_zero, id, List.mem_singleton] at hg
    rw [hg]; exact one_mem _
  | succ k ih =>
    intro g hg
    simp only [closureList, Function.iterate_succ_apply'] at hg
    simp only [closureStep, List.mem_dedup, List.mem_append, List.mem_flatMap,
      List.mem_map] at hg
    rcases hg with hg | ⟨h, hh, s, hs, rfl⟩
    · exact ih g hg
    · exact mul_mem (ih h hh) (Subgroup.subset_closure hs)

theorem one_mem_closureList {G : Type*} [Mul G] [One G] [DecidableEq G] (gens : List G) (k : ℕ) :
    (1 : G) ∈ closureList gens k := by
  induction k with
  | zero => simp [closureList]
  | succ k ih =>
    simp only [closureList, Function.iterate_succ_apply'] at ih ⊢
    simp only [closureStep, List.mem_dedup, List.mem_append]
    exact Or.inl ih

theorem sigmaGens_eq (n : ℕ) [NeZero n] : sigmaGens n = {x | x ∈ sigmaGensList n} := by
  ext x
  simp [sigmaGens, sigmaGensList]

theorem Dl_spec :
    ∀ d : Perm (Fin 4), d * x4 = x4 * d ↔ d ∈ Dl :=
  Certificates.certificate5039.1

theorem plClosedB6 : plClosedB 6 = true :=
  Certificates.certificate5039.2.1

theorem plClosedB7 : plClosedB 7 = true :=
  Certificates.certificate5039.2.2.1

theorem tlFactsB6 : tlFactsB 6 = true :=
  Certificates.certificate5039.2.2.2.1

theorem tlFactsB7 : tlFactsB 7 = true :=
  Certificates.certificate5039.2.2.2.2

theorem Pl_closed (n : ℕ) [NeZero n] (hn : n = 6 ∨ n = 7) :
    (∀ a ∈ Pl n, ∀ b ∈ Pl n, a * b ∈ Pl n) ∧ (∀ a ∈ Pl n, a⁻¹ ∈ Pl n) ∧
      (∀ a ∈ sigmaGensList n, a ∈ Pl n) := by
  have h : plClosedB n = true := by
    rcases hn with rfl | rfl
    · exact plClosedB6
    · exact plClosedB7
  simpa [plClosedB, List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq, and_assoc] using h

theorem Tl_facts (n : ℕ) [NeZero n] (hn : n = 6 ∨ n = 7) :
    (Tl n).length = 64 ∧ (Tl n).Nodup ∧ (Pl n).length = 16 := by
  have h : tlFactsB n = true := by
    rcases hn with rfl | rfl
    · exact tlFactsB6
    · exact tlFactsB7
  simpa [tlFactsB, Bool.and_eq_true, decide_eq_true_eq, and_assoc] using h

theorem mem_closure_sigmaGens_iff
    (n : ℕ) [NeZero n] (hn : n = 6 ∨ n = 7) (σ : Perm (Fin n)) :
    σ ∈ Subgroup.closure (sigmaGens n) ↔ σ ∈ Pl n := by
  obtain ⟨hmul, hinv, hgen⟩ := Pl_closed n hn
  constructor
  · intro h
    rw [sigmaGens_eq] at h
    refine Subgroup.closure_induction (p := fun x _ => x ∈ Pl n) ?_ ?_ ?_ ?_ h
    · intro x hx; exact hgen x hx
    · exact one_mem_closureList _ _
    · intro x y _ _ hx hy; exact hmul x hx y hy
    · intro x _ hx; exact hinv x hx
  · intro h
    rw [sigmaGens_eq]
    exact mem_closure_of_mem_closureList _ _ σ h

theorem mem_T0_iff
    (n : ℕ) [NeZero n] (hn : n = 6 ∨ n = 7) (g : Amb n) :
    g ∈ T0 n ↔ g ∈ Tl n := by
  constructor
  · rintro ⟨hF, h1, -⟩
    have hP : g.1 ∈ Pl n := (mem_closure_sigmaGens_iff n hn g.1).1 h1
    have hD : g.2 ∈ Dl := (Dl_spec g.2).1 hF.1
    simp only [Tl, List.mem_flatMap, List.mem_map, List.mem_filter, decide_eq_true_eq]
    exact ⟨g.1, hP, g.2, ⟨hD, hF.2⟩, rfl⟩
  · intro h
    simp only [Tl, List.mem_flatMap, List.mem_map, List.mem_filter, decide_eq_true_eq] at h
    obtain ⟨σ, hσ, d, ⟨hd, hs⟩, rfl⟩ := h
    exact ⟨⟨(Dl_spec d).2 hd, hs⟩, (mem_closure_sigmaGens_iff n hn σ).2 hσ, trivial⟩

theorem card_T0_eq
    (n : ℕ) [NeZero n] (hn : n = 6 ∨ n = 7) : Nat.card (T0 n) = 64 := by
  obtain ⟨hlen, hnd, -⟩ := Tl_facts n hn
  have : Nat.card (T0 n) = Nat.card ((Tl n).toFinset) := by
    apply Nat.card_congr
    exact Equiv.subtypeEquivRight (fun g => by simpa using mem_T0_iff n hn g)
  rw [this, Nat.card_eq_fintype_card, Fintype.card_coe, List.toFinset_card_of_nodup hnd, hlen]

end CFSG.GH74.GLS.C3.Layer2.Model
