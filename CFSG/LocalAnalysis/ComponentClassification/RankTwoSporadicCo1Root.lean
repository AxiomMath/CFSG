module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicCo1PW

public section

namespace CFSG.ComponentClassification.RankTwoSporadic.Co1

open Subgroup CFSG.Sporadic.Co1Schreier

namespace RootWitness

variable {X : Subgroup GL24} {base : List Native.Rows} {baseG : List GL24}
  {glob : List (List ℤ)} {r : Native.Rows} {x : GL24}
  {s₁ s₂ : List ℕ} {d₁ d₂ : List (List ℤ)} {zh₁ zh₂ : ℕ × ℕ} {dec₁ dec₂ : List (List ℕ)}

theorem forall₂_entries {E : List Native.Rows} {EG : List GL24} (h : List.Forall₂ MRep E EG)
    (s : List ℕ) : List.Forall₂ MRep (s.map (entryR E)) (s.map (entryG EG)) := by
  induction s with
  | nil => exact List.Forall₂.nil
  | cons k s ih => exact List.Forall₂.cons (mrep_entry h k) ih

theorem mem_of_entries {E : List Native.Rows} {EG : List GL24} (hE : List.Forall₂ MRep E EG)
    {H : Subgroup GL24} (hEG : ∀ g ∈ EG, g ∈ H) {targets : List Native.Rows} {TG : List GL24}
    (ht : List.Forall₂ MRep targets TG) :
    ∀ {idx : List ℕ}, idx.map (entryR E) = targets → ∀ g ∈ TG, g ∈ H := by
  induction ht with
  | nil => intro _ _ g hg; exact absurd hg List.not_mem_nil
  | @cons r g' rs gs hr _ ih =>
    intro idx h g hg
    match idx, h with
    | i :: is, h =>
      simp only [List.map_cons, List.cons.injEq] at h
      rcases List.mem_cons.mp hg with rfl | hg
      · have := mrep_entry hE i
        rw [h.1] at this
        rw [hr.eq this]
        exact entryG_mem hEG i
      · exact ih h.2 g hg

theorem pWitness (hb : List.Forall₂ MRep base baseG) (hbX : ∀ g ∈ baseG, g ∈ X)
    (hG : (Native.dag base glob).2.2 = true) (hr : MRep r x) (hx1 : x ≠ 1)
    (hP₁ : pwOK (entriesR base glob s₁) d₁ zh₁.1 zh₁.2 dec₁ r = true)
    (hP₂ : pwOK (entriesR base glob s₂) d₂ zh₂.1 zh₂.2 dec₂ r = true) {Z : Set GL24}
    (hZ : ∀ b ∈ X ⊓ Subgroup.centralizer {x},
      (∀ y ∈ s₁.map (entryG (dagG baseG glob)), b * y = y * b) →
      (∀ y ∈ s₂.map (entryG (dagG baseG glob)), b * y = y * b) → b ∈ Z)
    {E : Subgroup GL24} (hEX : E ≤ X) (hE : CFSG.Open.IsElemAbelian 2 E) (hxE : x ∈ E)
    (hEZ : ¬ (E : Set GL24) ⊆ Z) : PWitness X E := by
  have hrep := dag_rep hb glob hG
  have hmem : ∀ g ∈ dagG baseG glob, g ∈ X := dagG_mem hbX glob
  have hS₁ := forall₂_entries hrep s₁
  have hS₂ := forall₂_entries hrep s₂
  obtain ⟨hc₁, hpg₁⟩ := pw_of_check hS₁ hr hP₁
  obtain ⟨hc₂, hpg₂⟩ := pw_of_check hS₂ hr hP₂
  have hle : ∀ s : List ℕ, (∀ y ∈ s.map (entryG (dagG baseG glob)), y * x = x * y) →
      Subgroup.closure {g | g ∈ s.map (entryG (dagG baseG glob))} ≤
        X ⊓ Subgroup.centralizer {x} := by
    intro s hc
    rw [Subgroup.closure_le]
    intro y hy
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · obtain ⟨k, -, rfl⟩ := List.mem_map.mp hy
      exact entryG_mem hmem k
    · exact Subgroup.mem_centralizer_singleton_iff.mpr (hc y hy)
  obtain ⟨b, hbE, hbZ⟩ := Set.not_subset.mp hEZ
  have hbC : b ∈ X ⊓ Subgroup.centralizer {x} :=
    Subgroup.mem_inf.mpr ⟨hEX hbE, Subgroup.mem_centralizer_singleton_iff.mpr
      (comm_of_isElemAbelian hE hbE hxE)⟩
  by_cases h₁ : ∀ y ∈ s₁.map (entryG (dagG baseG glob)), b * y = y * b
  · by_cases h₂ : ∀ y ∈ s₂.map (entryG (dagG baseG glob)), b * y = y * b
    · exact absurd (hZ b hbC h₁ h₂) hbZ
    · push Not at h₂
      obtain ⟨y, hy, hby⟩ := h₂
      refine pWitness_of_perfGen hxE hx1 (hle s₂ hc₂) hpg₂ fun hEC => hby ?_
      exact (Subgroup.mem_centralizer_iff.mp (hEC hbE) y (Subgroup.subset_closure hy)).symm
  · push Not at h₁
    obtain ⟨y, hy, hby⟩ := h₁
    refine pWitness_of_perfGen hxE hx1 (hle s₁ hc₁) hpg₁ fun hEC => hby ?_
    exact (Subgroup.mem_centralizer_iff.mp (hEC hbE) y (Subgroup.subset_closure hy)).symm

theorem comm_of_words (hb : List.Forall₂ MRep base baseG)
    (hG : (Native.dag base glob).2.2 = true) {d : List (List ℤ)} {idx : List ℕ}
    {targets : List Native.Rows} {TG : List GL24} (ht : List.Forall₂ MRep targets TG)
    (hw : wordsOK (entriesR base glob s₁ ++ entriesR base glob s₂) d idx targets = true)
    {b : GL24} (h₁ : ∀ y ∈ s₁.map (entryG (dagG baseG glob)), b * y = y * b)
    (h₂ : ∀ y ∈ s₂.map (entryG (dagG baseG glob)), b * y = y * b) :
    ∀ g ∈ TG, b * g = g * b := by
  simp only [wordsOK, Bool.and_eq_true, beq_iff_eq] at hw
  obtain ⟨hD, hE⟩ := hw
  have hrep := dag_rep hb glob hG
  have hS := List.rel_append (forall₂_entries hrep s₁) (forall₂_entries hrep s₂)
  have hrepd := dag_rep hS d hD
  have hle : Subgroup.closure {g | g ∈ s₁.map (entryG (dagG baseG glob)) ++
      s₂.map (entryG (dagG baseG glob))} ≤ Subgroup.centralizer {b} :=
    (Subgroup.closure_le _).mpr fun y hy => Subgroup.mem_centralizer_singleton_iff.mpr
      ((List.mem_append.mp hy).elim (fun h => (h₁ y h).symm) (fun h => (h₂ y h).symm))
  intro g hg
  have hgm := mem_of_entries hrepd (dagG_mem (fun g hg => Subgroup.subset_closure hg) d) ht hE g hg
  exact (Subgroup.mem_centralizer_singleton_iff.mp (hle hgm)).symm

end RootWitness

end CFSG.ComponentClassification.RankTwoSporadic.Co1
