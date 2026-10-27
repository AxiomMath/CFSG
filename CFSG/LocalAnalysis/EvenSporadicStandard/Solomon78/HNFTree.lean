module

public import Std.Data.HashSet.Lemmas
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.HNFWalk
public import Mathlib.Data.Finset.Attr
public import Mathlib.Data.List.Nodup
public import Mathlib.Tactic.Bound.Init
public import Mathlib.Tactic.Finiteness.Attr
public import Mathlib.Tactic.SetLike
public import Mathlib.Tactic.ToAdditive

public section

namespace CFSG.EvenSporadicStandard.Solomon78

variable {Ω : Type*}

inductive HNFReach (m : ℕ) (act : ℕ → Ω → Ω) (ω₀ : Ω) : Ω → Prop
  | base : HNFReach m act ω₀ ω₀
  | step {g : ℕ} {ω : Ω} : g < m → HNFReach m act ω₀ ω → HNFReach m act ω₀ (act g ω)

theorem hnfWalk_sound {m : ℕ} {act : ℕ → Ω → Ω} {st : Ω → Array ℕ}
    {step : ℕ → Array ℕ → Array ℕ} (hstep : ∀ g < m, ∀ ω, st (act g ω) = step g (st ω))
    {key : Array ℕ → ℕ} {ω₀ : Ω} :
    ∀ (moves : List (ℕ × ℕ)) (stack : List (Array ℕ)) (seen : Std.HashSet ℕ) (cnt N : ℕ)
      (E L : List Ω), stack = E.map st → (∀ ω ∈ E, HNFReach m act ω₀ ω) → (∀ ω ∈ E, ω ∈ L) →
      L.Nodup → L.length = cnt → (∀ ω ∈ L, HNFReach m act ω₀ ω) →
      (∀ k, seen.contains k = true ↔ ∃ ω ∈ L, key (st ω) = k) →
      hnfWalk m step key moves stack seen cnt = some N →
      ∃ L' : List Ω, L'.Nodup ∧ L'.length = N ∧ ∀ ω ∈ L', HNFReach m act ω₀ ω := by
  intro moves
  induction moves with
  | nil =>
    intro stack seen cnt N E L _ _ _ hnd hlen hreach _ h
    simp only [hnfWalk, Option.some.injEq] at h
    exact ⟨L, hnd, by rw [hlen, h], hreach⟩
  | cons mv rest ih =>
    obtain ⟨up, g⟩ := mv
    intro stack seen cnt N E L hst hE hEL hnd hlen hreach hseen h
    simp only [hnfWalk] at h
    by_cases hg : g < m
    · simp only [hg, ↓reduceIte] at h
      have hdrop : stack.drop up = (E.drop up).map st := by rw [hst, List.map_drop]
      rcases hED : E.drop up with _ | ⟨ω₁, E'⟩
      · rw [hED] at hdrop
        simp only [List.map_nil] at hdrop
        rw [hdrop] at h
        simp at h
      · rw [hED] at hdrop
        simp only [List.map_cons] at hdrop
        rw [hdrop] at h
        simp only at h
        by_cases hsn : seen.contains (key (step g (st ω₁))) = true
        · simp only [hsn, ↓reduceIte] at h
          simp at h
        · simp only [hsn, Bool.false_eq_true, ↓reduceIte] at h
          have hω₁E : ω₁ ∈ E := List.mem_of_mem_drop (hED ▸ List.mem_cons_self)
          have hE'E : ∀ ω ∈ E', ω ∈ E := fun ω hω =>
            List.mem_of_mem_drop (hED ▸ List.mem_cons_of_mem _ hω)
          have hnotL : act g ω₁ ∉ L := by
            intro hmem
            apply hsn
            rw [hseen]
            exact ⟨act g ω₁, hmem, by rw [hstep g hg]⟩
          refine ih _ _ _ N (act g ω₁ :: ω₁ :: E') (act g ω₁ :: L) ?_ ?_ ?_ ?_ ?_ ?_ ?_ h
          · simp [hstep g hg]
          · intro ω hω
            simp only [List.mem_cons] at hω
            rcases hω with rfl | rfl | hω
            · exact HNFReach.step hg (hE ω₁ hω₁E)
            · exact hE _ hω₁E
            · exact hE ω (hE'E ω hω)
          · intro ω hω
            simp only [List.mem_cons] at hω ⊢
            rcases hω with rfl | rfl | hω
            · exact Or.inl rfl
            · exact Or.inr (hEL _ hω₁E)
            · exact Or.inr (hEL ω (hE'E ω hω))
          · exact List.nodup_cons.2 ⟨hnotL, hnd⟩
          · simp [hlen]
          · intro ω hω
            rcases List.mem_cons.1 hω with rfl | hω
            · exact HNFReach.step hg (hE ω₁ hω₁E)
            · exact hreach ω hω
          · intro k
            rw [Std.HashSet.contains_insert]
            simp only [Bool.or_eq_true, beq_iff_eq, hseen, List.mem_cons, exists_eq_or_imp,
              hstep g hg]
    · simp only [hg, ↓reduceIte] at h
      simp at h

theorem hnfWalk_sound' {m : ℕ} {act : ℕ → Ω → Ω} {st : Ω → Array ℕ}
    {step : ℕ → Array ℕ → Array ℕ} (hstep : ∀ g < m, ∀ ω, st (act g ω) = step g (st ω))
    {key : Array ℕ → ℕ} (ω₀ : Ω) (moves : List (ℕ × ℕ)) (N : ℕ)
    (h : hnfWalk m step key moves [st ω₀] ((∅ : Std.HashSet ℕ).insert (key (st ω₀))) 1 = some N) :
    ∃ L : List Ω, L.Nodup ∧ L.length = N ∧ ∀ ω ∈ L, HNFReach m act ω₀ ω := by
  refine hnfWalk_sound hstep moves [st ω₀] _ 1 N [ω₀] [ω₀] rfl ?_ ?_ (List.nodup_singleton _)
    rfl ?_ ?_ h
  · simpa using HNFReach.base
  · simp
  · simpa using HNFReach.base
  · intro k
    rw [Std.HashSet.contains_insert, Std.HashSet.contains_empty]
    simp only [Bool.or_false, beq_iff_eq, List.mem_singleton, exists_eq_left]

end CFSG.EvenSporadicStandard.Solomon78
