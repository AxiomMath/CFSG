module

public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.IsoBlocksFixed

public section

namespace CFSG.HardMathSupport.Cooperstein.AlternatingGeometry

open Equiv Equiv.Perm

variable {d : ℕ}

theorem two_mul_isoCount (W : Subgroup (Perm (Fin d))) :
    2 * Nat.card {x : Fin d // ∃ y, x < y ∧ IsIsoPair W x y} =
      Nat.card {x : Fin d // ∃ y, IsIsoPair W x y} := by
  classical
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_subtype, Fintype.card_subtype]
  let pt : Fin d → Fin d := fun x => if h : ∃ y, IsIsoPair W x y then h.choose else x
  have hpt : ∀ x, (∃ y, IsIsoPair W x y) → IsIsoPair W x (pt x) := by
    intro x hx
    simp only [pt, hx, ↓reduceDIte]
    exact hx.choose_spec
  have hptu : ∀ x y, IsIsoPair W x y → pt x = y := fun x y hy =>
    ((hpt x ⟨y, hy⟩).partner_unique hy)
  set T := Finset.univ.filter (fun x : Fin d => ∃ y, IsIsoPair W x y) with hT
  set P := Finset.univ.filter (fun x : Fin d => ∃ y, x < y ∧ IsIsoPair W x y) with hP
  set Q := T.filter (fun x => pt x < x) with hQ
  have hPT : P = T.filter (fun x => x < pt x) := by
    ext x
    simp only [hP, hT, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨y, hxy, hy⟩
      exact ⟨⟨y, hy⟩, by rw [hptu x y hy]; exact hxy⟩
    · rintro ⟨hx, hlt⟩
      exact ⟨pt x, hlt, hpt x hx⟩
  have hsplit : T.card = P.card + Q.card := by
    rw [hPT, hQ, ← Finset.card_union_of_disjoint]
    · congr 1
      ext x
      simp only [Finset.mem_union, Finset.mem_filter]
      constructor
      · intro hx
        refine (lt_trichotomy x (pt x)).elim (fun h => Or.inl ⟨hx, h⟩) fun h => h.elim
          (fun h => absurd h (hpt x (by simpa [hT] using hx)).1) fun h => Or.inr ⟨hx, h⟩
      · rintro (h | h) <;> exact h.1
    · rw [Finset.disjoint_left]
      intro x h1 h2
      simp only [Finset.mem_filter] at h1 h2
      exact lt_asymm h1.2 h2.2
  have hinv : ∀ x, (∃ y, IsIsoPair W x y) → pt (pt x) = x := fun x hx =>
    hptu _ _ (hpt x hx).symm'
  have hTmem : ∀ x, x ∈ T ↔ ∃ y, IsIsoPair W x y := by
    intro x; simp [hT]
  have hQP : Q.card = P.card := by
    symm
    apply Finset.card_bij (fun x _ => pt x)
    · intro x hx
      rw [hPT] at hx
      simp only [Finset.mem_filter] at hx
      have hx' := (hTmem x).1 hx.1
      refine Finset.mem_filter.2 ⟨(hTmem _).2 ⟨x, (hpt x hx').symm'⟩, ?_⟩
      rw [hinv x hx']; exact hx.2
    · intro x hx y hy h
      rw [hPT] at hx hy
      simp only [Finset.mem_filter] at hx hy
      have := congrArg pt h
      rwa [hinv x ((hTmem x).1 hx.1), hinv y ((hTmem y).1 hy.1)] at this
    · intro y hy
      simp only [hQ, Finset.mem_filter] at hy
      have hy' := (hTmem y).1 hy.1
      refine ⟨pt y, ?_, hinv y hy'⟩
      rw [hPT]
      refine Finset.mem_filter.2 ⟨(hTmem _).2 ⟨y, (hpt y hy').symm'⟩, ?_⟩
      rw [hinv y hy']; exact hy.2
  rw [hsplit, hQP]
  ring

end CFSG.HardMathSupport.Cooperstein.AlternatingGeometry
