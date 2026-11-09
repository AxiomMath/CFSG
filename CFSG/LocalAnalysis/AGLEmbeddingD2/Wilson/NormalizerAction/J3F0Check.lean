module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.NormalizerAction.J3F0Mat

public section

namespace CFSG.AGLEmbeddingD2.Wilson.NormalizerAction

open Matrix

private theorem all_of_chunks {α : Type*} (l : List α) (d : α) (f : α → Bool) (m K : ℕ)
    (hm : 0 < m) (hlen : l.length ≤ m * K)
    (h : ∀ k < K, (List.range' (m * k) m).all (fun i => f (l.getD i d)) = true) :
    l.all f = true := by
  rw [List.all_eq_true]
  intro x hx
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hx
  have hk : i / m < K := Nat.div_lt_of_lt_mul (lt_of_lt_of_le hi hlen)
  have hmem : i ∈ List.range' (m * (i / m)) m := by
    rw [List.mem_range'_1]
    have h1 := Nat.div_add_mod i m
    have h2 := Nat.mod_lt i hm
    generalize m * (i / m) = q at h1 ⊢
    generalize i % m = r at h1 h2
    omega
  have := List.all_eq_true.1 (h (i / m) hk) i hmem
  rwa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some] at this

private theorem matS_length_le : matS.length ≤ 12 * 6 := by
  decide +kernel

private theorem matChk_closed_0 :
    (List.range' (12 * 0) 12).all (fun i => matS.all fun t => inS (mulM (matS.getD i 1) t)) =
      true := by
  decide +kernel

private theorem matChk_closed_1 :
    (List.range' (12 * 1) 12).all (fun i => matS.all fun t => inS (mulM (matS.getD i 1) t)) =
      true := by
  decide +kernel

private theorem matChk_closed_2 :
    (List.range' (12 * 2) 12).all (fun i => matS.all fun t => inS (mulM (matS.getD i 1) t)) =
      true := by
  decide +kernel

private theorem matChk_closed_3 :
    (List.range' (12 * 3) 12).all (fun i => matS.all fun t => inS (mulM (matS.getD i 1) t)) =
      true := by
  decide +kernel

private theorem matChk_closed_4 :
    (List.range' (12 * 4) 12).all (fun i => matS.all fun t => inS (mulM (matS.getD i 1) t)) =
      true := by
  decide +kernel

private theorem matChk_closed_5 :
    (List.range' (12 * 5) 12).all (fun i => matS.all fun t => inS (mulM (matS.getD i 1) t)) =
      true := by
  decide +kernel

private theorem matChk_closed : matS.all (fun s => matS.all fun t => inS (mulM s t)) = true :=
  all_of_chunks matS 1 _ 12 6 (by decide) matS_length_le (fun k hk => match k, hk with
    | 0, _ => matChk_closed_0
    | 1, _ => matChk_closed_1
    | 2, _ => matChk_closed_2
    | 3, _ => matChk_closed_3
    | 4, _ => matChk_closed_4
    | 5, _ => matChk_closed_5
    | _ + 6, h => absurd h (by omega))

private theorem matChk_rest :
    (inS 1 && (List.finRange 6).all (fun i => inS (actMat i)) &&
      matS.all (fun s => matS.any fun t => eqM (mulM s t) 1) &&
      matS.all (fun s => eqM s 1 || allV.any fun v => nzV (mulV (subOne s) (mulV (subOne s) v)))) =
      true := by
  decide +kernel

theorem matChk_true : matChk = true := by
  unfold matChk
  rw [matChk_closed, Bool.and_true]
  exact matChk_rest

theorem matFacts :
    (1 : Matrix (Fin 4) (Fin 4) (ZMod 3)) ∈ matS ∧ (∀ i : Fin 6, actMat i ∈ matS) ∧
    (∀ s ∈ matS, ∀ t ∈ matS, s * t ∈ matS) ∧ (∀ s ∈ matS, ∃ t ∈ matS, s * t = 1) ∧
    (∀ s ∈ matS, s = 1 ∨ ∃ v : Fin 4 → ZMod 3, (s - 1) *ᵥ ((s - 1) *ᵥ v) ≠ 0) := by
  have h := matChk_true
  simp only [matChk, Bool.and_eq_true, List.all_eq_true, List.any_eq_true, Bool.or_eq_true,
    List.mem_finRange, forall_const, inS_iff, eqM_iff, nzV_iff, mulM_eq, mulV_eq, subOne_eq] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  refine ⟨h1, h2, h3, h4, ?_⟩
  intro s hs
  rcases h5 s hs with h | ⟨v, -, hv⟩
  · exact Or.inl h
  · exact Or.inr ⟨v, hv⟩

theorem fix_triv (a : Fin 4 → ZMod 3) (h1 : actMat 1 *ᵥ a = a) (h2 : actMat 2 *ᵥ a = a) :
    a 0 = 0 ∧ a 1 = 0 ∧ a 2 = 0 := by
  have key : ∀ a : Fin 4 → ZMod 3, mulV (actMat 1) a = a → mulV (actMat 2) a = a →
      a 0 = 0 ∧ a 1 = 0 ∧ a 2 = 0 := by decide
  exact key a (by rw [mulV_eq]; exact h1) (by rw [mulV_eq]; exact h2)

end CFSG.AGLEmbeddingD2.Wilson.NormalizerAction
