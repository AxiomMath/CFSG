module

public import Mathlib.Data.Matrix.Mul

public section

namespace CFSG.KC.BM.TwoAC

open scoped Matrix

variable {n : ℕ} {K : Type*} [CommRing K]

@[expose] def ForestOK (n : ℕ) (c : ℕ → ℕ) : Prop := ∀ t < n, c t < 2 * n → c t / 2 < t

@[expose] def SpinRel (c : ℕ → ℕ) (D : ℕ → Matrix (Fin n) (Fin n) K) (ρ : ℕ → Fin n → K)
    (S : Matrix (Fin n) (Fin n) K) : Prop :=
  ∀ t : Fin n, S t = if 2 * n ≤ c t.val then ρ (c t.val - 2 * n)
    else if h : c t.val / 2 < n then S ⟨c t.val / 2, h⟩ ᵥ* D (c t.val % 2) else 0

variable {c : ℕ → ℕ} {D : ℕ → Matrix (Fin n) (Fin n) K}

theorem spinRel_unique (hc : ForestOK n c) {ρ : ℕ → Fin n → K}
    {S S' : Matrix (Fin n) (Fin n) K} (h : SpinRel c D ρ S) (h' : SpinRel c D ρ S') : S = S' := by
  suffices key : ∀ m, ∀ t : Fin n, t.val < m → S t = S' t from
    funext fun t => key _ t (Nat.lt_succ_self _)
  intro m
  induction m with
  | zero => intro t ht; omega
  | succ m ih =>
    intro t ht
    rw [h t, h' t]
    split_ifs with h1 h2
    · rfl
    · rw [ih ⟨_, h2⟩ (by have := hc t.val t.isLt (by omega); simp only; omega)]
    · rfl

theorem spinRel_zero : SpinRel c D (0 : ℕ → Fin n → K) 0 := by
  intro t
  have e : ∀ u : Fin n, (0 : Matrix (Fin n) (Fin n) K) u = 0 := fun _ => rfl
  rw [e]
  split_ifs
  · rfl
  · rw [e, Matrix.zero_vecMul]
  · rfl

theorem spinRel_add {ρ ρ' : ℕ → Fin n → K} {S S' : Matrix (Fin n) (Fin n) K}
    (h : SpinRel c D ρ S) (h' : SpinRel c D ρ' S') : SpinRel c D (ρ + ρ') (S + S') := by
  intro t
  have e : ∀ u : Fin n, (S + S') u = S u + S' u := fun _ => rfl
  rw [e, h t, h' t]
  split_ifs
  · rfl
  · rw [e, Matrix.add_vecMul]
  · rw [add_zero]

theorem spinRel_smul (r : K) {ρ : ℕ → Fin n → K} {S : Matrix (Fin n) (Fin n) K}
    (h : SpinRel c D ρ S) : SpinRel c D (r • ρ) (r • S) := by
  intro t
  have e : ∀ u : Fin n, (r • S) u = r • S u := fun _ => rfl
  rw [e, h t]
  split_ifs
  · rfl
  · rw [e, Matrix.smul_vecMul]
  · rw [smul_zero]

theorem spinRel_sum {ι : Type*} (s : Finset ι) (ρ : ι → ℕ → Fin n → K)
    (S : ι → Matrix (Fin n) (Fin n) K) (h : ∀ i ∈ s, SpinRel c D (ρ i) (S i)) :
    SpinRel c D (∑ i ∈ s, ρ i) (∑ i ∈ s, S i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using spinRel_zero
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    exact spinRel_add (h i (Finset.mem_insert_self i s))
      (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

theorem spinRel_mul {ρ : ℕ → Fin n → K} {S M : Matrix (Fin n) (Fin n) K} (h : SpinRel c D ρ S)
    (hM : ∀ l, M * D l = D l * M) : SpinRel c D (fun i => ρ i ᵥ* M) (S * M) := by
  intro t
  have e : ∀ u : Fin n, (S * M) u = S u ᵥ* M := fun u => by
    funext j
    simp [Matrix.mul_apply, Matrix.vecMul, dotProduct]
  rw [e, h t]
  split_ifs
  · rfl
  · rw [e, Matrix.vecMul_vecMul, Matrix.vecMul_vecMul, hM]
  · simp

end CFSG.KC.BM.TwoAC

end
