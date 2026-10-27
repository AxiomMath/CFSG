module

public import Mathlib.Algebra.Group.Subgroup.Finite
public import Mathlib.Algebra.Group.Subgroup.Pointwise
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Group

public section

namespace CFSG.LocalAnalysis.ComponentInitial

variable {G : Type*} [Group G]

theorem inv_eq_sq_of_pow_three {x : G} (hx : x ^ 3 = 1) : x⁻¹ = x ^ 2 := by
  rw [inv_eq_iff_mul_eq_one, ← pow_succ', hx]

theorem mul_eq_inv_mul_inv_of_sq {x y : G} (h : (x * y) ^ 2 = 1) : x * y = y⁻¹ * x⁻¹ := by
  rw [← mul_inv_rev, eq_inv_iff_mul_eq_one, ← sq, h]

theorem sq_mul_comm_eq_one {x y : G} (h : (x * y) ^ 2 = 1) : (y * x) ^ 2 = 1 := by
  have : (y * x) ^ 2 = y * (x * y) ^ 2 * y⁻¹ := by
    rw [sq, sq]
    group
  rw [this, h, mul_one, mul_inv_cancel]

@[expose] def carmichaelRep {m : ℕ} (a : Fin m → G) (b : G) : Fin 3 ⊕ Fin m → G
  | .inl 0 => 1
  | .inl 1 => b
  | .inl 2 => b ^ 2
  | .inr i => a i * b ^ 2

theorem exists_mul_carmichaelRep_eq {m : ℕ} (a : Fin m → G) (b : G) (ha : ∀ i, a i ^ 3 = 1)
    (hb : b ^ 3 = 1) (hab : ∀ i, (a i * b) ^ 2 = 1) (haa : ∀ i j, i ≠ j → (a i * a j) ^ 2 = 1)
    (x : G) (hx : x = b ∨ ∃ j, x = a j) (k : Fin 3 ⊕ Fin m) :
    ∃ (k' : Fin 3 ⊕ Fin m), ∃ h ∈ Subgroup.closure (Set.range a),
      x * carmichaelRep a b k = carmichaelRep a b k' * h := by
  have hmem : ∀ i, a i ∈ Subgroup.closure (Set.range a) := fun i =>
    Subgroup.subset_closure (Set.mem_range_self i)
  have h1 : ∀ j, a j * b = b ^ 2 * a j ^ 2 := fun j => by
    rw [mul_eq_inv_mul_inv_of_sq (hab j), inv_eq_sq_of_pow_three hb,
      inv_eq_sq_of_pow_three (ha j)]
  have h2 : ∀ j, b * a j = a j ^ 2 * b ^ 2 := fun j => by
    rw [mul_eq_inv_mul_inv_of_sq (sq_mul_comm_eq_one (hab j)), inv_eq_sq_of_pow_three hb,
      inv_eq_sq_of_pow_three (ha j)]
  have h3 : ∀ i, b ^ 2 * a i ^ 2 = a i * b := fun i => (h1 i).symm
  rcases hx with rfl | ⟨j, rfl⟩
  · rcases k with k | i
    · fin_cases k
      · exact ⟨.inl 1, 1, Subgroup.one_mem _, by simp [carmichaelRep]⟩
      · exact ⟨.inl 2, 1, Subgroup.one_mem _, by simp [carmichaelRep, sq]⟩
      · exact ⟨.inl 0, 1, Subgroup.one_mem _, by
          simp only [carmichaelRep, mul_one]
          rw [← pow_succ', hb]⟩
    ·
      refine ⟨.inr i, a i ^ 2, Subgroup.pow_mem _ (hmem i) _, ?_⟩
      simp only [carmichaelRep]
      calc x * (a i * x ^ 2) = (x * a i) * x ^ 2 := by group
        _ = a i ^ 2 * x ^ 2 * x ^ 2 := by rw [h2]
        _ = a i ^ 2 * x * x ^ 3 := by group
        _ = a i * (x ^ 2 * a i ^ 2) := by
          rw [hb, h3]
          simp only [sq, mul_assoc, mul_one]
        _ = a i * x ^ 2 * a i ^ 2 := by group
  · rcases k with k | i
    · fin_cases k
      · exact ⟨.inl 0, a j, hmem j, by simp [carmichaelRep]⟩
      · exact ⟨.inl 2, a j ^ 2, Subgroup.pow_mem _ (hmem j) _, by
          simp only [carmichaelRep]
          exact h1 j⟩
      · exact ⟨.inr j, 1, Subgroup.one_mem _, by simp [carmichaelRep]⟩
    · rcases eq_or_ne i j with rfl | hij
      ·
        refine ⟨.inl 1, a i, hmem i, ?_⟩
        simp only [carmichaelRep]
        calc a i * (a i * b ^ 2) = a i ^ 2 * b ^ 2 := by simp only [sq, mul_assoc]
          _ = b * a i := (h2 i).symm
      ·
        refine ⟨.inr i, a i ^ 2 * a j, Subgroup.mul_mem _ (Subgroup.pow_mem _ (hmem i) _)
          (hmem j), ?_⟩
        simp only [carmichaelRep]
        have h4 : a j * a i = a i ^ 2 * a j ^ 2 := by
          rw [mul_eq_inv_mul_inv_of_sq (haa j i (Ne.symm hij)), inv_eq_sq_of_pow_three (ha i),
            inv_eq_sq_of_pow_three (ha j)]
        calc a j * (a i * b ^ 2) = (a j * a i) * b ^ 2 := by group
          _ = a i ^ 2 * (a j ^ 2 * b ^ 2) := by rw [h4]; group
          _ = a i ^ 2 * (b * a j) := by rw [h2]
          _ = a i * (a i * b) * a j := by simp only [sq, mul_assoc]
          _ = a i * (b ^ 2 * a i ^ 2) * a j := by rw [h3]
          _ = a i * b ^ 2 * (a i ^ 2 * a j) := by group

theorem card_closure_le_of_carmichael [Finite G] :
    ∀ (m : ℕ) (a : Fin m → G), (∀ i, a i ^ 3 = 1) → (∀ i j, i ≠ j → (a i * a j) ^ 2 = 1) →
      Nat.card (Subgroup.closure (Set.range a)) ≤ (m + 2).factorial / 2 := by
  intro m
  induction m with
  | zero =>
    intro a _ _
    rw [Set.range_eq_empty, Subgroup.closure_empty, Subgroup.card_bot]
    simp
  | succ m ih =>
    intro a ha haa
    set b := a (Fin.last m)
    set a' : Fin m → G := fun i => a i.castSucc
    set H := Subgroup.closure (Set.range a')
    have hH := ih a' (fun i => ha _) fun i j hij =>
      haa _ _ (fun h => hij (Fin.castSucc_injective _ h))
    have hHle : H ≤ Subgroup.closure (Set.range a) :=
      Subgroup.closure_mono (Set.range_subset_iff.mpr fun i => ⟨i.castSucc, rfl⟩)
    have hrep : ∀ k, carmichaelRep a' b k ∈ Subgroup.closure (Set.range a) := by
      have hb : b ∈ Subgroup.closure (Set.range a) := Subgroup.subset_closure ⟨_, rfl⟩
      rintro (k | i)
      · fin_cases k
        · exact Subgroup.one_mem _
        · exact hb
        · exact Subgroup.pow_mem _ hb _
      · exact Subgroup.mul_mem _ (Subgroup.subset_closure ⟨_, rfl⟩) (Subgroup.pow_mem _ hb _)
    have hcov : ∀ g ∈ Subgroup.closure (Set.range a),
        ∃ k, ∃ h ∈ H, g = carmichaelRep a' b k * h := by
      have hstep : ∀ x ∈ Set.range a, ∀ g, (∃ k, ∃ h ∈ H, g = carmichaelRep a' b k * h) →
          ∃ k, ∃ h ∈ H, x * g = carmichaelRep a' b k * h := by
        rintro x ⟨j, rfl⟩ g ⟨k, h, hh, rfl⟩
        have hx : a j = b ∨ ∃ i, a j = a' i := by
          cases j using Fin.lastCases with
          | last => exact Or.inl rfl
          | cast i => exact Or.inr ⟨i, rfl⟩
        obtain ⟨k', h', hh', he⟩ := exists_mul_carmichaelRep_eq a' b (fun i => ha _) (ha _)
          (fun i => haa _ _ (Fin.castSucc_ne_last i)) (fun i j hij => haa _ _
            (fun h => hij (Fin.castSucc_injective _ h))) (a j) hx k
        exact ⟨k', h' * h, H.mul_mem hh' hh, by rw [← mul_assoc, he, mul_assoc]⟩
      intro g hg
      induction hg using Subgroup.closure_induction_left with
      | one => exact ⟨.inl 0, 1, H.one_mem, by simp [carmichaelRep]⟩
      | mul_left x hx g _ ih => exact hstep x hx g ih
      | inv_mul_cancel x hx g _ ih =>
        obtain ⟨j, rfl⟩ := hx
        rw [inv_eq_sq_of_pow_three (ha j), sq, mul_assoc]
        exact hstep _ ⟨j, rfl⟩ _ (hstep _ ⟨j, rfl⟩ g ih)
    let f : (Fin 3 ⊕ Fin m) × H → Subgroup.closure (Set.range a) := fun p =>
      ⟨carmichaelRep a' b p.1 * p.2, Subgroup.mul_mem _ (hrep _) (hHle p.2.2)⟩
    have hf : Function.Surjective f := by
      rintro ⟨g, hg⟩
      obtain ⟨k, h, hh, rfl⟩ := hcov g hg
      exact ⟨(k, ⟨h, hh⟩), rfl⟩
    have hcard := Nat.card_le_card_of_surjective f hf
    rw [Nat.card_prod, Nat.card_sum, Nat.card_eq_fintype_card (α := Fin 3),
      Nat.card_eq_fintype_card (α := Fin m), Fintype.card_fin, Fintype.card_fin] at hcard
    have h2 : 2 ∣ (m + 2).factorial := Nat.dvd_factorial (by norm_num) (by omega)
    calc Nat.card (Subgroup.closure (Set.range a)) ≤ (3 + m) * Nat.card H := hcard
      _ ≤ (3 + m) * ((m + 2).factorial / 2) := Nat.mul_le_mul_left _ hH
      _ = (m + 1 + 2).factorial / 2 := by
        have : (m + 1 + 2).factorial = (m + 3) * (m + 2).factorial := Nat.factorial_succ (m + 2)
        rw [this, Nat.mul_div_assoc _ h2, Nat.add_comm 3 m]

end CFSG.LocalAnalysis.ComponentInitial
