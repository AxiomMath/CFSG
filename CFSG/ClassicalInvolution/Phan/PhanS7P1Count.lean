module

public import CFSG.ClassicalInvolution.Phan.PhanS5D1Basic
public import CFSG.ClassicalInvolution.Phan.PhanS5D2Conic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Data.Int.Star

public section

namespace CFSG.ClassicalInvolution.PhanB3.S.Std.P

open CFSG.ClassicalInvolution.PhanB3.S.Std CFSG.ClassicalInvolution.PhanB3.S.Std.D Polynomial

variable {K : Type} [Field K] (M : Model K)

theorem sesq_zero_left {G : Vec K → Vec K → K} (hG : Sesq M G) (y : Vec K) : G 0 y = 0 := by
  have := hG.smul_left 0 0 y
  simpa using this

theorem sesq_zero_right {G : Vec K → Vec K → K} (hG : Sesq M G) (x : Vec K) : G x 0 = 0 := by
  have := hG.smul_right 0 x 0
  simpa using this

variable {M}

theorem natDegree_conicPoly_pencil_le {G : Vec K → Vec K → K} (hG : Sesq M G) (c₀ c₁ : Vec K) :
    (conicPoly (M := M) G c₀ c₁ 0).natDegree ≤ M.q + 1 := by
  refine natDegree_sum_le_of_forall_le _ _ fun i _ => ?_
  refine natDegree_sum_le_of_forall_le _ _ fun j _ => ?_
  by_cases hi : (i : ℕ) = 2
  · have h0 : G (cs c₀ c₁ 0 i) (cs c₀ c₁ 0 j) = 0 := by
      have : i = 2 := Fin.ext hi
      subst this
      rw [cs_two]
      exact sesq_zero_left M hG _
    rw [h0]
    simp
  by_cases hj : (j : ℕ) = 2
  · have h0 : G (cs c₀ c₁ 0 i) (cs c₀ c₁ 0 j) = 0 := by
      have : j = 2 := Fin.ext hj
      subst this
      rw [cs_two]
      exact sesq_zero_right M hG _
    rw [h0]
    simp
  refine (natDegree_C_mul_X_pow_le _ _).trans ?_
  have hi' : (i : ℕ) ≤ 1 := by have := i.2; omega
  have hj' : (j : ℕ) ≤ 1 := by have := j.2; omega
  have : M.q * (j : ℕ) ≤ M.q * 1 := Nat.mul_le_mul_left _ hj'
  omega

variable [Finite K]

theorem card_zeros_pencil_le (hq : 3 ≤ M.q) {G : Vec K → Vec K → K} (hG : Sesq M G)
    {c₀ c₁ : Vec K} (h : ∃ i j : Fin 3, G (cs c₀ c₁ 0 i) (cs c₀ c₁ 0 j) ≠ 0) :
    Nat.card {μ : K // G (conicPt c₀ c₁ 0 μ) (conicPt c₀ c₁ 0 μ) = 0} ≤ M.q + 1 := by
  classical
  have := Fintype.ofFinite K
  have hP := conicPoly_ne_zero (M := M) hq h
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  refine (Polynomial.card_le_degree_of_subset_roots (p := conicPoly (M := M) G c₀ c₁ 0) ?_).trans
    (natDegree_conicPoly_pencil_le hG c₀ c₁)
  intro μ hμ
  rw [Finset.mem_val, Finset.mem_filter] at hμ
  rw [mem_roots hP, IsRoot.def, eval_conicPoly, ← hG.conic_eval]
  exact hμ.2

theorem exists_nonzero_of_card {ι : Type} [Fintype ι] {B : ℕ} (val : ι → K → K)
    (hB : ∀ i, Nat.card {μ : K // val i μ = 0} ≤ B) (hlt : Fintype.card ι * B < Nat.card K) :
    ∃ μ : K, ∀ i, val i μ ≠ 0 := by
  classical
  have := Fintype.ofFinite K
  by_contra hcon
  push Not at hcon
  have hsub : (Finset.univ : Finset K) ⊆
      Finset.univ.biUnion fun i : ι => Finset.univ.filter fun μ => val i μ = 0 := by
    intro μ _
    obtain ⟨i, hi⟩ := hcon μ
    exact Finset.mem_biUnion.2 ⟨i, Finset.mem_univ _, by simpa using hi⟩
  have h1 := (Finset.card_le_card hsub).trans Finset.card_biUnion_le
  have h2 : ∀ i, (Finset.univ.filter fun μ => val i μ = 0).card ≤ B := fun i => by
    have := hB i
    rwa [Nat.card_eq_fintype_card, Fintype.card_subtype] at this
  have h3 : ∑ i : ι, (Finset.univ.filter fun μ => val i μ = 0).card ≤ ∑ _i : ι, B :=
    Finset.sum_le_sum fun i _ => h2 i
  rw [Finset.card_univ, ← Nat.card_eq_fintype_card] at h1
  simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul] at h3
  omega

theorem exists_mu_conic_three (hq : 7 ≤ M.q) {G₁ G₂ G₃ : Vec K → Vec K → K} (h₁ : Sesq M G₁)
    (h₂ : Sesq M G₂) (h₃ : Sesq M G₃) {c₀ c₁ c₂ : Vec K}
    (w₁ : ∃ i j : Fin 3, G₁ (cs c₀ c₁ c₂ i) (cs c₀ c₁ c₂ j) ≠ 0)
    (w₂ : ∃ i j : Fin 3, G₂ (cs c₀ c₁ c₂ i) (cs c₀ c₁ c₂ j) ≠ 0)
    (w₃ : ∃ i j : Fin 3, G₃ (cs c₀ c₁ c₂ i) (cs c₀ c₁ c₂ j) ≠ 0) :
    ∃ μ : K, G₁ (conicPt c₀ c₁ c₂ μ) (conicPt c₀ c₁ c₂ μ) ≠ 0 ∧
      G₂ (conicPt c₀ c₁ c₂ μ) (conicPt c₀ c₁ c₂ μ) ≠ 0 ∧
      G₃ (conicPt c₀ c₁ c₂ μ) (conicPt c₀ c₁ c₂ μ) ≠ 0 := by
  have hcard : 3 * (2 * M.q + 2) < Nat.card K := by
    rw [M.card_K]
    nlinarith
  obtain ⟨μ, hμ⟩ := exists_nonzero_of_card (ι := Fin 3) (B := 2 * M.q + 2)
    (fun i μ => ![G₁, G₂, G₃] i (conicPt c₀ c₁ c₂ μ) (conicPt c₀ c₁ c₂ μ)) (fun i => by
      fin_cases i
      · exact card_zeros_le (by omega) h₁ w₁
      · exact card_zeros_le (by omega) h₂ w₂
      · exact card_zeros_le (by omega) h₃ w₃) (by simpa using hcard)
  exact ⟨μ, hμ 0, hμ 1, hμ 2⟩

theorem exists_mu_pencil_four (hq : 5 ≤ M.q) {G₁ G₂ G₃ G₄ : Vec K → Vec K → K}
    (h₁ : Sesq M G₁) (h₂ : Sesq M G₂) (h₃ : Sesq M G₃) (h₄ : Sesq M G₄) {c₀ c₁ : Vec K}
    (w₁ : ∃ i j : Fin 3, G₁ (cs c₀ c₁ 0 i) (cs c₀ c₁ 0 j) ≠ 0)
    (w₂ : ∃ i j : Fin 3, G₂ (cs c₀ c₁ 0 i) (cs c₀ c₁ 0 j) ≠ 0)
    (w₃ : ∃ i j : Fin 3, G₃ (cs c₀ c₁ 0 i) (cs c₀ c₁ 0 j) ≠ 0)
    (w₄ : ∃ i j : Fin 3, G₄ (cs c₀ c₁ 0 i) (cs c₀ c₁ 0 j) ≠ 0) :
    ∃ μ : K, G₁ (conicPt c₀ c₁ 0 μ) (conicPt c₀ c₁ 0 μ) ≠ 0 ∧
      G₂ (conicPt c₀ c₁ 0 μ) (conicPt c₀ c₁ 0 μ) ≠ 0 ∧
      G₃ (conicPt c₀ c₁ 0 μ) (conicPt c₀ c₁ 0 μ) ≠ 0 ∧
      G₄ (conicPt c₀ c₁ 0 μ) (conicPt c₀ c₁ 0 μ) ≠ 0 := by
  have hcard : 4 * (M.q + 1) < Nat.card K := by
    rw [M.card_K]
    nlinarith
  obtain ⟨μ, hμ⟩ := exists_nonzero_of_card (ι := Fin 4) (B := M.q + 1)
    (fun i μ => ![G₁, G₂, G₃, G₄] i (conicPt c₀ c₁ 0 μ) (conicPt c₀ c₁ 0 μ)) (fun i => by
      fin_cases i
      · exact card_zeros_pencil_le (by omega) h₁ w₁
      · exact card_zeros_pencil_le (by omega) h₂ w₂
      · exact card_zeros_pencil_le (by omega) h₃ w₃
      · exact card_zeros_pencil_le (by omega) h₄ w₄) (by simpa using hcard)
  exact ⟨μ, hμ 0, hμ 1, hμ 2, hμ 3⟩

end CFSG.ClassicalInvolution.PhanB3.S.Std.P
