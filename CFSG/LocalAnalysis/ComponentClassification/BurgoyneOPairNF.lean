module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneOEigen

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.O

open Matrix CFSG

variable {K : Type} [Field K] {d : ℕ}

structure PairFam (Rm A : Matrix (Fin d) (Fin d) K) {k : ℕ} (u : Fin k → Fin d → K) : Prop where
  ne : ∀ i, u i ⬝ᵥ Rm *ᵥ u i ≠ 0
  orth : ∀ i j, i ≠ j → u i ⬝ᵥ Rm *ᵥ u j = 0
  orthA : ∀ i j, i ≠ j → u i ⬝ᵥ Rm *ᵥ (A *ᵥ u j) = 0

section Bil

variable {Rm A : Matrix (Fin d) (Fin d) K} {c ε : K}

theorem dot_adj (hAR : Aᵀ * Rm = ε • (Rm * A)) (v w : Fin d → K) :
    (A *ᵥ v) ⬝ᵥ Rm *ᵥ w = ε * (v ⬝ᵥ Rm *ᵥ (A *ᵥ w)) := by
  have e1 : ∀ y, (A *ᵥ v) ⬝ᵥ y = v ⬝ᵥ (Aᵀ *ᵥ y) := fun y => by
    rw [dotProduct_mulVec, vecMul_transpose]
  rw [e1, mulVec_mulVec, hAR, smul_mulVec, ← mulVec_mulVec, dotProduct_smul, smul_eq_mul]

theorem mulVec_mulVec_self (hA2 : A * A = c • 1) (v : Fin d → K) : A *ᵥ (A *ᵥ v) = c • v := by
  rw [mulVec_mulVec, hA2, smul_mulVec, one_mulVec]

end Bil

theorem cramer_two {a b e p q : K} (hΔ : a * e - b ^ 2 ≠ 0) :
    p - ((p * e - q * b) / (a * e - b ^ 2) * a + (q * a - p * b) / (a * e - b ^ 2) * b) = 0 ∧
      q - ((p * e - q * b) / (a * e - b ^ 2) * b + (q * a - p * b) / (a * e - b ^ 2) * e) = 0 := by
  have h1 : (p * e - q * b) / (a * e - b ^ 2) * a + (q * a - p * b) / (a * e - b ^ 2) * b = p := by
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, div_eq_iff hΔ]
    ring
  have h2 : (p * e - q * b) / (a * e - b ^ 2) * b + (q * a - p * b) / (a * e - b ^ 2) * e = q := by
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, div_eq_iff hΔ]
    ring
  exact ⟨by rw [h1, sub_self], by rw [h2, sub_self]⟩

theorem exists_perp_of_lt (h2 : (2 : K) ≠ 0) {Rm : Matrix (Fin d) (Fin d) K} (hR : Rmᵀ = Rm)
    (hnd : ∀ v, (∀ w, v ⬝ᵥ Rm *ᵥ w = 0) → v = 0) {A : Matrix (Fin d) (Fin d) K} {c ε : K}
    (hA2 : A * A = c • 1) (hAR : Aᵀ * Rm = ε • (Rm * A))
    (hpair : ∀ u, u ⬝ᵥ Rm *ᵥ u ≠ 0 →
      (u ⬝ᵥ Rm *ᵥ u) * ((A *ᵥ u) ⬝ᵥ Rm *ᵥ (A *ᵥ u)) - (u ⬝ᵥ Rm *ᵥ (A *ᵥ u)) ^ 2 ≠ 0)
    {k : ℕ} {u : Fin k → Fin d → K} (hu : PairFam Rm A u) (hk : 2 * k < d) :
    ∃ v, v ⬝ᵥ Rm *ᵥ v ≠ 0 ∧ ∀ i, v ⬝ᵥ Rm *ᵥ u i = 0 ∧ v ⬝ᵥ Rm *ᵥ (A *ᵥ u i) = 0 := by
  by_contra hcon
  push Not at hcon
  have hba : ∀ i, (A *ᵥ u i) ⬝ᵥ Rm *ᵥ u i = u i ⬝ᵥ Rm *ᵥ (A *ᵥ u i) := fun i => dot_symm hR _ _
  have hAA : ∀ i j, i ≠ j → (A *ᵥ u i) ⬝ᵥ Rm *ᵥ (A *ᵥ u j) = 0 := by
    intro i j hij
    rw [dot_adj hAR, mulVec_mulVec_self hA2, mulVec_smul, dotProduct_smul, smul_eq_mul,
      hu.orth i j hij, mul_zero, mul_zero]
  have hAu : ∀ i j, i ≠ j → (A *ᵥ u i) ⬝ᵥ Rm *ᵥ u j = 0 := by
    intro i j hij
    rw [dot_symm hR, hu.orthA j i (Ne.symm hij)]
  obtain ⟨α, hα⟩ : ∃ α : (Fin d → K) → Fin k → K, ∀ w i, α w i =
      ((w ⬝ᵥ Rm *ᵥ u i) * ((A *ᵥ u i) ⬝ᵥ Rm *ᵥ (A *ᵥ u i)) -
        (w ⬝ᵥ Rm *ᵥ (A *ᵥ u i)) * (u i ⬝ᵥ Rm *ᵥ (A *ᵥ u i))) /
        ((u i ⬝ᵥ Rm *ᵥ u i) * ((A *ᵥ u i) ⬝ᵥ Rm *ᵥ (A *ᵥ u i)) -
          (u i ⬝ᵥ Rm *ᵥ (A *ᵥ u i)) ^ 2) := ⟨_, fun _ _ => rfl⟩
  obtain ⟨β, hβ⟩ : ∃ β : (Fin d → K) → Fin k → K, ∀ w i, β w i =
      ((w ⬝ᵥ Rm *ᵥ (A *ᵥ u i)) * (u i ⬝ᵥ Rm *ᵥ u i) -
        (w ⬝ᵥ Rm *ᵥ u i) * (u i ⬝ᵥ Rm *ᵥ (A *ᵥ u i))) /
        ((u i ⬝ᵥ Rm *ᵥ u i) * ((A *ᵥ u i) ⬝ᵥ Rm *ᵥ (A *ᵥ u i)) -
          (u i ⬝ᵥ Rm *ᵥ (A *ᵥ u i)) ^ 2) := ⟨_, fun _ _ => rfl⟩
  obtain ⟨π, hπ⟩ : ∃ π : (Fin d → K) → Fin d → K, ∀ w,
      π w = w - ∑ i, (α w i • u i + β w i • (A *ᵥ u i)) := ⟨_, fun _ => rfl⟩
  have hdot_sum : ∀ (w : Fin d → K) (z : Fin d → K),
      (∑ i, (α w i • u i + β w i • (A *ᵥ u i))) ⬝ᵥ Rm *ᵥ z =
        ∑ i, (α w i * (u i ⬝ᵥ Rm *ᵥ z) + β w i * ((A *ᵥ u i) ⬝ᵥ Rm *ᵥ z)) := by
    intro w z
    rw [sum_dotProduct]
    exact Finset.sum_congr rfl fun i _ => by rw [add_dotProduct, smul_dotProduct,
      smul_dotProduct, smul_eq_mul, smul_eq_mul]
  have hπu : ∀ w j, π w ⬝ᵥ Rm *ᵥ u j = 0 := by
    intro w j
    rw [hπ, sub_dotProduct, hdot_sum, Finset.sum_eq_single j (fun i _ hij => by
      rw [hu.orth i j hij, hAu i j hij, mul_zero, mul_zero, add_zero]) (by simp), hba, hα, hβ]
    exact (cramer_two (hpair (u j) (hu.ne j))).1
  have hπA : ∀ w j, π w ⬝ᵥ Rm *ᵥ (A *ᵥ u j) = 0 := by
    intro w j
    rw [hπ, sub_dotProduct, hdot_sum, Finset.sum_eq_single j (fun i _ hij => by
      rw [hu.orthA i j hij, hAA i j hij, mul_zero, mul_zero, add_zero]) (by simp), hα, hβ]
    exact (cramer_two (hpair (u j) (hu.ne j))).2
  have hU0 : ∀ x : Fin d → K, (∀ i, x ⬝ᵥ Rm *ᵥ u i = 0 ∧ x ⬝ᵥ Rm *ᵥ (A *ᵥ u i) = 0) →
      x ⬝ᵥ Rm *ᵥ x = 0 := by
    intro x hx
    by_contra h
    obtain ⟨i, hi⟩ := hcon x h
    exact hi (hx i).1 (hx i).2
  have hU : ∀ x y : Fin d → K, (∀ i, x ⬝ᵥ Rm *ᵥ u i = 0 ∧ x ⬝ᵥ Rm *ᵥ (A *ᵥ u i) = 0) →
      (∀ i, y ⬝ᵥ Rm *ᵥ u i = 0 ∧ y ⬝ᵥ Rm *ᵥ (A *ᵥ u i) = 0) → x ⬝ᵥ Rm *ᵥ y = 0 := by
    intro x y hx hy
    have hxy : ∀ i, (x + y) ⬝ᵥ Rm *ᵥ u i = 0 ∧ (x + y) ⬝ᵥ Rm *ᵥ (A *ᵥ u i) = 0 := fun i => by
      rw [add_dotProduct, add_dotProduct, (hx i).1, (hx i).2, (hy i).1, (hy i).2, add_zero]
      exact ⟨rfl, rfl⟩
    have e := hU0 _ hxy
    rw [add_dotProduct, mulVec_add, dotProduct_add, dotProduct_add, hU0 x hx,
      hU0 y hy, dot_symm hR x y] at e
    have : (2 : K) * (x ⬝ᵥ Rm *ᵥ y) = 0 := by linear_combination e
    exact (mul_eq_zero.1 this).resolve_left h2
  have hπU : ∀ w, ∀ i, π w ⬝ᵥ Rm *ᵥ u i = 0 ∧ π w ⬝ᵥ Rm *ᵥ (A *ᵥ u i) = 0 :=
    fun w i => ⟨hπu w i, hπA w i⟩
  have hπ0 : ∀ w, π w = 0 := by
    intro w
    refine hnd _ fun z => ?_
    have hz : z = π z + ∑ i, (α z i • u i + β z i • (A *ᵥ u i)) := by
      rw [hπ, sub_add_cancel]
    rw [hz, mulVec_add, dotProduct_add, hU _ _ (hπU w) (hπU z), zero_add, mulVec_sum,
      dotProduct_sum]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [mulVec_add, mulVec_smul, mulVec_smul, dotProduct_add, dotProduct_smul, dotProduct_smul,
      (hπU w i).1, (hπU w i).2, smul_zero, smul_zero, add_zero]
  set f : Fin k ⊕ Fin k → Fin d → K := Sum.elim u fun i => A *ᵥ u i with hf
  have htop : Submodule.span K (Set.range f) = ⊤ := by
    refine eq_top_iff.2 fun w _ => ?_
    have hw : w = ∑ i, (α w i • u i + β w i • (A *ᵥ u i)) := by
      have := hπ0 w
      rw [hπ, sub_eq_zero] at this
      exact this
    rw [hw]
    refine Submodule.sum_mem _ fun i _ => Submodule.add_mem _ ?_ ?_
    · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨Sum.inl i, rfl⟩)
    · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨Sum.inr i, rfl⟩)
  have hle := finrank_range_le_card (R := K) f
  rw [Set.finrank, htop, finrank_top, Module.finrank_fin_fun, Fintype.card_sum,
    Fintype.card_fin] at hle
  omega

theorem exists_pairFam (h2 : (2 : K) ≠ 0) {Rm : Matrix (Fin d) (Fin d) K} (hR : Rmᵀ = Rm)
    (hnd : ∀ v, (∀ w, v ⬝ᵥ Rm *ᵥ w = 0) → v = 0) {A : Matrix (Fin d) (Fin d) K} {c ε : K}
    (hA2 : A * A = c • 1) (hAR : Aᵀ * Rm = ε • (Rm * A)) (hε : ε * ε = 1)
    (hpair : ∀ u, u ⬝ᵥ Rm *ᵥ u ≠ 0 →
      (u ⬝ᵥ Rm *ᵥ u) * ((A *ᵥ u) ⬝ᵥ Rm *ᵥ (A *ᵥ u)) - (u ⬝ᵥ Rm *ᵥ (A *ᵥ u)) ^ 2 ≠ 0) :
    ∀ k, 2 * k ≤ d → ∃ u : Fin k → Fin d → K, PairFam Rm A u := by
  intro k
  induction k with
  | zero => exact fun _ => ⟨Fin.elim0, ⟨fun i => i.elim0, fun i => i.elim0, fun i => i.elim0⟩⟩
  | succ k ih =>
    intro hk
    obtain ⟨u, hu⟩ := ih (by omega)
    obtain ⟨v, hv, hvu⟩ := exists_perp_of_lt h2 hR hnd hA2 hAR hpair hu (by omega)
    have hvA : ∀ i, u i ⬝ᵥ Rm *ᵥ (A *ᵥ v) = 0 := by
      intro i
      have e := dot_adj hAR (u i) v
      rw [dot_symm hR, (hvu i).2] at e
      have : u i ⬝ᵥ Rm *ᵥ (A *ᵥ v) = ε * (ε * (u i ⬝ᵥ Rm *ᵥ (A *ᵥ v))) := by
        rw [← mul_assoc, hε, one_mul]
      rw [this, ← e, mul_zero]
    refine ⟨Fin.cons v u, ⟨fun i => ?_, fun i j hij => ?_, fun i j hij => ?_⟩⟩
    · cases i using Fin.cases with
      | zero => simpa using hv
      | succ i => simpa using hu.ne i
    · cases i using Fin.cases <;> cases j using Fin.cases
      · exact absurd rfl hij
      · simpa using (hvu _).1
      · simp only [Fin.cons_succ, Fin.cons_zero]
        rw [dot_symm hR]
        exact (hvu _).1
      · simpa using hu.orth _ _ (fun h => hij (by rw [h]))
    · cases i using Fin.cases <;> cases j using Fin.cases
      · exact absurd rfl hij
      · simpa using (hvu _).2
      · simpa using hvA _
      · simpa using hu.orthA _ _ (fun h => hij (by rw [h]))

end CFSG.ComponentClassification.Burgoyne.O
