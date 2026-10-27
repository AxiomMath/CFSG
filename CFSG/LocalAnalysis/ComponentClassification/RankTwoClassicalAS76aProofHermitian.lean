module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofSquareZero
public import Mathlib.LinearAlgebra.Matrix.SchurComplement

public section

namespace CFSG.ComponentClassification.RankTwoClassical

open Module Matrix
open scoped Matrix

variable {ι K : Type} [Fintype ι] [Field K] (σ : K →+* K)

@[expose] def hform (u v : ι → K) : K := (σ ∘ u) ⬝ᵥ v

@[expose] def adjM (A : Matrix ι ι K) : Matrix ι ι K := (A.map σ)ᵀ

variable {σ}

theorem hform_add_left (u u' v : ι → K) : hform σ (u + u') v = hform σ u v + hform σ u' v := by
  simp only [hform]
  rw [show (σ ∘ (u + u')) = σ ∘ u + σ ∘ u' by ext i; simp, add_dotProduct]

theorem hform_add_right (u v v' : ι → K) : hform σ u (v + v') = hform σ u v + hform σ u v' :=
  dotProduct_add _ _ _

theorem hform_sub_right (u v v' : ι → K) : hform σ u (v - v') = hform σ u v - hform σ u v' :=
  dotProduct_sub _ _ _

theorem hform_sub_left (u u' v : ι → K) : hform σ (u - u') v = hform σ u v - hform σ u' v := by
  simp only [hform]
  rw [show (σ ∘ (u - u')) = σ ∘ u - σ ∘ u' by ext i; simp, sub_dotProduct]

theorem hform_smul_left (c : K) (u v : ι → K) : hform σ (c • u) v = σ c * hform σ u v := by
  simp only [hform]
  rw [show (σ ∘ (c • u)) = σ c • (σ ∘ u) by ext i; simp, smul_dotProduct, smul_eq_mul]

theorem hform_smul_right (c : K) (u v : ι → K) : hform σ u (c • v) = c * hform σ u v := by
  simp only [hform, dotProduct_smul, smul_eq_mul]

theorem hform_zero_left (v : ι → K) : hform σ 0 v = 0 := by
  simp [hform]

theorem hform_zero_right (u : ι → K) : hform σ u 0 = 0 := by
  simp [hform]

theorem hform_sum_right {α : Type*} (s : Finset α) (u : ι → K) (v : α → ι → K) :
    hform σ u (∑ a ∈ s, v a) = ∑ a ∈ s, hform σ u (v a) := by
  simp only [hform, dotProduct_sum]

theorem hform_sum_left {α : Type*} (s : Finset α) (u : α → ι → K) (v : ι → K) :
    hform σ (∑ a ∈ s, u a) v = ∑ a ∈ s, hform σ (u a) v := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [hform_zero_left]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, hform_add_left, ih]

theorem hform_mulVec (A : Matrix ι ι K) (u v : ι → K) :
    hform σ (A *ᵥ u) v = hform σ u (adjM σ A *ᵥ v) := by
  simp only [hform, adjM, dotProduct, mulVec, Function.comp, map_sum, map_mul,
    Finset.sum_mul, Finset.mul_sum, transpose_apply, map_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

variable (hσ : ∀ x, σ (σ x) = x)
include hσ

theorem hform_comm (u v : ι → K) : hform σ v u = σ (hform σ u v) := by
  simp only [hform, dotProduct, Function.comp, map_sum, map_mul, hσ]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

omit [Fintype ι] in
theorem adjM_adjM (A : Matrix ι ι K) : adjM σ (adjM σ A) = A := by
  ext i j
  simp [adjM, hσ]

theorem hform_mulVec_right (A : Matrix ι ι K) (u v : ι → K) :
    hform σ u (A *ᵥ v) = hform σ (adjM σ A *ᵥ u) v := by
  rw [hform_mulVec, adjM_adjM hσ]

omit hσ in
theorem eq_zero_of_hform_left [DecidableEq ι] {v : ι → K} (h : ∀ u, hform σ u v = 0) : v = 0 := by
  ext i
  have := h (Pi.single i 1)
  simp only [hform, dotProduct, Function.comp, Pi.single_apply] at this
  simpa [apply_ite σ, map_one, map_zero] using this

theorem eq_zero_of_hform_right [DecidableEq ι] {u : ι → K} (h : ∀ v, hform σ u v = 0) : u = 0 := by
  refine eq_zero_of_hform_left (σ := σ) fun v => ?_
  rw [hform_comm hσ, h v, map_zero]

omit hσ

theorem adjM_mul (A B : Matrix ι ι K) : adjM σ (A * B) = adjM σ B * adjM σ A := by
  rw [adjM, adjM, adjM, Matrix.map_mul, transpose_mul]

omit [Fintype ι] in
theorem adjM_add (A B : Matrix ι ι K) : adjM σ (A + B) = adjM σ A + adjM σ B := by
  ext i j
  simp [adjM]

omit [Fintype ι] in
theorem adjM_sub (A B : Matrix ι ι K) : adjM σ (A - B) = adjM σ A - adjM σ B := by
  ext i j
  simp [adjM]

omit [Fintype ι] in
theorem adjM_one [DecidableEq ι] : adjM σ (1 : Matrix ι ι K) = 1 := by
  simp [adjM]

omit [Fintype ι] in
theorem adjM_smul (c : K) (A : Matrix ι ι K) : adjM σ (c • A) = σ c • adjM σ A := by
  ext i j
  simp [adjM]

omit [Fintype ι] in
theorem adjM_vecMulVec (a b : ι → K) :
    adjM σ (vecMulVec a b) = vecMulVec (σ ∘ b) (σ ∘ a) := by
  ext i j
  simp [adjM, vecMulVec_apply, mul_comm]

omit [Fintype ι] in
theorem adjM_sum {α : Type*} (s : Finset α) (A : α → Matrix ι ι K) :
    adjM σ (∑ a ∈ s, A a) = ∑ a ∈ s, adjM σ (A a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [adjM]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, adjM_add, ih]

theorem vecMulVec_mulVec' (a b v : ι → K) : vecMulVec a b *ᵥ v = (b ⬝ᵥ v) • a := by
  rw [vecMulVec_mulVec, op_smul_eq_smul]

section Proj

variable {k : ℕ}

variable (σ) in
@[expose] def projP (u w : Fin k → ι → K) : Matrix ι ι K := ∑ i, vecMulVec (u i) (σ ∘ w i)

theorem projP_mulVec (u w : Fin k → ι → K) (v : ι → K) :
    projP σ u w *ᵥ v = ∑ i, hform σ (w i) v • u i := by
  rw [projP, Matrix.sum_mulVec]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [vecMulVec_mulVec']
  rfl

omit [Fintype ι] in
theorem adjM_projP (hσ : ∀ x, σ (σ x) = x) (u w : Fin k → ι → K) :
    adjM σ (projP σ u w) = projP σ w u := by
  rw [projP, adjM_sum, projP]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [adjM_vecMulVec]
  congr 1
  ext a
  simp [hσ]

end Proj

omit [Fintype ι] in
theorem rank_eq_finrank_range [Fintype ι] (A : Matrix ι ι K) :
    A.rank = finrank K (LinearMap.range A.mulVecLin) := rfl

theorem rank_eq_sub_one_of_split {N E₁ E₂ : Matrix ι ι K} (hsum : N = E₁ + E₂)
    (h1 : E₁.rank = 1) (hker : ∀ v, N *ᵥ v = 0 → E₂ *ᵥ v = 0) {x₀ : ι → K}
    (hx₂ : E₂ *ᵥ x₀ = 0) (hxN : N *ᵥ x₀ ≠ 0) : E₂.rank = N.rank - 1 := by
  rw [rank_eq_finrank_range, rank_eq_finrank_range] at *
  have hle : LinearMap.range N.mulVecLin ≤
      LinearMap.range E₁.mulVecLin ⊔ LinearMap.range E₂.mulVecLin := by
    rintro _ ⟨v, rfl⟩
    rw [hsum, Matrix.mulVecLin_add, LinearMap.add_apply]
    exact Submodule.add_mem_sup ⟨v, rfl⟩ ⟨v, rfl⟩
  have h2 := (Submodule.finrank_mono hle).trans
    (Submodule.finrank_add_le_finrank_add_finrank _ _)
  have hkle : LinearMap.ker N.mulVecLin ⊔ (K ∙ x₀) ≤ LinearMap.ker E₂.mulVecLin := by
    refine sup_le (fun v hv => hker v hv) ?_
    rw [Submodule.span_singleton_le_iff_mem]
    exact hx₂
  have hdis : LinearMap.ker N.mulVecLin ⊓ (K ∙ x₀) = ⊥ := by
    rw [eq_bot_iff]
    intro v hv
    obtain ⟨hvN, hvx⟩ := Submodule.mem_inf.mp hv
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hvx
    have h3 : c • (N *ᵥ x₀) = 0 := by
      have : N.mulVecLin (c • x₀) = 0 := hvN
      rwa [map_smul] at this
    rcases smul_eq_zero.mp h3 with h4 | h4
    · rw [h4, zero_smul]; exact Submodule.zero_mem _
    · exact absurd h4 hxN
  have h5 := Submodule.finrank_sup_add_finrank_inf_eq (LinearMap.ker N.mulVecLin) (K ∙ x₀)
  rw [hdis, finrank_bot, add_zero, finrank_span_singleton (fun h => hxN (by
    rw [h, Matrix.mulVec_zero]))] at h5
  have h6 := Submodule.finrank_mono hkle
  have h7 := LinearMap.finrank_range_add_finrank_ker N.mulVecLin
  have h8 := LinearMap.finrank_range_add_finrank_ker E₂.mulVecLin
  omega

section Dual

variable (hσ : ∀ x, σ (σ x) = x)
include hσ

theorem exists_hform_dual {ρ : Type} [Fintype ρ] [DecidableEq ρ] (g : ρ → ι → K)
    (hg : LinearIndependent K g) :
    ∃ w : ρ → ι → K, ∀ r s, hform σ (g r) (w s) = if r = s then 1 else 0 := by
  classical
  let R : Matrix ρ ι K := fun r a => σ (g r a)
  have hR : ∀ w r, (R *ᵥ w) r = hform σ (g r) w := fun w r => rfl
  have hrow : LinearIndependent K R.row := by
    rw [linearIndependent_iff']
    intro s c hc r hr
    have h1 : ∑ i ∈ s, σ (c i) • g i = 0 := by
      ext a
      have h2 := congrArg σ (congrFun hc a)
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, map_sum, map_mul,
        map_zero] at h2 ⊢
      rw [← h2]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp [R, Matrix.row, hσ]
    have h3 := (linearIndependent_iff'.mp hg) s (fun i => σ (c i)) h1 r hr
    have h4 := congrArg σ h3
    rwa [hσ, map_zero] at h4
  have hrank : R.rank = Fintype.card ρ := by
    rw [Matrix.rank_eq_finrank_span_row, finrank_span_eq_card hrow]
  have htop : LinearMap.range R.mulVecLin = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    have h1 : finrank K (LinearMap.range R.mulVecLin) = Fintype.card ρ := hrank
    rw [h1, Module.finrank_fintype_fun_eq_card]
  choose w hw using fun s : ρ => (htop ▸ Submodule.mem_top : Pi.single s (1 : K) ∈
    LinearMap.range R.mulVecLin)
  refine ⟨w, fun r s => ?_⟩
  rw [← hR, show R *ᵥ w s = R.mulVecLin (w s) from rfl, hw s, Pi.single_apply]

theorem exists_isotropic_dual [CharP K 2] (htr : ∀ c, σ c = c → ∃ d, d + σ d = c) {k : ℕ}
    (u u' : Fin k → ι → K) (huu : ∀ i j, hform σ (u i) (u j) = 0)
    (hdual : ∀ i j, hform σ (u i) (u' j) = if i = j then 1 else 0) :
    ∃ u'' : Fin k → ι → K, (∀ i j, hform σ (u i) (u'' j) = if i = j then 1 else 0) ∧
      (∀ i j, hform σ (u'' i) (u'' j) = 0) ∧
      ∀ j, ∃ c : Fin k → K, u'' j = u' j + ∑ m, c m • u m := by
  classical
  set G : Fin k → Fin k → K := fun i j => hform σ (u' i) (u' j) with hG
  have hGσ : ∀ i j, σ (G i j) = G j i := fun i j => by
    rw [hG]
    exact (hform_comm hσ _ _).symm
  choose d hd using fun i => htr (-G i i) (by rw [map_neg, hGσ])
  let c : Fin k → Fin k → K := fun j i => if i < j then -G i j else if i = j then d i else 0
  refine ⟨fun j => u' j + ∑ m, c j m • u m, fun i j => ?_, fun i j => ?_, fun j => ⟨c j, rfl⟩⟩
  · rw [hform_add_right, hform_sum_right, hdual]
    simp [hform_smul_right, huu]
  · have hu'u : ∀ i m, hform σ (u' i) (u m) = if m = i then 1 else 0 := fun i m => by
      rw [hform_comm hσ, hdual]
      split_ifs <;> simp
    rw [hform_add_left, hform_add_right, hform_add_right, hform_sum_right, hform_sum_left,
      hform_sum_left]
    simp only [hform_smul_right, hform_smul_left, hu'u, hdual, hform_sum_right, huu, mul_zero,
      Finset.sum_const_zero, add_zero, mul_ite, mul_one, Finset.sum_ite_eq', Finset.mem_univ,
      ↓reduceIte]
    change G i j + c j i + σ (c i j) = 0
    rcases lt_trichotomy i j with hij | rfl | hij
    · simp only [c, hij, not_lt.mpr hij.le, ne_of_gt hij, ↓reduceIte, map_zero, add_zero,
        add_neg_cancel]
    · simp only [c, lt_irrefl, ↓reduceIte]
      rw [add_assoc, hd, add_neg_cancel]
    · simp only [c, hij, not_lt.mpr hij.le, ne_of_gt hij, ↓reduceIte, map_neg, hGσ, add_zero,
        add_neg_cancel]

end Dual

section Split

variable [DecidableEq ι] (hσ : ∀ x, σ (σ x) = x)
include hσ

theorem exists_hform_mulVec_ne_zero [CharP K 2] (hσ1 : ∃ x, σ x ≠ x) {N : Matrix ι ι K}
    (hNh : adjM σ N = N) (hN0 : N ≠ 0) : ∃ x, hform σ x (N *ᵥ x) ≠ 0 := by
  have hNadj : ∀ u v, hform σ (N *ᵥ u) v = hform σ u (N *ᵥ v) := fun u v => by
    rw [hform_mulVec, hNh]
  by_contra! h
  apply hN0
  obtain ⟨l, hl⟩ := hσ1
  have key : ∀ x y, hform σ x (N *ᵥ y) + σ (hform σ x (N *ᵥ y)) = 0 := by
    intro x y
    have h1 := h (x + y)
    rw [Matrix.mulVec_add, hform_add_left, hform_add_right, hform_add_right, h x, h y,
      zero_add, add_zero, ← hNadj y x, hform_comm hσ x (N *ᵥ y)] at h1
    exact h1
  have hxy : ∀ x y, hform σ x (N *ᵥ y) = 0 := by
    intro x y
    have ht := key x y
    have hlt := key (l • x) y
    rw [hform_smul_left, map_mul, hσ] at hlt
    have hst : σ (hform σ x (N *ᵥ y)) = hform σ x (N *ᵥ y) := by
      rw [add_eq_zero_iff_eq_neg, CharTwo.neg_eq] at ht
      exact ht.symm
    rw [hst, ← add_mul] at hlt
    have hne : σ l + l ≠ 0 := fun h0 => hl (by rwa [add_eq_zero_iff_eq_neg, CharTwo.neg_eq] at h0)
    exact (mul_eq_zero.mp hlt).resolve_left hne
  ext i j
  have h2 := eq_zero_of_hform_left (σ := σ) fun u => hxy u (Pi.single j 1)
  have h3 := congrFun h2 i
  simpa [Matrix.mulVec_single_one] using h3

omit hσ in
theorem one_add_smul_mul_one_add_smul {P : Matrix ι ι K} (hP : P * P = P) {a b : K}
    (hab : a + b + a * b = 0) : (1 + a • P) * (1 + b • P) = 1 := by
  rw [add_mul, one_mul, mul_add, mul_one, smul_mul_smul_comm, hP,
    show (1 : Matrix ι ι K) + b • P + (a • P + (a * b) • P) = 1 + (a + b + a * b) • P by
      rw [add_smul, add_smul]; abel,
    hab, zero_smul, add_zero]

theorem exists_hermitian_split [Finite K] [CharP K 2] (hσ1 : ∃ x, σ x ≠ x)
    (htr : ∀ c, σ c = c → ∃ d, d + σ d = c) (N : Matrix ι ι K) (hN : N * N = 0)
    (hNh : adjM σ N = N) (hℓ : 2 ≤ N.rank) :
    ∃ E₁ E₂ : Matrix ι ι K, N = E₁ + E₂ ∧ E₁ * E₁ = 0 ∧ E₁ * E₂ = 0 ∧ E₂ * E₁ = 0 ∧
      E₂ * E₂ = 0 ∧ adjM σ E₁ = E₁ ∧ adjM σ E₂ = E₂ ∧ E₁.rank = 1 ∧ E₂.rank = N.rank - 1 ∧
      (∃ v, E₁ *ᵥ v ≠ 0 ∧ E₂ *ᵥ v = 0) ∧
      ∀ c : K, σ c = c → c ≠ 0 → ∃ D : GL ι K, (D : Matrix ι ι K).det = 1 ∧
        adjM σ (D : Matrix ι ι K) * (D : Matrix ι ι K) = 1 ∧
        ((D⁻¹ : GL ι K) : Matrix ι ι K) * E₁ * (D : Matrix ι ι K) = E₁ ∧
        ((D⁻¹ : GL ι K) : Matrix ι ι K) * E₂ * (D : Matrix ι ι K) = c • E₂ := by
  classical
  have hN0 : N ≠ 0 := by
    rintro rfl
    rw [Matrix.rank_zero] at hℓ
    omega
  have hNadj : ∀ u v, hform σ (N *ᵥ u) v = hform σ u (N *ᵥ v) := fun u v => by
    rw [hform_mulVec, hNh]
  have hNN : ∀ v, N *ᵥ (N *ᵥ v) = 0 := fun v => by
    rw [Matrix.mulVec_mulVec, hN, Matrix.zero_mulVec]
  obtain ⟨x₀, hx₀⟩ := exists_hform_mulVec_ne_zero hσ hσ1 hNh hN0
  set c₀ := hform σ x₀ (N *ᵥ x₀) with hc₀
  have hc₀σ : σ c₀ = c₀ := by
    rw [hc₀, ← hform_comm hσ, hNadj]
  set e₀ := N *ᵥ x₀ with he₀
  have he₀N : ∀ v, hform σ e₀ (N *ᵥ v) = 0 := fun v => by
    rw [he₀, hNadj, hNN, hform_zero_right]
  have he₀x₀ : hform σ e₀ x₀ = c₀ := by rw [he₀, hNadj]
  have he₀0 : e₀ ≠ 0 := by
    intro h
    apply hx₀
    rw [hc₀, h, hform_zero_right]
  set E₁ : Matrix ι ι K := c₀⁻¹ • vecMulVec e₀ (σ ∘ e₀) with hE₁
  have hE₁v : ∀ v, E₁ *ᵥ v = (c₀⁻¹ * hform σ e₀ v) • e₀ := fun v => by
    rw [hE₁, Matrix.smul_mulVec, vecMulVec_mulVec', smul_smul]
    rfl
  set E₂ := N - E₁ with hE₂
  have hE₂v : ∀ v, E₂ *ᵥ v = N *ᵥ v - E₁ *ᵥ v := fun v => by rw [hE₂, Matrix.sub_mulVec]
  have hE₁N : E₁ * N = 0 := by
    rw [Matrix.ext_iff_mulVec]
    intro v
    rw [← Matrix.mulVec_mulVec, hE₁v, he₀N, mul_zero, zero_smul, Matrix.zero_mulVec]
  have hNE₁ : N * E₁ = 0 := by
    rw [Matrix.ext_iff_mulVec]
    intro v
    rw [← Matrix.mulVec_mulVec, hE₁v, Matrix.mulVec_smul, he₀, hNN, smul_zero,
      Matrix.zero_mulVec]
  have h11 : E₁ * E₁ = 0 := by
    rw [Matrix.ext_iff_mulVec]
    intro v
    rw [← Matrix.mulVec_mulVec, hE₁v (E₁ *ᵥ v), hE₁v v, hform_smul_right,
      show hform σ e₀ e₀ = 0 from he₀N x₀, mul_zero, mul_zero, zero_smul, Matrix.zero_mulVec]
  have h12 : E₁ * E₂ = 0 := by rw [hE₂, mul_sub, hE₁N, h11, sub_zero]
  have h21 : E₂ * E₁ = 0 := by rw [hE₂, sub_mul, hNE₁, h11, sub_zero]
  have hNE₂ : N * E₂ = 0 := by rw [hE₂, mul_sub, hN, hNE₁, sub_zero]
  have h22 : E₂ * E₂ = 0 := by rw [hE₂, sub_mul, hNE₂, h12, sub_zero]
  have hE₁h : adjM σ E₁ = E₁ := by
    rw [hE₁, adjM_smul, adjM_vecMulVec, map_inv₀, hc₀σ]
    congr 2
    ext a
    simp [hσ]
  have hE₂h : adjM σ E₂ = E₂ := by rw [hE₂, adjM_sub, hNh, hE₁h]
  have hE₂adj : ∀ u v, hform σ (E₂ *ᵥ u) v = hform σ u (E₂ *ᵥ v) := fun u v => by
    rw [hform_mulVec, hE₂h]
  have hE₁x₀ : E₁ *ᵥ x₀ = e₀ := by
    rw [hE₁v, he₀x₀, inv_mul_cancel₀ hx₀, one_smul]
  have hE₂x₀ : E₂ *ᵥ x₀ = 0 := by rw [hE₂v, hE₁x₀, he₀, sub_self]
  have hrank₁ : E₁.rank = 1 := by
    rw [rank_eq_finrank_range]
    have hR : LinearMap.range E₁.mulVecLin = K ∙ e₀ := by
      apply le_antisymm
      · rintro _ ⟨v, rfl⟩
        rw [Matrix.mulVecLin_apply, hE₁v]
        exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self e₀)
      · rw [Submodule.span_singleton_le_iff_mem]
        exact ⟨x₀, hE₁x₀⟩
    rw [hR, finrank_span_singleton he₀0]
  have hrank₂ : E₂.rank = N.rank - 1 := by
    refine (rank_eq_sub_one_of_split (by rw [hE₂, add_sub_cancel]) hrank₁ (fun v hv => ?_)
      hE₂x₀ (by rw [← he₀]; exact he₀0))
    rw [hE₂v, hv, hE₁v, he₀, hNadj, hv, hform_zero_right, mul_zero, zero_smul, sub_zero]
  refine ⟨E₁, E₂, by rw [hE₂, add_sub_cancel], h11, h12, h21, h22, hE₁h, hE₂h, hrank₁, hrank₂,
    ⟨x₀, by rw [hE₁x₀]; exact he₀0, hE₂x₀⟩, fun c hcσ hc => ?_⟩
  set U := LinearMap.range E₂.mulVecLin with hU
  set k := finrank K U with hk
  let bU := Module.finBasis K U
  set u : Fin k → ι → K := fun i => (bU i : ι → K) with hu
  have hmemU : ∀ w ∈ U, ∃ z, w = E₂ *ᵥ z := by
    rintro _ ⟨z, rfl⟩
    exact ⟨z, rfl⟩
  have huU : ∀ i, u i ∈ U := fun i => (bU i).2
  have hE₂U : ∀ w ∈ U, E₂ *ᵥ w = 0 := by
    intro w hw
    obtain ⟨z, rfl⟩ := hmemU w hw
    rw [Matrix.mulVec_mulVec, h22, Matrix.zero_mulVec]
  have hisoU : ∀ w ∈ U, ∀ w' ∈ U, hform σ w w' = 0 := by
    intro w hw w' hw'
    obtain ⟨z, rfl⟩ := hmemU w hw
    obtain ⟨z', rfl⟩ := hmemU w' hw'
    rw [hE₂adj, Matrix.mulVec_mulVec, h22, Matrix.zero_mulVec, hform_zero_right]
  have he₀U : ∀ w ∈ U, hform σ e₀ w = 0 := by
    intro w hw
    obtain ⟨z, rfl⟩ := hmemU w hw
    rw [he₀, hNadj, Matrix.mulVec_mulVec, hNE₂, Matrix.zero_mulVec, hform_zero_right]
  have hx₀U : ∀ w ∈ U, hform σ x₀ w = 0 := by
    intro w hw
    obtain ⟨z, rfl⟩ := hmemU w hw
    rw [← hE₂adj, hE₂x₀, hform_zero_left]
  let g : Fin k ⊕ Unit → ι → K := Sum.elim u fun _ => e₀
  have hg : LinearIndependent K g := by
    have hu : LinearIndependent K u := bU.linearIndependent.map' U.subtype U.ker_subtype
    refine hu.sum_type (linearIndependent_unique_iff.mpr he₀0) ?_
    rw [Submodule.disjoint_def]
    intro w hw hwe
    have hspan : Submodule.span K (Set.range u) ≤ U := Submodule.span_le.mpr (by
      rintro _ ⟨i, rfl⟩; exact huU i)
    have h1 := hx₀U w (hspan hw)
    have hre : Set.range (fun _ : Unit => e₀) = {e₀} := Set.range_const
    rw [hre] at hwe
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hwe
    rw [hform_smul_right] at h1
    rw [(mul_eq_zero.mp h1).resolve_right hx₀, zero_smul]
  obtain ⟨w, hw⟩ := exists_hform_dual hσ g hg
  set u' : Fin k → ι → K := fun j => w (.inl j) with hu'
  have hdual : ∀ i j, hform σ (u i) (u' j) = if i = j then 1 else 0 := fun i j => by
    have := hw (.inl i) (.inl j)
    simpa [g, Sum.inl_injective.eq_iff] using this
  have he₀u' : ∀ j, hform σ e₀ (u' j) = 0 := fun j => by
    have := hw (.inr ()) (.inl j)
    simpa [g] using this
  obtain ⟨u'', hdual'', hiso'', hcomb⟩ := exists_isotropic_dual hσ htr u u'
    (fun i j => hisoU _ (huU i) _ (huU j)) hdual
  have he₀u'' : ∀ j, hform σ e₀ (u'' j) = 0 := fun j => by
    obtain ⟨cj, hcj⟩ := hcomb j
    rw [hcj, hform_add_right, hform_sum_right, he₀u', zero_add]
    exact Finset.sum_eq_zero fun m _ => by rw [hform_smul_right, he₀U _ (huU m), mul_zero]
  set P := projP σ u u'' with hP
  set P' := projP σ u'' u with hP'
  have hPv : ∀ v, P *ᵥ v = ∑ i, hform σ (u'' i) v • u i := fun v => projP_mulVec u u'' v
  have hP'v : ∀ v, P' *ᵥ v = ∑ i, hform σ (u i) v • u'' i := fun v => projP_mulVec u'' u v
  have hu''u : ∀ i j, hform σ (u'' i) (u j) = if i = j then 1 else 0 := fun i j => by
    rw [hform_comm hσ, hdual'']
    by_cases h : i = j
    · subst h
      simp
    · simp [h, Ne.symm h]
  have huu : ∀ i j, hform σ (u i) (u j) = 0 := fun i j => hisoU _ (huU i) _ (huU j)
  have hPu : ∀ j, P *ᵥ u j = u j := fun j => by
    rw [hPv]
    simp [hu''u]
  have hPu'' : ∀ j, P *ᵥ u'' j = 0 := fun j => by
    rw [hPv]
    simp [hiso'']
  have hP'u : ∀ j, P' *ᵥ u j = 0 := fun j => by
    rw [hP'v]
    simp [huu]
  have hP'u'' : ∀ j, P' *ᵥ u'' j = u'' j := fun j => by
    rw [hP'v]
    simp [hdual'']
  have hPP : P * P = P := by
    rw [Matrix.ext_iff_mulVec]
    intro v
    rw [← Matrix.mulVec_mulVec, hPv v, Matrix.mulVec_sum]
    simp only [Matrix.mulVec_smul, hPu]
  have hP'P' : P' * P' = P' := by
    rw [Matrix.ext_iff_mulVec]
    intro v
    rw [← Matrix.mulVec_mulVec, hP'v v, Matrix.mulVec_sum]
    simp only [Matrix.mulVec_smul, hP'u'']
  have hPP' : P * P' = 0 := by
    rw [Matrix.ext_iff_mulVec]
    intro v
    rw [← Matrix.mulVec_mulVec, hP'v v, Matrix.mulVec_sum]
    simp [Matrix.mulVec_smul, hPu'']
  have hP'P : P' * P = 0 := by
    rw [Matrix.ext_iff_mulVec]
    intro v
    rw [← Matrix.mulVec_mulVec, hPv v, Matrix.mulVec_sum]
    simp [Matrix.mulVec_smul, hP'u]
  have hrepr : ∀ v, E₂ *ᵥ v = ∑ j, bU.repr ⟨E₂ *ᵥ v, ⟨v, rfl⟩⟩ j • u j := fun v => by
    have h1 := congrArg Subtype.val (bU.sum_repr ⟨E₂ *ᵥ v, ⟨v, rfl⟩⟩)
    rw [Submodule.coe_sum] at h1
    simp only [Submodule.coe_smul] at h1
    exact h1.symm
  have hE₂u : ∀ i, E₂ *ᵥ u i = 0 := fun i => hE₂U _ (huU i)
  have hE₂P : E₂ * P = 0 := by
    rw [Matrix.ext_iff_mulVec]
    intro v
    rw [← Matrix.mulVec_mulVec, hPv v, Matrix.mulVec_sum]
    simp [Matrix.mulVec_smul, hE₂u]
  have hPE₂ : P * E₂ = E₂ := by
    rw [Matrix.ext_iff_mulVec]
    intro v
    rw [← Matrix.mulVec_mulVec, hrepr v, Matrix.mulVec_sum]
    simp only [Matrix.mulVec_smul, hPu]
  have hP'E₂ : P' * E₂ = 0 := by
    rw [Matrix.ext_iff_mulVec]
    intro v
    have h1 : ∀ i, hform σ (u i) (E₂ *ᵥ v) = 0 := fun i => hisoU _ (huU i) _ ⟨v, rfl⟩
    rw [← Matrix.mulVec_mulVec, hP'v]
    simp [h1]
  have hE₂P' : E₂ * P' = E₂ := by
    rw [Matrix.ext_iff_mulVec]
    intro v
    rw [← Matrix.mulVec_mulVec, ← sub_eq_zero, ← Matrix.mulVec_sub]
    refine eq_zero_of_hform_left (σ := σ) fun z => ?_
    rw [← hE₂adj, hrepr z, hform_sum_left]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [hform_smul_left, hform_sub_right, hP'v, hform_sum_right]
    simp [hform_smul_right, hdual'', Finset.sum_ite_eq]
  obtain ⟨α, hα⟩ := isSquare_of_charTwo' c⁻¹
  have hα0 : α ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hα
    exact inv_ne_zero hc hα
  have hασ : σ α = α := by
    have h1 : σ α * σ α = α * α := by rw [← map_mul, ← hα, map_inv₀, hcσ]
    have h2 : (σ α - α) * (σ α - α) = 0 := by
      have : (σ α - α) * (σ α - α) = σ α * σ α - α * α - 2 * (α * (σ α - α)) := by ring
      rw [this, h1, sub_self, CharTwo.two_eq_zero, zero_mul, sub_zero]
    exact sub_eq_zero.mp (mul_self_eq_zero.mp h2)
  have hab : (α - 1) + (α⁻¹ - 1) + (α - 1) * (α⁻¹ - 1) = 0 := by
    field_simp
    ring
  obtain ⟨X, hX⟩ : ∃ X : Matrix ι ι K, X = 1 + (α - 1) • P := ⟨_, rfl⟩
  obtain ⟨Y, hY⟩ : ∃ Y : Matrix ι ι K, Y = 1 + (α⁻¹ - 1) • P' := ⟨_, rfl⟩
  obtain ⟨X', hX'⟩ : ∃ X' : Matrix ι ι K, X' = 1 + (α - 1) • P' := ⟨_, rfl⟩
  obtain ⟨Y', hY'⟩ : ∃ Y' : Matrix ι ι K, Y' = 1 + (α⁻¹ - 1) • P := ⟨_, rfl⟩
  have hab' : (α⁻¹ - 1) + (α - 1) + (α⁻¹ - 1) * (α - 1) = 0 := by
    rw [show (α⁻¹ - 1) + (α - 1) + (α⁻¹ - 1) * (α - 1) =
      (α - 1) + (α⁻¹ - 1) + (α - 1) * (α⁻¹ - 1) by ring]
    exact hab
  have hYX' : Y * X' = 1 := by rw [hY, hX']; exact one_add_smul_mul_one_add_smul hP'P' hab'
  have hY'X : Y' * X = 1 := by rw [hY', hX]; exact one_add_smul_mul_one_add_smul hPP hab'
  have hXY' : X * Y' = 1 := by rw [hX, hY']; exact one_add_smul_mul_one_add_smul hPP hab
  have hX'Y : X' * Y = 1 := by rw [hX', hY]; exact one_add_smul_mul_one_add_smul hP'P' hab
  have hDD' : (X * Y) * (X' * Y') = 1 := by
    rw [mul_assoc, ← mul_assoc Y, hYX', one_mul, hXY']
  have hD'D : (X' * Y') * (X * Y) = 1 := by
    rw [mul_assoc, ← mul_assoc Y', hY'X, one_mul, hX'Y]
  let D : GL ι K := ⟨X * Y, X' * Y', hDD', hD'D⟩
  have hDinv : ((D⁻¹ : GL ι K) : Matrix ι ι K) = X' * Y' := rfl
  have hadjD : adjM σ (X * Y) = X' * Y' := by
    rw [adjM_mul, hY, hX, adjM_add, adjM_add, adjM_one, adjM_smul, adjM_smul, hP, hP',
      adjM_projP hσ, adjM_projP hσ, map_sub, map_sub, map_one, map_inv₀, hασ, ← hP, ← hP', hX',
      hY']
    rw [add_mul, one_mul, mul_add, mul_one, smul_mul_smul_comm, hPP', smul_zero, add_zero,
      add_mul, one_mul, mul_add, mul_one, smul_mul_smul_comm, hP'P, smul_zero, add_zero]
    abel
  refine ⟨D, ?_, ?_, ?_, ?_⟩
  ·
    change (X * Y).det = 1
    have hdetP : ∀ a : K, ((1 : Matrix ι ι K) + a • P).det = (1 + a) ^ k := by
      intro a
      let A : Matrix ι (Fin k) K := Matrix.of fun x i => u i x
      let B : Matrix (Fin k) ι K := Matrix.of fun i x => σ (u'' i x)
      have hAB : P = A * B := by
        ext x y
        simp only [hP, projP, Matrix.sum_apply, vecMulVec_apply, Matrix.mul_apply, A, B,
          Matrix.of_apply, Function.comp]
      have hBA : B * A = 1 := by
        ext i j
        have := hu''u i j
        simp only [hform, dotProduct, Function.comp] at this
        simp only [Matrix.mul_apply, A, B, Matrix.of_apply, this, Matrix.one_apply]
      rw [hAB, ← Matrix.mul_smul, Matrix.det_one_add_mul_comm, Matrix.smul_mul, hBA,
        show (1 : Matrix (Fin k) (Fin k) K) + a • 1 = (1 + a) • 1 by rw [add_smul, one_smul],
        Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin]
    have hdetP' : ∀ a : K, ((1 : Matrix ι ι K) + a • P').det = (1 + a) ^ k := by
      intro a
      let A : Matrix ι (Fin k) K := Matrix.of fun x i => u'' i x
      let B : Matrix (Fin k) ι K := Matrix.of fun i x => σ (u i x)
      have hAB : P' = A * B := by
        ext x y
        simp only [hP', projP, Matrix.sum_apply, vecMulVec_apply, Matrix.mul_apply, A, B,
          Matrix.of_apply, Function.comp]
      have hBA : B * A = 1 := by
        ext i j
        have := hdual'' i j
        simp only [hform, dotProduct, Function.comp] at this
        simp only [Matrix.mul_apply, A, B, Matrix.of_apply, this, Matrix.one_apply]
      rw [hAB, ← Matrix.mul_smul, Matrix.det_one_add_mul_comm, Matrix.smul_mul, hBA,
        show (1 : Matrix (Fin k) (Fin k) K) + a • 1 = (1 + a) • 1 by rw [add_smul, one_smul],
        Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin]
    rw [Matrix.det_mul, hX, hY, hdetP, hdetP', add_sub_cancel, add_sub_cancel, ← mul_pow,
      mul_inv_cancel₀ hα0, one_pow]
  · exact (show adjM σ (X * Y) * (X * Y) = 1 by rw [hadjD]; exact hD'D)
  ·
    have hPe : P *ᵥ e₀ = 0 := by
      rw [hPv]
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [hform_comm hσ, he₀u'', map_zero, zero_smul]
    have hP'e : P' *ᵥ e₀ = 0 := by
      rw [hP'v]
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [hform_comm hσ, he₀U _ (huU i), map_zero, zero_smul]
    have hDe : (X * Y) *ᵥ e₀ = e₀ := by
      rw [← Matrix.mulVec_mulVec, hY, Matrix.add_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec,
        hP'e, smul_zero, add_zero, hX, Matrix.add_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec,
        hPe, smul_zero, add_zero]
    have hD'e : (X' * Y') *ᵥ e₀ = e₀ := by
      rw [← Matrix.mulVec_mulVec, hY', Matrix.add_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec,
        hPe, smul_zero, add_zero, hX', Matrix.add_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec,
        hP'e, smul_zero, add_zero]
    rw [hDinv, Matrix.ext_iff_mulVec]
    intro v
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hE₁v, hE₁v, Matrix.mulVec_smul, hD'e,
      hform_mulVec_right hσ, hadjD, hD'e]
  ·
    have hmod : E₂ + (α⁻¹ - 1) • E₂ = α⁻¹ • E₂ := by
      nth_rewrite 1 [← one_smul K E₂]
      rw [← add_smul, add_sub_cancel]
    have h1 : E₂ * (X * Y) = α⁻¹ • E₂ := by
      rw [← mul_assoc, hX, mul_add, mul_one, Matrix.mul_smul, hE₂P, smul_zero, add_zero, hY,
        mul_add, mul_one, Matrix.mul_smul, hE₂P', hmod]
    have h2 : (X' * Y') * E₂ = α⁻¹ • E₂ := by
      rw [mul_assoc, hY', add_mul, one_mul, Matrix.smul_mul, hPE₂, hmod, Matrix.mul_smul, hX',
        add_mul, one_mul, Matrix.smul_mul, hP'E₂, smul_zero, add_zero]
    rw [hDinv, mul_assoc (X' * Y') E₂ (X * Y), h1, Matrix.mul_smul, h2, smul_smul, ← mul_inv,
      ← hα, inv_inv]

end Split

end CFSG.ComponentClassification.RankTwoClassical
