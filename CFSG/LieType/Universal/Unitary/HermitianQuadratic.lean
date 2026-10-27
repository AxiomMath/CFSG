module

public import CFSG.LieType.Universal.Unitary.Hermitian
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic.NoncommRing

public section

namespace CFSG.LieType.Universal.Unitary

open Matrix

variable {F : Type*} [Field F] {σ : F ≃+* F} {r : ℕ}

private theorem sub_one_mul_self_eq_zero [CharP F 2] {A : Matrix (Fin r) (Fin r) F}
    (hA : A * A = 1) : (A - 1) * (A - 1) = 0 := by
  have h2 : (1 : Matrix (Fin r) (Fin r) F) + 1 = 0 := by
    ext i j
    simp only [Matrix.add_apply, Matrix.zero_apply]
    exact CharTwo.add_self_eq_zero _
  have hAA : A + A = 0 := by
    ext i j
    simp only [Matrix.add_apply, Matrix.zero_apply]
    exact CharTwo.add_self_eq_zero _
  have h : (A - 1) * (A - 1) = A * A + 1 - (A + A) := by noncomm_ring
  rw [h, hA, h2, hAA, sub_zero]

private theorem sub_one_mul_sub_one_comm {A B : Matrix (Fin r) (Fin r) F}
    (hAB : A * B = B * A) : (A - 1) * (B - 1) = (B - 1) * (A - 1) := by
  noncomm_ring [hAB]

private theorem add_self_eq_zero [CharP F 2] (A : Matrix (Fin r) (Fin r) F) : A + A = 0 := by
  ext i j
  simp only [Matrix.add_apply, Matrix.zero_apply]
  exact CharTwo.add_self_eq_zero _

private theorem eq_zero_of_mul_conjTr_eq_zero {γ : Matrix (Fin r) (Fin r) F}
    (h : ∀ i : Fin r, γ * single i i (1 : F) * conjTr σ γ = 0) : γ = 0 := by
  ext k i
  have hkk := congrFun (congrFun (h i) k) k
  rw [Matrix.mul_apply] at hkk
  rw [Finset.sum_eq_single i] at hkk
  · rw [Matrix.mul_single_apply_same, mul_one, conjTr_apply] at hkk
    rcases mul_eq_zero.mp hkk with h0 | h0
    · exact h0
    · exact σ.injective (h0.trans (map_zero σ).symm)
  · intro x _ hx
    rw [Matrix.mul_single_apply_of_ne (i := i) (j := i) (a := k) (b := x) (c := (1 : F)) hx]
    simp
  · intro hi
    exact absurd (Finset.mem_univ i) hi

private theorem eq_zero_of_forall_hermitian [CharP F 2]
    (hσ : ∀ c, σ (σ c) = c) {ζ : F} (hζ : ζ + σ ζ = 1)
    {B C : Matrix (Fin r) (Fin r) F}
    (h : ∀ M, M + conjTr σ M = 0 → B * M * conjTr σ C + C * M * conjTr σ B = 0)
    (M : Matrix (Fin r) (Fin r) F) :
    B * M * conjTr σ C + C * M * conjTr σ B = 0 := by
  let f : Matrix (Fin r) (Fin r) F → Matrix (Fin r) (Fin r) F :=
    fun M => B * M * conjTr σ C + C * M * conjTr σ B
  have h0 : f 0 = 0 := by
    dsimp only [f]
    simp
  have hadd : ∀ p q, f (p + q) = f p + f q := by
    intro p q
    dsimp only [f]
    rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_add, Matrix.add_mul]
    abel
  have hsmul : ∀ (c : F) p, f (c • p) = c • f p := by
    intro c p
    dsimp only [f]
    rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul, smul_add]
  have hbasis : ∀ (i j : Fin r) (x : F), f (single i j x) = 0 := by
    intro i j x
    have hH1 : (single i j 1 + single j i 1) + conjTr σ (single i j 1 + single j i 1) = 0 := by
      have hc : conjTr σ (single i j 1 + single j i 1) = single i j 1 + single j i 1 := by
        simp only [conjTr_add, conjTr_single, map_one]
        abel
      rw [hc, add_self_eq_zero]
    have hH2 : (ζ • single i j 1 + σ ζ • single j i 1) +
        conjTr σ (ζ • single i j 1 + σ ζ • single j i 1) = 0 := by
      have hc : conjTr σ (ζ • single i j 1 + σ ζ • single j i 1) =
          ζ • single i j 1 + σ ζ • single j i 1 := by
        simp only [conjTr_add, conjTr_smul, conjTr_single, hσ, map_one]
        abel
      rw [hc, add_self_eq_zero]
    have h1 : f (single i j 1 + single j i 1) = 0 := h _ hH1
    have h2 : f (ζ • single i j 1 + σ ζ • single j i 1) = 0 := h _ hH2
    have hcomb : single i j x = (x * σ ζ) • (single i j 1 + single j i 1) +
        x • (ζ • single i j 1 + σ ζ • single j i 1) := by
      rw [smul_add, smul_add, smul_smul, smul_smul]
      simp only [smul_single, smul_eq_mul, mul_one]
      rw [show single i j (x * σ ζ) + single j i (x * σ ζ) +
          (single i j (x * ζ) + single j i (x * σ ζ)) =
          (single i j (x * σ ζ) + single i j (x * ζ)) +
            (single j i (x * σ ζ) + single j i (x * σ ζ)) by abel]
      rw [← single_add, ← single_add]
      rw [show x * σ ζ + x * ζ = x by rw [← mul_add, add_comm, hζ, mul_one]]
      rw [show x * σ ζ + x * σ ζ = 0 by
        rw [← mul_add, CharTwo.add_self_eq_zero, mul_zero]]
      simp
    rw [hcomb, hadd, hsmul, hsmul, h1, h2, smul_zero, smul_zero, add_zero]
  refine Matrix.induction_on' M h0 ?_ ?_
  · intro p q hp hq
    change f p = 0 at hp
    change f q = 0 at hq
    change f (p + q) = 0
    rw [hadd, hp, hq, add_zero]
  · intro i j x
    exact hbasis i j x

private theorem mul_single_mul_conjTr_apply
    (B C : Matrix (Fin r) (Fin r) F) (i l p j : Fin r) :
    (B * single p j (1 : F) * conjTr σ C) i l = B i p * σ (C l j) := by
  rw [Matrix.mul_apply]
  rw [Finset.sum_eq_single j]
  · rw [Matrix.mul_single_apply_same, mul_one, conjTr_apply]
  · intro x _ hx
    rw [Matrix.mul_single_apply_of_ne (i := p) (j := j) (a := i) (b := x) (c := (1 : F)) hx]
    simp
  · intro hj
    exact absurd (Finset.mem_univ j) hj

private theorem mul_single_mul_conjTr_add_apply
    (B C : Matrix (Fin r) (Fin r) F) (i l p j : Fin r) :
    ((B * single p j (1 : F) * conjTr σ C +
      C * single p j (1 : F) * conjTr σ B) i l) =
      B i p * σ (C l j) + C i p * σ (B l j) := by
  rw [Matrix.add_apply, mul_single_mul_conjTr_apply, mul_single_mul_conjTr_apply]

private theorem hermitian_condition_sub_one {P P' : Matrix (Fin r) (Fin r) F}
    (h : ∀ M : Matrix (Fin r) (Fin r) F, M + conjTr σ M = 0 →
      P' * (P * M * conjTr σ P - M) * conjTr σ P' = P * M * conjTr σ P - M) :
    ∀ M : Matrix (Fin r) (Fin r) F, M + conjTr σ M = 0 →
      (1 + (P' - 1)) * (M * conjTr σ (P - 1) + (P - 1) * M +
        (P - 1) * M * conjTr σ (P - 1)) * (1 + conjTr σ (P' - 1)) =
      M * conjTr σ (P - 1) + (P - 1) * M +
        (P - 1) * M * conjTr σ (P - 1) := by
  set α : Matrix (Fin r) (Fin r) F := P - 1 with hα
  set β : Matrix (Fin r) (Fin r) F := P' - 1 with hβ
  have hP : P = 1 + α := by rw [hα]; abel
  have hP' : P' = 1 + β := by rw [hβ]; abel
  have hPc : conjTr σ P = 1 + conjTr σ α := by rw [hP, conjTr_add, conjTr_one]
  have hP'c : conjTr σ P' = 1 + conjTr σ β := by rw [hP', conjTr_add, conjTr_one]
  have hD : ∀ M, P * M * conjTr σ P - M =
      M * conjTr σ α + α * M + α * M * conjTr σ α := by
    intro M
    rw [hPc, hP]
    noncomm_ring
  intro M hM
  have hh := h M hM
  rw [hP'c, hP', hD M] at hh
  exact hh

private theorem mul_conjTr_eq_zero_of_hermitian [CharP F 2]
    {α β : Matrix (Fin r) (Fin r) F} (hα2 : α * α = 0) (hcomm : α * β = β * α)
    (hγP' : α * β * (1 + β) = α * β)
    (hhyp : ∀ M, M + conjTr σ M = 0 →
      (1 + β) * (M * conjTr σ α + α * M + α * M * conjTr σ α) * (1 + conjTr σ β) =
      M * conjTr σ α + α * M + α * M * conjTr σ α)
    {M : Matrix (Fin r) (Fin r) F} (hM : M + conjTr σ M = 0) :
    α * β * M * conjTr σ (α * β) = 0 := by
  have hβαα : ∀ X : Matrix (Fin r) (Fin r) F, β * (α * (α * X)) = 0 := by
    intro X
    rw [← mul_assoc α α X, hα2, zero_mul, mul_zero]
  have hh := hhyp M hM
  have h2 : α * β * (M * conjTr σ α + α * M + α * M * conjTr σ α) *
      (1 + conjTr σ β) =
      α * β * (M * conjTr σ α + α * M + α * M * conjTr σ α) := by
    calc α * β * (M * conjTr σ α + α * M + α * M * conjTr σ α) * (1 + conjTr σ β)
        = α * β * (1 + β) * (M * conjTr σ α + α * M + α * M * conjTr σ α) *
            (1 + conjTr σ β) := by rw [hγP']
      _ = α * β * ((1 + β) * (M * conjTr σ α + α * M + α * M * conjTr σ α) *
            (1 + conjTr σ β)) := by noncomm_ring
      _ = α * β * (M * conjTr σ α + α * M + α * M * conjTr σ α) := by rw [hh]
  have hγD : α * β * (M * conjTr σ α + α * M + α * M * conjTr σ α) =
      α * β * M * conjTr σ α := by
    simp only [mul_add, mul_assoc, hcomm, hβαα, mul_zero, zero_mul, add_zero]
  have h3 : α * β * M * conjTr σ α * (1 + conjTr σ β) = α * β * M * conjTr σ α := by
    rw [← hγD]
    exact h2
  have h6 : α * β * M * (conjTr σ α * conjTr σ β) = 0 := by
    have h' : α * β * M * conjTr σ α + α * β * M * (conjTr σ α * conjTr σ β) =
        α * β * M * conjTr σ α := by
      simpa [mul_add, mul_assoc] using h3
    exact add_left_cancel (show α * β * M * conjTr σ α +
      α * β * M * (conjTr σ α * conjTr σ β) = α * β * M * conjTr σ α + 0 by
        simpa using h')
  have hc : conjTr σ α * conjTr σ β = conjTr σ (α * β) := by
    rw [← conjTr_mul, ← hcomm]
  rwa [hc] at h6

private theorem sub_one_mul_sub_one_eq_zero [CharP F 2] {P P' : Matrix (Fin r) (Fin r) F}
    (hP : P * P = 1) (hP' : P' * P' = 1) (hPP' : P * P' = P' * P)
    (h : ∀ M, M + conjTr σ M = 0 →
      P' * (P * M * conjTr σ P - M) * conjTr σ P' = P * M * conjTr σ P - M) :
    (P - 1) * (P' - 1) = 0 := by
  set α : Matrix (Fin r) (Fin r) F := P - 1 with hα
  set β : Matrix (Fin r) (Fin r) F := P' - 1 with hβ
  have hα2 : α * α = 0 := by rw [hα]; exact sub_one_mul_self_eq_zero hP
  have hβ2 : β * β = 0 := by rw [hβ]; exact sub_one_mul_self_eq_zero hP'
  have hcomm : α * β = β * α := by rw [hα, hβ]; exact sub_one_mul_sub_one_comm hPP'
  have hhyp : ∀ M, M + conjTr σ M = 0 →
      (1 + β) * (M * conjTr σ α + α * M + α * M * conjTr σ α) * (1 + conjTr σ β) =
      M * conjTr σ α + α * M + α * M * conjTr σ α := by
    intro M hM
    have hh := hermitian_condition_sub_one h M hM
    simpa only [hα, hβ] using hh
  have hγP' : α * β * (1 + β) = α * β := by noncomm_ring [hβ2]
  have hγM : ∀ M, M + conjTr σ M = 0 → α * β * M * conjTr σ (α * β) = 0 := by
    intro M hM
    exact mul_conjTr_eq_zero_of_hermitian hα2 hcomm hγP' hhyp hM
  have hsingle : ∀ i : Fin r, α * β * single i i (1 : F) * conjTr σ (α * β) = 0 := by
    intro i
    refine hγM (single i i (1 : F)) ?_
    have hc : conjTr σ (single i i (1 : F)) = single i i (1 : F) := by
      rw [conjTr_single, map_one]
    rw [hc, add_self_eq_zero]
  exact eq_zero_of_mul_conjTr_eq_zero hsingle

private theorem mul_conjTr_add_eq_zero_of_forall [CharP F 2]
    {α β : Matrix (Fin r) (Fin r) F} (hcomm : α * β = β * α) (hγ0 : α * β = 0)
    (hhyp : ∀ M, M + conjTr σ M = 0 →
      (1 + β) * (M * conjTr σ α + α * M + α * M * conjTr σ α) * (1 + conjTr σ β) =
      M * conjTr σ α + α * M + α * M * conjTr σ α) :
    ∀ M, M + conjTr σ M = 0 → β * M * conjTr σ α + α * M * conjTr σ β = 0 := by
  have hγ0' : β * α = 0 := by rw [← hcomm, hγ0]
  have hγc0 : conjTr σ α * conjTr σ β = 0 := by
    have hcαβ : conjTr σ α * conjTr σ β = conjTr σ β * conjTr σ α := by
      rw [← conjTr_mul, ← conjTr_mul, hcomm]
    rw [hcαβ]
    have hc := congrArg (conjTr σ) hγ0
    rwa [conjTr_mul, conjTr_zero] at hc
  have hβα : ∀ X : Matrix (Fin r) (Fin r) F, β * (α * X) = 0 := by
    intro X
    rw [← mul_assoc, hγ0', zero_mul]
  intro M hM
  have hh := hhyp M hM
  have hD0 : (M * conjTr σ α + α * M + α * M * conjTr σ α) * conjTr σ β +
      β * (M * conjTr σ α + α * M + α * M * conjTr σ α) +
      β * (M * conjTr σ α + α * M + α * M * conjTr σ α) * conjTr σ β = 0 := by
    have hexp : (1 + β) * (M * conjTr σ α + α * M + α * M * conjTr σ α) *
        (1 + conjTr σ β) =
        (M * conjTr σ α + α * M + α * M * conjTr σ α) +
          (M * conjTr σ α + α * M + α * M * conjTr σ α) * conjTr σ β +
          β * (M * conjTr σ α + α * M + α * M * conjTr σ α) +
          β * (M * conjTr σ α + α * M + α * M * conjTr σ α) * conjTr σ β := by
      noncomm_ring
    have h' : (M * conjTr σ α + α * M + α * M * conjTr σ α) +
        ((M * conjTr σ α + α * M + α * M * conjTr σ α) * conjTr σ β +
        β * (M * conjTr σ α + α * M + α * M * conjTr σ α) +
        β * (M * conjTr σ α + α * M + α * M * conjTr σ α) * conjTr σ β) =
        (M * conjTr σ α + α * M + α * M * conjTr σ α) + 0 := by
      rw [show (M * conjTr σ α + α * M + α * M * conjTr σ α) +
          ((M * conjTr σ α + α * M + α * M * conjTr σ α) * conjTr σ β +
          β * (M * conjTr σ α + α * M + α * M * conjTr σ α) +
          β * (M * conjTr σ α + α * M + α * M * conjTr σ α) * conjTr σ β) =
          (1 + β) * (M * conjTr σ α + α * M + α * M * conjTr σ α) *
            (1 + conjTr σ β) by
        rw [hexp]
        abel]
      rw [hh, add_zero]
    exact add_left_cancel h'
  simpa only [mul_add, add_mul, mul_assoc, hγ0, hβα, hγc0, mul_zero, zero_mul, add_zero,
    zero_add, add_comm] using hD0

private theorem exists_sub_one_eq_smul_sub_one_of_forall [CharP F 2]
    {P P' : Matrix (Fin r) (Fin r) F} (hP1 : P ≠ 1)
    (hstep2 : ∀ M : Matrix (Fin r) (Fin r) F, (P' - 1) * M * conjTr σ (P - 1) +
      (P - 1) * M * conjTr σ (P' - 1) = 0) :
    ∃ c : F, c + σ c = 0 ∧ P' - 1 = c • (P - 1) := by
  have hαne : (P - 1 : Matrix (Fin r) (Fin r) F) ≠ 0 := sub_ne_zero.mpr hP1
  obtain ⟨l, j, hlj⟩ : ∃ l j : Fin r, (P - 1) l j ≠ 0 := by
    by_contra h
    push Not at h
    exact hαne (by ext l j; exact h l j)
  set c : F := σ ((P' - 1) l j) / σ ((P - 1) l j) with hc
  have hβ_eq : P' - 1 = c • (P - 1) := by
    ext i p
    have h0 := congrFun (congrFun (hstep2 (single p j (1 : F))) i) l
    have h0' : (P' - 1) i p * σ ((P - 1) l j) +
        (P - 1) i p * σ ((P' - 1) l j) = 0 := by
      rwa [mul_single_mul_conjTr_add_apply] at h0
    have hden : σ ((P - 1) l j) ≠ 0 := (map_ne_zero σ).mpr hlj
    have hEq : (P' - 1) i p * σ ((P - 1) l j) =
        (P - 1) i p * σ ((P' - 1) l j) := CharTwo.add_eq_zero.mp h0'
    have hip : (P' - 1) i p =
        (σ ((P' - 1) l j) / σ ((P - 1) l j)) * (P - 1) i p := by
      field_simp [hden]
      simpa [mul_comm] using hEq
    rw [hc]
    exact hip
  refine ⟨c, ?_, hβ_eq⟩
  · have h0 := congrFun (congrFun (hstep2 (single j j (1 : F))) l) l
    rw [hβ_eq, conjTr_smul] at h0
    simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.add_apply, Matrix.smul_apply,
      smul_eq_mul] at h0
    rw [mul_single_mul_conjTr_apply] at h0
    have hprod : (P - 1) l j * σ ((P - 1) l j) ≠ 0 :=
      mul_ne_zero hlj ((map_ne_zero σ).mpr hlj)
    have hsum : (c + σ c) * ((P - 1) l j * σ ((P - 1) l j)) = 0 := by
      rw [add_mul]
      exact h0
    rcases mul_eq_zero.mp hsum with h | h
    · exact h
    · exact absurd h hprod

theorem exists_sub_one_eq_smul_sub_one [CharP F 2] (hσ : ∀ c, σ (σ c) = c)
    (htr : ∀ a, σ a = a → ∃ c, c + σ c = a) {P P' : Matrix (Fin r) (Fin r) F}
    (hP : P * P = 1) (hP' : P' * P' = 1) (hPP' : P * P' = P' * P) (hP1 : P ≠ 1)
    (h : ∀ M : Matrix (Fin r) (Fin r) F, M + conjTr σ M = 0 →
      P' * (P * M * conjTr σ P - M) * conjTr σ P' = P * M * conjTr σ P - M) :
    ∃ c : F, c + σ c = 0 ∧ P' - 1 = c • (P - 1) := by
  obtain ⟨ζ, hζ⟩ := htr 1 (map_one σ)
  have hγ0 : (P - 1) * (P' - 1) = 0 := sub_one_mul_sub_one_eq_zero hP hP' hPP' h
  have hcomm : (P - 1) * (P' - 1) = (P' - 1) * (P - 1) := sub_one_mul_sub_one_comm hPP'
  have hHerm : ∀ M, M + conjTr σ M = 0 →
      (P' - 1) * M * conjTr σ (P - 1) + (P - 1) * M * conjTr σ (P' - 1) = 0 :=
    mul_conjTr_add_eq_zero_of_forall hcomm hγ0 (hermitian_condition_sub_one h)
  have hstep2 : ∀ M, (P' - 1) * M * conjTr σ (P - 1) +
      (P - 1) * M * conjTr σ (P' - 1) = 0 := by
    intro M
    exact eq_zero_of_forall_hermitian hσ hζ hHerm M
  exact exists_sub_one_eq_smul_sub_one_of_forall hP1 hstep2

private theorem vecMul_conjTr_apply (A : Matrix (Fin r) (Fin r) F) (y : Fin r → F) :
    (fun i => σ (y i)) ᵥ* conjTr σ A = fun i => σ ((A *ᵥ y) i) := by
  ext i
  simp only [Matrix.vecMul, Matrix.mulVec, conjTr_apply, dotProduct, map_sum, map_mul]
  exact Finset.sum_congr rfl fun j _ => by rw [mul_comm]

private theorem mul_vecMulVec_mul_conjTr (A : Matrix (Fin r) (Fin r) F) (x y : Fin r → F) :
    A * vecMulVec x (fun i => σ (y i)) * conjTr σ A =
      vecMulVec (A *ᵥ x) (fun i => σ ((A *ᵥ y) i)) := by
  rw [Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, vecMul_conjTr_apply]

private theorem exists_kernel_vector_notMem_span [CharP F 2] {P : Matrix (Fin r) (Fin r) F}
    (hr : 3 ≤ r) (hP : P * P = 1) (hP1 : P ≠ 1) :
    ∃ (x u y : Fin r → F) (i₀ : Fin r), u = (P - 1) *ᵥ x ∧ u i₀ ≠ 0 ∧
      (P - 1) *ᵥ u = 0 ∧ (P - 1) *ᵥ y = 0 ∧
        y ∉ Submodule.span F {u} := by
  have hα2 : (P - 1) * (P - 1) = 0 := sub_one_mul_self_eq_zero hP
  have hαne : (P - 1 : Matrix (Fin r) (Fin r) F) ≠ 0 := sub_ne_zero.mpr hP1
  obtain ⟨i₀, j₀, hij⟩ : ∃ i j : Fin r, (P - 1) i j ≠ 0 := by
    by_contra h
    push Not at h
    exact hαne (by ext i j; exact h i j)
  set x : Fin r → F := Pi.single j₀ (1 : F) with hx
  set u : Fin r → F := (P - 1) *ᵥ x with hu_def
  have hui : u i₀ ≠ 0 := by
    rw [hu_def, hx, Matrix.mulVec_single_one]
    simpa [Matrix.col_apply] using hij
  have hu : (P - 1) *ᵥ u = 0 := by
    rw [hu_def, Matrix.mulVec_mulVec, hα2, Matrix.zero_mulVec]
  have hrange : LinearMap.range (P - 1).mulVecLin ≤ LinearMap.ker (P - 1).mulVecLin := by
    rintro v ⟨w, rfl⟩
    rw [LinearMap.mem_ker, Matrix.mulVecLin_apply, Matrix.mulVecLin_apply,
      Matrix.mulVec_mulVec, hα2, Matrix.zero_mulVec]
  have hdim : 2 ≤ Module.finrank F (LinearMap.ker (P - 1).mulVecLin) := by
    have hrank := LinearMap.finrank_range_add_finrank_ker (P - 1).mulVecLin
    have hle := Submodule.finrank_mono hrange
    rw [Module.finrank_fin_fun] at hrank
    have h3 : 3 ≤ r := hr
    omega
  have hu_mem : u ∈ LinearMap.ker (P - 1).mulVecLin := by
    rw [LinearMap.mem_ker, Matrix.mulVecLin_apply]
    exact hu
  have hspan_le : Submodule.span F {u} ≤ LinearMap.ker (P - 1).mulVecLin := by
    rw [Submodule.span_le]
    intro v hv
    rw [Set.mem_singleton_iff] at hv
    subst hv
    exact hu_mem
  have hu_ne : u ≠ 0 := fun h => hui (by rw [h]; rfl)
  have hlt : Submodule.span F {u} < LinearMap.ker (P - 1).mulVecLin :=
    Submodule.lt_of_le_of_finrank_lt_finrank hspan_le
      (by rw [finrank_span_singleton hu_ne]; omega)
  obtain ⟨y, hyK, hy_span⟩ := IsConcreteLE.exists_of_lt hlt
  have hy : (P - 1) *ᵥ y = 0 := by
    rwa [LinearMap.mem_ker, Matrix.mulVecLin_apply] at hyK
  exact ⟨x, u, y, i₀, rfl, hui, hu, hy, hy_span⟩

private theorem exists_addMonoidHom_hermitian_fixing_aux [CharP F 2]
    (hσ : ∀ c, σ (σ c) = c) {P : Matrix (Fin r) (Fin r) F} {x u y : Fin r → F}
    (hu : u = (P - 1) *ᵥ x) (hy : (P - 1) *ᵥ y = 0) :
    ∃ μ : F →+ Matrix (Fin r) (Fin r) F,
      (∀ l, μ l + conjTr σ (μ l) = 0) ∧
      ∀ l, P * μ l * conjTr σ P =
        μ l + l • vecMulVec u (fun i => σ (y i)) +
          σ l • vecMulVec y (fun i => σ (u i)) := by
  let A : Matrix (Fin r) (Fin r) F := vecMulVec x (fun i => σ (y i))
  let B : Matrix (Fin r) (Fin r) F := vecMulVec y (fun i => σ (x i))
  let C : Matrix (Fin r) (Fin r) F := vecMulVec u (fun i => σ (y i))
  let D : Matrix (Fin r) (Fin r) F := vecMulVec y (fun i => σ (u i))
  let μ : F →+ Matrix (Fin r) (Fin r) F :=
    { toFun := fun l => l • A + σ l • B
      map_zero' := by simp
      map_add' := by
        intro a b
        simp only [map_add, add_smul]
        abel }
  have hPy : P *ᵥ y = y := by
    have h := hy
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_zero] at h
    exact h
  have hPx : P *ᵥ x = x + u := by
    have h := hu
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, eq_comm, sub_eq_iff_eq_add] at h
    simpa [add_comm] using h
  have hPA : P * A * conjTr σ P = A + C := by
    dsimp only [A, C]
    rw [mul_vecMulVec_mul_conjTr, hPy, hPx, add_vecMulVec]
  have hPB : P * B * conjTr σ P = B + D := by
    dsimp only [B, D]
    rw [mul_vecMulVec_mul_conjTr, hPy, hPx]
    rw [show (fun i => σ ((x + u) i)) = (fun i => σ (x i)) + (fun i => σ (u i)) by
      funext i
      simp]
    rw [vecMulVec_add]
  have hPμ : ∀ l, P * μ l * conjTr σ P = μ l + l • C + σ l • D := by
    intro l
    change P * (l • A + σ l • B) * conjTr σ P = (l • A + σ l • B) + l • C + σ l • D
    rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.smul_mul, hPA, hPB]
    simp only [smul_add]
    abel
  have hμherm : ∀ l, μ l + conjTr σ (μ l) = 0 := by
    intro l
    change (l • A + σ l • B) + conjTr σ (l • A + σ l • B) = 0
    rw [conjTr_add, conjTr_smul, conjTr_smul, conjTr_vecMulVec hσ, conjTr_vecMulVec hσ, hσ]
    simpa [add_comm, add_left_comm, add_assoc] using add_self_eq_zero (l • A + σ l • B)
  exact ⟨μ, hμherm, hPμ⟩

private theorem eq_zero_of_forall_conj_eq [CharP F 2]
    {P : Matrix (Fin r) (Fin r) F} {u y : Fin r → F} {i₀ : Fin r}
    (hui : u i₀ ≠ 0) (hy_span : y ∉ Submodule.span F {u})
    {μ : F →+ Matrix (Fin r) (Fin r) F}
    (hPμ : ∀ l, P * μ l * conjTr σ P =
      μ l + l • vecMulVec u (fun i => σ (y i)) +
        σ l • vecMulVec y (fun i => σ (u i))) :
    ∀ l, P * μ l * conjTr σ P = μ l → l = 0 := by
  intro l hl
  have h0 : l • vecMulVec u (fun i => σ (y i)) +
      σ l • vecMulVec y (fun i => σ (u i)) = 0 := by
    have h := hPμ l
    rw [hl] at h
    have h' : μ l + (l • vecMulVec u (fun i => σ (y i)) +
        σ l • vecMulVec y (fun i => σ (u i))) = μ l + 0 := by
      calc μ l + (l • vecMulVec u (fun i => σ (y i)) +
          σ l • vecMulVec y (fun i => σ (u i))) =
          μ l + l • vecMulVec u (fun i => σ (y i)) +
            σ l • vecMulVec y (fun i => σ (u i)) := by abel
        _ = μ l := h.symm
        _ = μ l + 0 := by rw [add_zero]
    exact add_left_cancel h'
  by_contra hl0
  have hyj : ∀ j : Fin r,
      y j = (σ.symm (σ l * y i₀) / σ.symm (l * u i₀)) * u j := by
    intro j
    have hrow := congrFun (congrFun h0 i₀) j
    simp only [Matrix.add_apply, Matrix.smul_apply, vecMulVec_apply, smul_eq_mul] at hrow
    have hEq : l * u i₀ * σ (y j) = σ l * y i₀ * σ (u j) := by
      have h := CharTwo.add_eq_zero.mp hrow
      simpa [mul_assoc] using h
    have hEq' : σ.symm (l * u i₀) * y j = σ.symm (σ l * y i₀) * u j := by
      have h := congrArg σ.symm hEq
      simpa [map_mul] using h
    have hden : σ.symm (l * u i₀) ≠ 0 :=
      (map_ne_zero σ.symm).mpr (mul_ne_zero hl0 hui)
    field_simp [hden]
    simpa [mul_comm] using hEq'
  have hy_span' : y ∈ Submodule.span F {u} := by
    rw [Submodule.mem_span_singleton]
    refine ⟨σ.symm (σ l * y i₀) / σ.symm (l * u i₀), ?_⟩
    funext k
    rw [Pi.smul_apply, smul_eq_mul]
    exact (hyj k).symm
  exact hy_span hy_span'

theorem exists_addMonoidHom_eq_zero_of_conj_eq [CharP F 2] (hσ : ∀ c, σ (σ c) = c)
    (hr : 3 ≤ r) {P : Matrix (Fin r) (Fin r) F} (hP : P * P = 1) (hP1 : P ≠ 1) :
    ∃ μ : F →+ Matrix (Fin r) (Fin r) F, (∀ l, μ l + conjTr σ (μ l) = 0) ∧
      ∀ l, P * μ l * conjTr σ P = μ l → l = 0 := by
  obtain ⟨x, u, y, i₀, hu, hui, _hu0, hy, hy_span⟩ :=
    exists_kernel_vector_notMem_span hr hP hP1
  obtain ⟨μ, hμherm, hPμ⟩ := exists_addMonoidHom_hermitian_fixing_aux hσ hu hy
  exact ⟨μ, hμherm, eq_zero_of_forall_conj_eq hui hy_span hPμ⟩

end CFSG.LieType.Universal.Unitary
