module

public import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Diagonal.Basic
public import CFSG.LocalAnalysis.ComponentInitial.LinearFlagOrder
import CFSG.LocalAnalysis.ComponentInitial.LinearHigherInvariant

public section

namespace CFSG.SeitzReduction.LinearPilot

open Matrix

section Normalizer

variable {F : Type*} [Field F]

theorem isUpperTriangular_of_conj_transvection {B Bi : Matrix (Fin 3) (Fin 3) F}
    (hB : B * Bi = 1)
    (h₁ : ∀ i, (Bi * transvection 0 1 (1 : F) * B : Matrix (Fin 3) (Fin 3) F) i 0 =
      (1 : Matrix (Fin 3) (Fin 3) F) i 0)
    (h₂ : ∀ i, (Bi * transvection 1 2 (1 : F) * B : Matrix (Fin 3) (Fin 3) F) i 0 =
      (1 : Matrix (Fin 3) (Fin 3) F) i 0)
    (h₃ : ∀ j, (B * transvection 1 2 (1 : F) * Bi : Matrix (Fin 3) (Fin 3) F) 2 j =
      (1 : Matrix (Fin 3) (Fin 3) F) 2 j) :
    B.IsUpperTriangular := by
  have hB' : Bi * B = 1 := mul_eq_one_comm.mp hB
  have hcol : ∀ u : Matrix (Fin 3) (Fin 3) F,
      (∀ i, (Bi * u * B) i 0 = (1 : Matrix (Fin 3) (Fin 3) F) i 0) → ∀ i, (u * B) i 0 = B i 0 := by
    intro u hu i
    have h1 : u * B = B * (Bi * u * B) := by
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hB, Matrix.one_mul]
    rw [h1, Matrix.mul_apply]
    simp only [hu, one_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
      ite_true]
  have hrow : ∀ u : Matrix (Fin 3) (Fin 3) F,
      (∀ j, (B * u * Bi) 2 j = (1 : Matrix (Fin 3) (Fin 3) F) 2 j) → ∀ j, (B * u) 2 j = B 2 j := by
    intro u hu j
    have h1 : B * u = (B * u * Bi) * B := by
      rw [Matrix.mul_assoc, hB', Matrix.mul_one]
    rw [h1, Matrix.mul_apply]
    simp only [hu, one_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ,
      ite_true]
  have h10 : B 1 0 = 0 := by
    have h := hcol _ h₁ 0
    rw [transvection_mul_apply_same, one_mul] at h
    linear_combination h
  have h20 : B 2 0 = 0 := by
    have h := hcol _ h₂ 1
    rw [transvection_mul_apply_same, one_mul] at h
    linear_combination h
  have h21 : B 2 1 = 0 := by
    have h := hrow _ h₃ 2
    rw [mul_transvection_apply_same, one_mul] at h
    linear_combination h
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all [Fin.lt_def]

end Normalizer

section Hilbert

variable {F : Type*} [Field F] {n : ℕ}

theorem exists_add_mul_map_ne_zero (σ : F →+* F) (hσ1 : ∃ x, σ x ≠ x) (b : F) :
    ∃ x : F, x + b * σ x ≠ 0 := by
  by_contra h
  push Not at h
  obtain ⟨y, hy⟩ := hσ1
  have h1 := h 1
  rw [map_one, mul_one] at h1
  have h2 := h y
  apply hy
  have hb : b = -1 := by linear_combination h1
  rw [hb] at h2
  linear_combination -h2

theorem exists_isUpperTriangular_eq_mul_map (σ : F →+* F) (hσσ : ∀ x, σ (σ x) = x)
    (hσ1 : ∃ x, σ x ≠ x) {B : Matrix (Fin n) (Fin n) F} (hBu : B.IsUpperTriangular)
    (hBσ : B * B.map σ = 1) :
    ∃ A Ai : Matrix (Fin n) (Fin n) F, A.IsUpperTriangular ∧ A * Ai = 1 ∧ Ai * A = 1 ∧
      A = B * A.map σ := by
  classical
  choose x hx using exists_add_mul_map_ne_zero σ hσ1
  set X : Matrix (Fin n) (Fin n) F := diagonal fun i => x (B i i) with hX
  have hXσ : X.map σ = diagonal fun i => σ (x (B i i)) := diagonal_map (map_zero σ)
  have hXσσ : (X.map σ).map σ = X := by
    rw [hXσ, diagonal_map (map_zero σ)]
    simp only [hσσ, hX]
  set A : Matrix (Fin n) (Fin n) F := X + B * X.map σ with hA
  have hAu : A.IsUpperTriangular :=
    (blockTriangular_diagonal _).add (hBu.mul (hXσ ▸ blockTriangular_diagonal _))
  have hAii : ∀ i, A i i = x (B i i) + B i i * σ (x (B i i)) := by
    intro i
    rw [hA, Matrix.add_apply, hXσ, mul_diagonal, hX, diagonal_apply_eq]
  have hdet : A.det ≠ 0 := by
    rw [det_of_isUpperTriangular hAu, Finset.prod_ne_zero_iff]
    intro i _
    rw [hAii]
    exact hx _
  refine ⟨A, A⁻¹, hAu, mul_nonsing_inv A (isUnit_iff_ne_zero.mpr hdet),
    nonsing_inv_mul A (isUnit_iff_ne_zero.mpr hdet), ?_⟩
  rw [hA, Matrix.map_add σ (map_add σ), Matrix.map_mul, hXσσ, Matrix.mul_add, ← Matrix.mul_assoc,
    hBσ,
    Matrix.one_mul, add_comm]

theorem map_conj_eq_of_mul_eq (σ : F →+* F) (hσσ : ∀ x, σ (σ x) = x)
    {A Ai B M : Matrix (Fin n) (Fin n) F} (hAAi : A * Ai = 1) (hA : A = B * A.map σ)
    (hBσ : B * B.map σ = 1) (hM : M * B = B * M.map σ) :
    (Ai * M * A).map σ = Ai * M * A := by
  have hmm : ∀ N : Matrix (Fin n) (Fin n) F, (N.map σ).map σ = N := fun N => by
    rw [Matrix.map_map]
    ext i j
    exact hσσ _
  have hBσ' : B.map σ * B = 1 := by
    have h := congrArg (fun N => N.map σ) hBσ
    simp only [Matrix.map_mul, hmm, Matrix.map_one σ (map_zero σ) (map_one σ)] at h
    exact h
  have hAσ : A.map σ = B.map σ * A := by
    conv_rhs => rw [hA, ← Matrix.mul_assoc, hBσ', Matrix.one_mul]
  have hAiA : Ai * A = 1 := mul_eq_one_comm.mp hAAi
  have hAiσ : Ai.map σ = Ai * B := by
    have h := congrArg (fun N => N.map σ) hAAi
    simp only [Matrix.map_mul, Matrix.map_one σ (map_zero σ) (map_one σ)] at h
    rw [hAσ] at h
    calc Ai.map σ = Ai * (B * (B.map σ * A * Ai.map σ)) := by
          rw [← Matrix.mul_assoc B, ← Matrix.mul_assoc B, hBσ, Matrix.one_mul,
            ← Matrix.mul_assoc, hAiA, Matrix.one_mul]
      _ = Ai * B := by rw [h, Matrix.mul_one]
  have hMσ : B * M.map σ * B.map σ = M := by
    rw [← hM, Matrix.mul_assoc, hBσ, Matrix.mul_one]
  rw [Matrix.map_mul, Matrix.map_mul, hAiσ, hAσ]
  calc Ai * B * M.map σ * (B.map σ * A) = Ai * (B * M.map σ * B.map σ) * A := by
        simp only [Matrix.mul_assoc]
    _ = Ai * M * A := by rw [hMσ]

theorem conj_mul_eq_of_map_eq (σ : F →+* F) (hσσ : ∀ x, σ (σ x) = x)
    {A Ai B N : Matrix (Fin n) (Fin n) F} (hAAi : A * Ai = 1) (hA : A = B * A.map σ)
    (hBσ : B * B.map σ = 1) (hN : N.map σ = N) :
    A * N * Ai * B = B * (A * N * Ai).map σ := by
  have hmm : ∀ N : Matrix (Fin n) (Fin n) F, (N.map σ).map σ = N := fun N => by
    rw [Matrix.map_map]
    ext i j
    exact hσσ _
  have hBσ' : B.map σ * B = 1 := by
    have h := congrArg (fun N => N.map σ) hBσ
    simp only [Matrix.map_mul, hmm, Matrix.map_one σ (map_zero σ) (map_one σ)] at h
    exact h
  have hAσ : A.map σ = B.map σ * A := by
    conv_rhs => rw [hA, ← Matrix.mul_assoc, hBσ', Matrix.one_mul]
  have hAiA : Ai * A = 1 := mul_eq_one_comm.mp hAAi
  have hAiσ : Ai.map σ = Ai * B := by
    have h := congrArg (fun N => N.map σ) hAAi
    simp only [Matrix.map_mul, Matrix.map_one σ (map_zero σ) (map_one σ)] at h
    rw [hAσ] at h
    calc Ai.map σ = Ai * (B * (B.map σ * A * Ai.map σ)) := by
          rw [← Matrix.mul_assoc B, ← Matrix.mul_assoc B, hBσ, Matrix.one_mul,
            ← Matrix.mul_assoc, hAiA, Matrix.one_mul]
      _ = Ai * B := by rw [h, Matrix.mul_one]
  rw [Matrix.map_mul, Matrix.map_mul, hAσ, hAiσ, hN]
  simp only [← Matrix.mul_assoc]
  rw [hBσ, Matrix.one_mul]

end Hilbert

section Count

variable {F : Type*} [Field F] [CharP F 2]

theorem exists_map_castHom_eq_of_map_eq (σ : F →+* F) (hfix : ∀ x, σ x = x → x = 0 ∨ x = 1)
    {N : Matrix (Fin 3) (Fin 3) F} (hN : N.map σ = N) (hdet : N.det = 1) :
    ∃ y : SpecialLinearGroup (Fin 3) (ZMod 2),
      ((SpecialLinearGroup.map (ZMod.castHom (dvd_refl 2) F) y : SpecialLinearGroup (Fin 3) F) :
        Matrix (Fin 3) (Fin 3) F) = N := by
  have hent : ∀ i j, ∃ b : ZMod 2, ZMod.castHom (dvd_refl 2) F b = N i j := by
    intro i j
    have h1 : σ (N i j) = N i j := congrFun (congrFun hN i) j
    rcases hfix _ h1 with h | h
    · exact ⟨0, by rw [map_zero, h]⟩
    · exact ⟨1, by rw [map_one, h]⟩
  choose M hM using hent
  have h1 : (ZMod.castHom (dvd_refl 2) F).mapMatrix (Matrix.of M) = N := by
    ext i j
    exact hM i j
  have hdetM : (Matrix.of M).det = 1 := by
    apply ZMod.castHom_injective F
    rw [map_one, RingHom.map_det, h1, hdet]
  exact ⟨⟨Matrix.of M, hdetM⟩, h1⟩

theorem ncard_twistFixed_le (σ : F →+* F) (hσσ : ∀ x, σ (σ x) = x)
    (hfix : ∀ x, σ x = x → x = 0 ∨ x = 1) {A Ai B : Matrix (Fin 3) (Fin 3) F}
    (hAAi : A * Ai = 1) (hA : A = B * A.map σ) (hBσ : B * B.map σ = 1) :
    {M : SpecialLinearGroup (Fin 3) F |
      (M : Matrix (Fin 3) (Fin 3) F) * B = B * (M : Matrix (Fin 3) (Fin 3) F).map σ}.ncard ≤
        168 := by
  set T := {M : SpecialLinearGroup (Fin 3) F |
    (M : Matrix (Fin 3) (Fin 3) F) * B = B * (M : Matrix (Fin 3) (Fin 3) F).map σ} with hT
  have hAiA : Ai * A = 1 := mul_eq_one_comm.mp hAAi
  have hex : ∀ M : T, ∃ y : SpecialLinearGroup (Fin 3) (ZMod 2),
      ((SpecialLinearGroup.map (ZMod.castHom (dvd_refl 2) F) y : SpecialLinearGroup (Fin 3) F) :
        Matrix (Fin 3) (Fin 3) F) = Ai * (M : SpecialLinearGroup (Fin 3) F) * A := by
    intro M
    refine exists_map_castHom_eq_of_map_eq σ hfix
      (map_conj_eq_of_mul_eq σ hσσ hAAi hA hBσ M.2) ?_
    rw [det_mul, det_mul, (M : SpecialLinearGroup (Fin 3) F).2, mul_one, ← det_mul, hAiA,
      det_one]
  choose f hf using hex
  have hinj : Function.Injective f := by
    intro M M' h
    have h3 : Ai * ((M : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) * A =
        Ai * ((M' : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) * A := by
      rw [← hf M, ← hf M', h]
    apply Subtype.ext
    apply Subtype.ext
    calc ((M : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
          A * (Ai * (M : SpecialLinearGroup (Fin 3) F) * A) * Ai := by
            simp only [← Matrix.mul_assoc, hAAi, Matrix.one_mul]
            rw [Matrix.mul_assoc, hAAi, Matrix.mul_one]
      _ = A * (Ai * (M' : SpecialLinearGroup (Fin 3) F) * A) * Ai := by rw [h3]
      _ = ((M' : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) := by
            simp only [← Matrix.mul_assoc, hAAi, Matrix.one_mul]
            rw [Matrix.mul_assoc, hAAi, Matrix.mul_one]
  rw [← Nat.card_coe_set_eq]
  calc Nat.card T ≤ Nat.card (SpecialLinearGroup (Fin 3) (ZMod 2)) :=
        Nat.card_le_card_of_injective f hinj
    _ = 168 := by
        rw [CFSG.LocalAnalysis.ComponentInitial.LinearFlag.card_SL_eq (by norm_num),
          Nat.card_zmod]
        decide

end Count

section Vectors

variable {F : Type*} [Field F]

theorem card_le_eight_of_twist (σ : F →+* F) (hσ : ∀ x, σ x = x ^ 2)
    {A Ai B : Matrix (Fin 3) (Fin 3) F} (hAAi : A * Ai = 1) (hA : A = B * A.map σ) {μ : F}
    {X : Type*} (f : X → Fin 3 → F) (hf : Function.Injective f)
    (hV : ∀ x, μ • f x = B *ᵥ fun i => σ (f x i)) : Nat.card X ≤ 8 := by
  have hAiA : Ai * A = 1 := mul_eq_one_comm.mp hAAi
  set s' : X → Fin 3 → F := fun x => Ai *ᵥ f x with hs'
  have hfs : ∀ x, f x = A *ᵥ s' x := fun x => by rw [hs', mulVec_mulVec, hAAi, one_mulVec]
  have hcoord : ∀ x j, s' x j = 0 ∨ s' x j = μ := by
    intro x j
    have h1 : (B *ᵥ fun i => σ (f x i)) = A *ᵥ fun i => σ (s' x i) := by
      have h0 : (fun i => σ (f x i)) = A.map σ *ᵥ fun i => σ (s' x i) := by
        rw [hfs x]
        funext i
        exact RingHom.map_mulVec σ A (s' x) i
      rw [h0, mulVec_mulVec, ← hA]
    have h2 : A *ᵥ (μ • s' x) = A *ᵥ fun i => σ (s' x i) := by
      rw [mulVec_smul, ← hfs, hV, h1]
    have h3 : μ • s' x = fun i => σ (s' x i) := by
      have h4 := congrArg (fun v => Ai *ᵥ v) h2
      simp only [mulVec_mulVec, hAiA, one_mulVec] at h4
      exact h4
    have h4 := congrFun h3 j
    simp only [Pi.smul_apply, smul_eq_mul, hσ] at h4
    have h5 : s' x j * (s' x j - μ) = 0 := by linear_combination -h4
    rcases mul_eq_zero.1 h5 with h | h
    · exact Or.inl h
    · exact Or.inr (by linear_combination h)
  classical
  let g : X → Fin 3 → Bool := fun x j => decide (s' x j = 0)
  have hg : Function.Injective g := by
    intro x y hxy
    apply hf
    rw [hfs x, hfs y]
    congr 1
    funext j
    have h := congrFun hxy j
    simp only [g, decide_eq_decide] at h
    rcases hcoord x j with hx | hx <;> rcases hcoord y j with hy | hy
    · rw [hx, hy]
    · rw [hx, hy]
      exact (hy.symm.trans (h.1 hx)).symm
    · rw [hx, hy]
      exact hx.symm.trans (h.2 hy)
    · rw [hx, hy]
  calc Nat.card X ≤ Nat.card (Fin 3 → Bool) := Nat.card_le_card_of_injective g hg
    _ = 8 := by rw [Nat.card_fun]; simp

end Vectors

section Generation

variable {F : Type*} [Field F] [CharP F 2]

variable (F) in
@[expose] def swapMat01 : Matrix (Fin 3) (Fin 3) F := !![0, 1, 0; 1, 0, 0; 0, 0, 1]

variable (F) in
@[expose] def swapMat12 : Matrix (Fin 3) (Fin 3) F := !![1, 0, 0; 0, 0, 1; 0, 1, 0]

theorem det_swapMat01 : (swapMat01 F).det = 1 := by
  rw [swapMat01, det_fin_three]
  simp [CharTwo.neg_eq]

theorem det_swapMat12 : (swapMat12 F).det = 1 := by
  rw [swapMat12, det_fin_three]
  simp [CharTwo.neg_eq]

variable (F) in
@[expose] def swapSL01 : SpecialLinearGroup (Fin 3) F := ⟨swapMat01 F, det_swapMat01⟩

variable (F) in
@[expose] def swapSL12 : SpecialLinearGroup (Fin 3) F := ⟨swapMat12 F, det_swapMat12⟩

omit [CharP F 2] in
theorem map_swapMat01 (σ : F →+* F) : (swapMat01 F).map σ = swapMat01 F := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [swapMat01]

omit [CharP F 2] in
theorem map_swapMat12 (σ : F →+* F) : (swapMat12 F).map σ = swapMat12 F := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [swapMat12]

theorem swapSL01_conj_transvection_zero_one (a : F) :
    swapSL01 F * SpecialLinearGroup.transvection (show (0 : Fin 3) ≠ 1 by decide) a *
        swapSL01 F = SpecialLinearGroup.transvection (show (1 : Fin 3) ≠ 0 by decide) a := by
  apply Subtype.ext
  rw [SpecialLinearGroup.coe_mul, SpecialLinearGroup.coe_mul, SpecialLinearGroup.transvection_coe,
    SpecialLinearGroup.transvection_coe]
  change swapMat01 F * _ * swapMat01 F = _
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [swapMat01, Matrix.mul_apply, Fin.sum_univ_three, vecMul, dotProduct, Matrix.single_apply,
      Matrix.one_apply]

theorem swapSL12_conj_transvection_one_two (a : F) :
    swapSL12 F * SpecialLinearGroup.transvection (show (1 : Fin 3) ≠ 2 by decide) a *
        swapSL12 F = SpecialLinearGroup.transvection (show (2 : Fin 3) ≠ 1 by decide) a := by
  apply Subtype.ext
  rw [SpecialLinearGroup.coe_mul, SpecialLinearGroup.coe_mul, SpecialLinearGroup.transvection_coe,
    SpecialLinearGroup.transvection_coe]
  change swapMat12 F * _ * swapMat12 F = _
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [swapMat12, Matrix.mul_apply, Fin.sum_univ_three, vecMul, dotProduct, Matrix.single_apply,
      Matrix.one_apply]

theorem swapSL01_conj_transvection_two_one (a : F) :
    swapSL01 F * SpecialLinearGroup.transvection (show (2 : Fin 3) ≠ 1 by decide) a *
        swapSL01 F = SpecialLinearGroup.transvection (show (2 : Fin 3) ≠ 0 by decide) a := by
  apply Subtype.ext
  rw [SpecialLinearGroup.coe_mul, SpecialLinearGroup.coe_mul, SpecialLinearGroup.transvection_coe,
    SpecialLinearGroup.transvection_coe]
  change swapMat01 F * _ * swapMat01 F = _
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [swapMat01, Matrix.mul_apply, Fin.sum_univ_three, vecMul, dotProduct, Matrix.single_apply,
      Matrix.one_apply]

theorem eq_top_of_unitriangular_le_of_swap {H : Subgroup (SpecialLinearGroup (Fin 3) F)}
    (hU : CFSG.LocalAnalysis.ComponentInitial.LinearFlag.unitriangular 3 F ≤ H)
    (h01 : swapSL01 F ∈ H) (h12 : swapSL12 F ∈ H) : H = ⊤ := by
  have hup : ∀ (i j : Fin 3) (h : i < j) (a : F), SpecialLinearGroup.transvection h.ne a ∈ H :=
    fun i j h a =>
      hU (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.transvection_mem_unitriangular h a)
  have h10 : ∀ a : F, SpecialLinearGroup.transvection (show (1 : Fin 3) ≠ 0 by decide) a ∈ H := by
    intro a
    rw [← swapSL01_conj_transvection_zero_one]
    exact mul_mem (mul_mem h01 (hup 0 1 (by decide) a)) h01
  have h21 : ∀ a : F, SpecialLinearGroup.transvection (show (2 : Fin 3) ≠ 1 by decide) a ∈ H := by
    intro a
    rw [← swapSL12_conj_transvection_one_two]
    exact mul_mem (mul_mem h12 (hup 1 2 (by decide) a)) h12
  have h20 : ∀ a : F, SpecialLinearGroup.transvection (show (2 : Fin 3) ≠ 0 by decide) a ∈ H := by
    intro a
    rw [← swapSL01_conj_transvection_two_one]
    exact mul_mem (mul_mem h01 (h21 a)) h01
  have ht : ∀ (i j : Fin 3) (hij : i ≠ j) (a : F), SpecialLinearGroup.transvection hij a ∈ H := by
    intro i j hij a
    rcases lt_or_gt_of_ne hij with h | h
    · exact hup i j h a
    · fin_cases i <;> fin_cases j <;> simp only [Fin.lt_def] at h <;> first
        | omega | exact h10 a | exact h20 a | exact h21 a
  refine eq_top_iff.2 fun M _ => ?_
  refine SpecialLinearGroup.diagonal_transvection_induction' (· ∈ H) M (fun i j hij c hc => ?_) ht
    (fun A B hA hB => H.mul_mem hA hB)
  rw [← SpecialLinearGroup.diag2nUnit_mk0, SpecialLinearGroup.diag2nUnit_decompose]
  exact mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (ht _ _ _ _) (ht _ _ _ _)) (ht _ _ _ _))
    (ht _ _ _ _)) (ht _ _ _ _)) (ht _ _ _ _)

theorem eq_top_of_conj_swap {H : Subgroup (SpecialLinearGroup (Fin 3) F)}
    {A Ai : Matrix (Fin 3) (Fin 3) F} (hAu : A.IsUpperTriangular) (hAAi : A * Ai = 1)
    (hU : CFSG.LocalAnalysis.ComponentInitial.LinearFlag.unitriangular 3 F ≤ H)
    (h01 : ∃ M ∈ H, (M : Matrix (Fin 3) (Fin 3) F) = A * swapMat01 F * Ai)
    (h12 : ∃ M ∈ H, (M : Matrix (Fin 3) (Fin 3) F) = A * swapMat12 F * Ai) : H = ⊤ := by
  have hAiA : Ai * A = 1 := mul_eq_one_comm.mp hAAi
  have hdet : ∀ N : SpecialLinearGroup (Fin 3) F,
      (A * (N : Matrix (Fin 3) (Fin 3) F) * Ai).det = 1 := fun N => by
    rw [det_mul, det_mul, N.2, mul_one, mul_comm, ← det_mul, hAiA, det_one]
  let κ : SpecialLinearGroup (Fin 3) F →* SpecialLinearGroup (Fin 3) F :=
    { toFun := fun N => ⟨A * (N : Matrix (Fin 3) (Fin 3) F) * Ai, hdet N⟩
      map_one' := Subtype.ext (by
        change A * (1 : Matrix (Fin 3) (Fin 3) F) * Ai = 1
        rw [Matrix.mul_one, hAAi])
      map_mul' := fun N N' => Subtype.ext (by
        change A * ((N : Matrix (Fin 3) (Fin 3) F) * (N' : Matrix (Fin 3) (Fin 3) F)) * Ai =
          (A * (N : Matrix (Fin 3) (Fin 3) F) * Ai) * (A * (N' : Matrix (Fin 3) (Fin 3) F) * Ai)
        simp only [Matrix.mul_assoc]
        rw [← Matrix.mul_assoc Ai A, hAiA, Matrix.one_mul]) }
  have hκ : ∀ N, ((κ N : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      A * (N : Matrix (Fin 3) (Fin 3) F) * Ai := fun N => rfl
  have hAiu : Ai.IsUpperTriangular := by
    have : Invertible A := Matrix.invertibleOfIsUnitDet A (Matrix.isUnit_det_of_right_inverse hAAi)
    rw [← Matrix.inv_eq_right_inv hAAi]
    exact blockTriangular_inv_of_blockTriangular hAu
  have hdiag : ∀ i, A i i * Ai i i = 1 := fun i => by
    rw [← CFSG.LocalAnalysis.ComponentInitial.LinearFlag.mul_apply_self_of_isUpperTriangular hAu
      hAiu, hAAi, one_apply_eq]
  have hκU : ∀ u ∈ CFSG.LocalAnalysis.ComponentInitial.LinearFlag.unitriangular 3 F,
      κ u ∈ CFSG.LocalAnalysis.ComponentInitial.LinearFlag.unitriangular 3 F := by
    intro u hu
    have hu' : (u : Matrix (Fin 3) (Fin 3) F).IsUpperTriangular := fun i j h => hu.1 i j h
    refine ⟨fun i j hij => ?_, fun i => ?_⟩
    · rw [hκ]
      exact ((hAu.mul hu').mul hAiu) hij
    · rw [hκ, CFSG.LocalAnalysis.ComponentInitial.LinearFlag.mul_apply_self_of_isUpperTriangular
        (hAu.mul hu') hAiu,
        CFSG.LocalAnalysis.ComponentInitial.LinearFlag.mul_apply_self_of_isUpperTriangular hAu hu',
        hu.2, mul_one, hdiag]
  have htop : H.comap κ = ⊤ := by
    apply eq_top_of_unitriangular_le_of_swap
    · intro u hu
      exact hU (hκU u hu)
    · obtain ⟨M, hM, hMeq⟩ := h01
      change κ (swapSL01 F) ∈ H
      convert hM using 1
      exact Subtype.ext (by rw [hκ, hMeq]; rfl)
    · obtain ⟨M, hM, hMeq⟩ := h12
      change κ (swapSL12 F) ∈ H
      convert hM using 1
      exact Subtype.ext (by rw [hκ, hMeq]; rfl)
  refine eq_top_iff.2 fun N _ => ?_
  have hdetN : (Ai * (N : Matrix (Fin 3) (Fin 3) F) * A).det = 1 := by
    rw [det_mul, det_mul, N.2, mul_one, ← det_mul, hAiA, det_one]
  let N' : SpecialLinearGroup (Fin 3) F := ⟨Ai * (N : Matrix (Fin 3) (Fin 3) F) * A, hdetN⟩
  have hN : κ N' = N := by
    apply Subtype.ext
    change A * (Ai * (N : Matrix (Fin 3) (Fin 3) F) * A) * Ai = (N : Matrix (Fin 3) (Fin 3) F)
    simp only [← Matrix.mul_assoc, hAAi, Matrix.one_mul]
    rw [Matrix.mul_assoc, hAAi, Matrix.mul_one]
  have h1 : N' ∈ H.comap κ := by
    rw [htop]
    exact Subgroup.mem_top _
  rw [← hN]
  exact h1

end Generation

end CFSG.SeitzReduction.LinearPilot
