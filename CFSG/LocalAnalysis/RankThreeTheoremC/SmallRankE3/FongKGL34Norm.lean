module

public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherGraphFieldInvolution

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3

theorem image_fixedPoints_conj {K : Type*} [Group K] (Ψ σ : MulAut K) :
    (Ψ : K → K) '' {x : K | σ x = x} = {x : K | (Ψ * σ * Ψ⁻¹) x = x} := by
  ext y
  simp only [Set.mem_image, Set.mem_setOf_eq, MulAut.mul_apply]
  constructor
  · rintro ⟨x, hx, rfl⟩
    simp [hx]
  · intro hy
    refine ⟨Ψ⁻¹ y, ?_, by simp⟩
    apply Ψ.injective
    simpa using hy

theorem closure_fixedPoints_conj {K : Type*} [Group K] (Ψ σ₁ σ₂ : MulAut K) :
    Subgroup.closure ({x : K | (Ψ * σ₁ * Ψ⁻¹) x = x} ∪ {x : K | (Ψ * σ₂ * Ψ⁻¹) x = x}) =
      (Subgroup.closure ({x : K | σ₁ x = x} ∪ {x : K | σ₂ x = x})).map (Ψ : K →* K) := by
  rw [MonoidHom.map_closure, Set.image_union, ← image_fixedPoints_conj, ← image_fixedPoints_conj]
  rfl

open Subgroup Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag


theorem symmetric_of_graph_involution {n : ℕ} {F : Type*} [Field F] [Finite F] [CharP F 2]
    (hn : 3 ≤ n) (C : GL (Fin n) F)
    (h : (conjAut n F C * dualAut n F) * (conjAut n F C * dualAut n F) = 1) :
    ∀ i j, (C : Matrix (Fin n) (Fin n) F) i j = (C : Matrix (Fin n) (Fin n) F) j i := by
  have hδδ : dualAut n F * dualAut n F = 1 :=
    (standard_automorphism_transport (K := F) (n := n)).2.2.2.1
  have h2 : (conjAut n F C * dualAut n F) * (conjAut n F C * dualAut n F) =
      conjAut n F (C * GeneralLinearGroup.inverseTranspose C) := by
    calc (conjAut n F C * dualAut n F) * (conjAut n F C * dualAut n F)
        = conjAut n F C * (dualAut n F * conjAut n F C) * dualAut n F := by group
      _ = conjAut n F C * (conjAut n F (GeneralLinearGroup.inverseTranspose C) * dualAut n F) *
            dualAut n F := by rw [dualAut_mul_conjAut]
      _ = conjAut n F C * conjAut n F (GeneralLinearGroup.inverseTranspose C) *
            (dualAut n F * dualAut n F) := by group
      _ = conjAut n F (C * GeneralLinearGroup.inverseTranspose C) := by
        rw [hδδ, mul_one, map_mul]
  rw [h2] at h
  obtain ⟨-, ν, hν⟩ := eq_one_of_conjAut_mul_fieldAut_eq_one hn
    (C * GeneralLinearGroup.inverseTranspose C) 1 (by rw [map_one, mul_one]; exact h)
  have h2F : (2 : F) = 0 := by exact_mod_cast CharP.cast_eq_zero F 2
  set M : Matrix (Fin n) (Fin n) F := (C : Matrix (Fin n) (Fin n) F) with hM
  set N : Matrix (Fin n) (Fin n) F := ((C⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) with hN
  have hMN : M * N = 1 := C.mul_inv
  have hscal : M * Nᵀ = (ν : F) • (1 : Matrix (Fin n) (Fin n) F) := by
    have := congrArg (fun g : GL (Fin n) F => (g : Matrix (Fin n) (Fin n) F)) hν
    simp only [GeneralLinearGroup.coe_scalar, Units.val_mul,
      GeneralLinearGroup.coe_inverseTranspose] at this
    rw [← this, Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]
  have hNtMt : Nᵀ * Mᵀ = 1 := by
    rw [← Matrix.transpose_mul, hMN, Matrix.transpose_one]
  have h3 : M = (ν : F) • Mᵀ := by
    have := congrArg (fun X => X * Mᵀ) hscal
    simp only [Matrix.mul_assoc, hNtMt, Matrix.mul_one, Matrix.smul_mul, Matrix.one_mul] at this
    exact this
  have h4 : Mᵀ = (ν : F) • M := by
    have := congrArg Matrix.transpose h3
    rwa [Matrix.transpose_smul, Matrix.transpose_transpose] at this
  have h5 : M = ((ν : F) * ν) • M := by
    calc M = (ν : F) • Mᵀ := h3
      _ = (ν : F) • ((ν : F) • M) := by rw [← h4]
      _ = ((ν : F) * ν) • M := by rw [smul_smul]
  have hν2 : (ν : F) * ν = 1 := by
    have := congrArg (fun X => X * N) h5
    simp only [Matrix.smul_mul, hMN] at this
    have h00 := congrFun (congrFun this ⟨0, by omega⟩) ⟨0, by omega⟩
    simpa using h00.symm
  have hν1 : (ν : F) = 1 := by
    have hsq : ((ν : F) + 1) ^ 2 = 0 := by
      linear_combination hν2 + ((ν : F) + 1) * h2F
    have hz : (ν : F) + 1 = 0 := pow_eq_zero_iff (two_ne_zero) |>.mp hsq
    linear_combination hz - h2F
  intro i j
  have := congrFun (congrFun h3 i) j
  rw [hν1, one_smul] at this
  simpa using this

theorem rational_of_map_eq_mul_scalar {n k : ℕ} {F : Type*} [Field F] (hn : 3 ≤ n)
    (h : UnitaryFieldData 2 k F) (φ : F ≃+* F) (hφ : ∀ x, φ x = h.bar x) (A' : GL (Fin n) F)
    (c : Fˣ)
    (hA : GeneralLinearGroup.map (φ : F →+* F) A' = A' * GeneralLinearGroup.scalar (Fin n) c) :
    ∃ C : GL (Fin n) F,
      (∀ i j, φ ((C : Matrix (Fin n) (Fin n) F) i j) = (C : Matrix (Fin n) (Fin n) F) i j) ∧
        conjAut n F C = conjAut n F A' := by
  have hφφ : ∀ x, φ (φ x) = x := fun x => by rw [hφ, hφ, h.bar_bar]
  set M : Matrix (Fin n) (Fin n) F := (A' : Matrix (Fin n) (Fin n) F) with hM
  have hent : ∀ i j, φ (M i j) = (c : F) * M i j := by
    intro i j
    have := congrArg (fun g : GL (Fin n) F => (g : Matrix (Fin n) (Fin n) F) i j) hA
    simp only [GeneralLinearGroup.map_apply, Units.val_mul, GeneralLinearGroup.coe_scalar,
      Matrix.mul_apply, Matrix.scalar_apply, Matrix.diagonal_apply] at this
    simp only [RingHom.coe_coe] at this
    simpa [mul_comm] using this
  have hmat : M.map φ = (c : F) • M := Matrix.ext hent
  have h2 : M = (φ c * c) • M := by
    calc M = (M.map φ).map φ := by ext i j; simp [hφφ]
      _ = ((c : F) • M).map φ := by rw [hmat]
      _ = (φ c * c) • M := by ext i j; simp [hent]; ring
  have hN1 : φ c * c = 1 := by
    have := congrArg (fun X => X * ((A'⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)) h2
    simp only [Matrix.smul_mul, hM, A'.mul_inv] at this
    have h00 := congrFun (congrFun this ⟨0, by omega⟩) ⟨0, by omega⟩
    simpa using h00.symm
  have hu : h.norm (c : F) = 1 := by
    show (c : F) * h.bar c = 1
    rw [← hφ]
    linear_combination hN1
  obtain ⟨r, hr0, hr⟩ := h.exists_div_bar_eq hu
  have hφr0 : φ r ≠ 0 := (map_ne_zero φ).mpr hr0
  have hcr : (c : F) = r / φ r := by rw [← hφ] at hr; exact hr.symm
  refine ⟨GeneralLinearGroup.scalar (Fin n) (Units.mk0 r hr0) * A', ?_, ?_⟩
  · intro i j
    have hC : ((GeneralLinearGroup.scalar (Fin n) (Units.mk0 r hr0) * A' : GL (Fin n) F) :
        Matrix (Fin n) (Fin n) F) i j = r * M i j := by
      simp [Units.val_mul, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, hM]
    rw [hC, map_mul, hent, hcr]
    field_simp
  · rw [map_mul, conjAut_scalar, one_mul]

theorem graph_normal_form {n k : ℕ} {F : Type*} [Field F] [Finite F] (hn : 3 ≤ n) (hk : 1 ≤ k)
    (hF : Nat.card F = 2 ^ (2 * k)) (φ : F ≃+* F) (hφ : ∀ x, φ x = x ^ 2 ^ k)
    (H A : GL (Fin n) F)
    (hcomm : (conjAut n F H * fieldAut n F φ * (conjAut n F H)⁻¹) * (conjAut n F A * dualAut n F) =
      (conjAut n F A * dualAut n F) * (conjAut n F H * fieldAut n F φ * (conjAut n F H)⁻¹))
    (hinv : (conjAut n F A * dualAut n F) * (conjAut n F A * dualAut n F) = 1) :
    ∃ C : GL (Fin n) F,
      (∀ i j, φ ((C : Matrix (Fin n) (Fin n) F) i j) = (C : Matrix (Fin n) (Fin n) F) i j) ∧
      (∀ i j, (C : Matrix (Fin n) (Fin n) F) i j = (C : Matrix (Fin n) (Fin n) F) j i) ∧
      (conjAut n F H)⁻¹ * (conjAut n F A * dualAut n F) * conjAut n F H =
        conjAut n F C * dualAut n F := by
  have hU : UnitaryFieldData 2 k F := ⟨Nat.prime_two, hk, by rw [hF]⟩
  haveI : CharP F 2 := hU.charP
  have hφbar : ∀ x, φ x = hU.bar x := fun x => by rw [hφ, hU.bar_apply]
  set c := conjAut n F H with hc
  set s := conjAut n F A * dualAut n F with hs
  set f := fieldAut n F φ with hf
  set A' : GL (Fin n) F := H⁻¹ * A * GeneralLinearGroup.inverseTranspose H with hA'
  have hg' : c⁻¹ * s * c = conjAut n F A' * dualAut n F := by
    calc c⁻¹ * s * c = c⁻¹ * conjAut n F A * (dualAut n F * c) := by rw [hs, hc]; group
      _ = c⁻¹ * conjAut n F A * (conjAut n F (GeneralLinearGroup.inverseTranspose H) *
            dualAut n F) := by rw [hc, dualAut_mul_conjAut]
      _ = conjAut n F A' * dualAut n F := by
        rw [hA', hc, map_mul, map_mul, map_inv]; group
  have hfg' : f * (c⁻¹ * s * c) = (c⁻¹ * s * c) * f := by
    calc f * (c⁻¹ * s * c) = c⁻¹ * (c * f * c⁻¹ * s) * c := by group
      _ = c⁻¹ * (s * (c * f * c⁻¹)) * c := by rw [hcomm]
      _ = (c⁻¹ * s * c) * f := by group
  have h5 : conjAut n F (GeneralLinearGroup.map (φ : F →+* F) A') = conjAut n F A' := by
    rw [hg'] at hfg'
    have e1 : f * (conjAut n F A' * dualAut n F) =
        conjAut n F (GeneralLinearGroup.map (φ : F →+* F) A') * (f * dualAut n F) := by
      rw [← mul_assoc, hf, fieldAut_mul_conjAut, mul_assoc]
    have e2 : (conjAut n F A' * dualAut n F) * f = conjAut n F A' * (f * dualAut n F) := by
      rw [mul_assoc, hf, dualAut_mul_fieldAut]
    rw [e1, e2] at hfg'
    exact mul_right_cancel hfg'
  obtain ⟨-, c0, hc0⟩ := eq_one_of_conjAut_mul_fieldAut_eq_one hn
    (A'⁻¹ * GeneralLinearGroup.map (φ : F →+* F) A') 1
    (by rw [map_one, mul_one, map_mul, map_inv, h5, inv_mul_cancel])
  have hA : GeneralLinearGroup.map (φ : F →+* F) A' = A' * GeneralLinearGroup.scalar (Fin n) c0 := by
    rw [hc0]; group
  obtain ⟨C, hCφ, hCc⟩ := rational_of_map_eq_mul_scalar hn hU φ hφbar A' c0 hA
  refine ⟨C, hCφ, ?_, ?_⟩
  · apply symmetric_of_graph_involution hn C
    rw [hCc, ← hg']
    calc c⁻¹ * s * c * (c⁻¹ * s * c) = c⁻¹ * (s * s) * c := by group
      _ = 1 := by rw [hinv]; group
  · rw [hg', hCc]

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3
