module

public import CFSG.GH74.Generic.BProg.B2.GenLocU4GenBase

public section

namespace CFSG.GH74.Generic.BProg.B2

open Matrix CFSG CFSG.GH74 CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Phan
  CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits CFSG.RankThree.PartTwo.KFacts CFSG.RankThree.PartOne
  CFSG.RankThree.PartOne.KCUnitaryModel CFSG.GH74.Generic.BProg.B2.GenLocU3Lift Subgroup
  CFSG.GH74.Generic.BProg.B2.GenLocU4Aux CFSG.ClassicalGroups.Unitary CFSG.LieType.Steinberg
open scoped MatrixGroups

namespace GenLocU4Gen

section Generic2

variable {K : Type} [Field K]

@[expose] def idx4 (i : Fin 3) (x : Fin 2) : Fin 4 := ⟨i.val + x.val, by omega⟩

theorem diag_mul_blockMat4 (d : Fin 4 → K) (hd : ∀ k, d k ≠ 0) (i : Fin 3) (Y : Matrix (Fin 2) (Fin 2) K) :
    Matrix.diagonal d * blockMat 4 i.val Y =
      blockMat 4 i.val (Matrix.diagonal (fun x => d (idx4 i x)) * Y *
        Matrix.diagonal (fun x => (d (idx4 i x))⁻¹)) * Matrix.diagonal d := by
  ext a b
  rw [Matrix.diagonal_mul, Matrix.mul_diagonal, blockMat_apply, blockMat_apply]
  by_cases h : (i.val ≤ a.val ∧ a.val < i.val + 2) ∧ (i.val ≤ b.val ∧ b.val < i.val + 2)
  · rw [dite_eq_left h, dite_eq_left h]
    have ha : idx4 i ⟨a.val - i.val, by omega⟩ = a := Fin.ext (by simp [idx4]; omega)
    have hb : idx4 i ⟨b.val - i.val, by omega⟩ = b := Fin.ext (by simp [idx4]; omega)
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
    simp only [ha, hb]
    have := hd b
    field_simp
  · rw [dite_eq_right h, dite_eq_right h]
    simp only [Matrix.one_apply]
    by_cases hab : a = b
    · subst hab; simp
    · simp [hab]

theorem blockMat4_injective (i : Fin 3) {B1 B2 : Matrix (Fin 2) (Fin 2) K}
    (h : blockMat 4 i.val B1 = blockMat 4 i.val B2) : B1 = B2 := by
  ext a b
  have := congrFun (congrFun h ⟨i.val + a.val, by omega⟩) ⟨i.val + b.val, by omega⟩
  rw [blockMat_apply, blockMat_apply] at this
  have hc : (i.val ≤ i.val + a.val ∧ i.val + a.val < i.val + 2) ∧ (i.val ≤ i.val + b.val ∧ i.val + b.val < i.val + 2) :=
    ⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩⟩
  rw [dite_eq_left hc, dite_eq_left hc] at this
  have ha : (⟨i.val + a.val - i.val, by omega⟩ : Fin 2) = a := Fin.ext (by simp)
  have hb : (⟨i.val + b.val - i.val, by omega⟩ : Fin 2) = b := Fin.ext (by simp)
  simpa [ha, hb] using this

end Generic2

section Diag4

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]

theorem block_action_diag (hK : Nat.card K = (p ^ f) ^ 2) (P : GL (Fin 4) K)
    (hP : ((P : Matrix (Fin 4) (Fin 4) K).map (· ^ (p ^ f)))ᵀ * (P : Matrix (Fin 4) (Fin 4) K) = 1) (i : Fin 3)
    (ρ : GL (Fin 4) K) (d : Fin 4 → K) (hd0 : ∀ j, d j ≠ 0)
    (hρ : ((P⁻¹ * ρ * P : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = Matrix.diagonal d)
    (x x' : Su K p f 2)
    (hx : ρ * (frameBlock hK P hP i x : GL (Fin 4) K) * ρ⁻¹ = (frameBlock hK P hP i x' : GL (Fin 4) K)) :
    ((x' : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
      Matrix.diagonal (fun k => d (idx4 i k)) * ((x : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *
        Matrix.diagonal (fun k => (d (idx4 i k))⁻¹) := by
  have hX' : ((blockEmb2 K p f 3 i x' : Su K p f 4) : GL (Fin 4) K) =
      (P⁻¹ * ρ * P) * ((blockEmb2 K p f 3 i x : Su K p f 4) : GL (Fin 4) K) * (P⁻¹ * ρ * P)⁻¹ := by
    have h1 : ((blockEmb2 K p f 3 i x' : Su K p f 4) : GL (Fin 4) K) =
        P⁻¹ * (frameBlock hK P hP i x' : GL (Fin 4) K) * P := by
      show _ = P⁻¹ * (P * ((blockEmb2 K p f 3 i x' : Su K p f 4) : GL (Fin 4) K) * P⁻¹) * P
      group
    rw [h1, ← hx]
    show P⁻¹ * (ρ * (P * ((blockEmb2 K p f 3 i x : Su K p f 4) : GL (Fin 4) K) * P⁻¹) * ρ⁻¹) * P = _
    group
  generalize P⁻¹ * ρ * P = Dg at hX' hρ
  have hDinv : ((Dg⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = Matrix.diagonal (fun k => (d k)⁻¹) := by
    rw [Matrix.coe_units_inv, hρ]
    apply Matrix.inv_eq_right_inv
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext k
    exact mul_inv_cancel₀ (hd0 k)
  have hmat : blockMat 4 i.val ((x' : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
      Matrix.diagonal d * blockMat 4 i.val ((x : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *
        Matrix.diagonal (fun k => (d k)⁻¹) := by
    have := congrArg (fun u : GL (Fin 4) K => (u : Matrix (Fin 4) (Fin 4) K)) hX'
    simp only [Units.val_mul, hDinv, hρ, coe_coe_blockEmb2] at this
    exact this
  rw [diag_mul_blockMat4 d hd0 i, Matrix.mul_assoc, Matrix.diagonal_mul_diagonal] at hmat
  have hone : (Matrix.diagonal (fun k => d k * (d k)⁻¹) : Matrix (Fin 4) (Fin 4) K) = 1 := by
    rw [← Matrix.diagonal_one]
    congr 1
    funext k
    exact mul_inv_cancel₀ (hd0 k)
  rw [hone, Matrix.mul_one] at hmat
  exact blockMat4_injective i hmat

theorem block_action_twisted (hK : Nat.card K = (p ^ f) ^ 2) (P : GL (Fin 4) K)
    (hP : ((P : Matrix (Fin 4) (Fin 4) K).map (· ^ (p ^ f)))ᵀ * (P : Matrix (Fin 4) (Fin 4) K) = 1) (i : Fin 3)
    (ψ : K ≃+* K) (A : GL (Fin 4) K) (d : Fin 4 → K) (hd0 : ∀ j, d j ≠ 0)
    (hA : ((P⁻¹ * A * glAut ψ P : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = Matrix.diagonal d)
    (x x' : Su K p f 2)
    (hx : A * glAut ψ (frameBlock hK P hP i x : GL (Fin 4) K) * A⁻¹ = (frameBlock hK P hP i x' : GL (Fin 4) K)) :
    ((x' : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
      Matrix.diagonal (fun k => d (idx4 i k)) * ((x : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).map ψ *
        Matrix.diagonal (fun k => (d (idx4 i k))⁻¹) := by
  have hX' : ((blockEmb2 K p f 3 i x' : Su K p f 4) : GL (Fin 4) K) =
      (P⁻¹ * A * glAut ψ P) * glAut ψ ((blockEmb2 K p f 3 i x : Su K p f 4) : GL (Fin 4) K) *
        (P⁻¹ * A * glAut ψ P)⁻¹ := by
    have h1 : ((blockEmb2 K p f 3 i x' : Su K p f 4) : GL (Fin 4) K) =
        P⁻¹ * (frameBlock hK P hP i x' : GL (Fin 4) K) * P := by
      show _ = P⁻¹ * (P * ((blockEmb2 K p f 3 i x' : Su K p f 4) : GL (Fin 4) K) * P⁻¹) * P
      group
    rw [h1, ← hx]
    show P⁻¹ * (A * glAut ψ (P * ((blockEmb2 K p f 3 i x : Su K p f 4) : GL (Fin 4) K) * P⁻¹) * A⁻¹) * P = _
    simp only [map_mul, map_inv]
    group
  generalize P⁻¹ * A * glAut ψ P = Dg at hX' hA
  have hDinv : ((Dg⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = Matrix.diagonal (fun k => (d k)⁻¹) := by
    rw [Matrix.coe_units_inv, hA]
    apply Matrix.inv_eq_right_inv
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext k
    exact mul_inv_cancel₀ (hd0 k)
  have hmat : blockMat 4 i.val ((x' : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
      Matrix.diagonal d * blockMat 4 i.val (((x : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).map ψ) *
        Matrix.diagonal (fun k => (d k)⁻¹) := by
    have := congrArg (fun u : GL (Fin 4) K => (u : Matrix (Fin 4) (Fin 4) K)) hX'
    simp only [Units.val_mul, hDinv, hA, coe_glAut, coe_coe_blockEmb2] at this
    rw [GenLocU3Blk.map_blockMat ψ i.val] at this
    exact this
  rw [diag_mul_blockMat4 d hd0 i, Matrix.mul_assoc, Matrix.diagonal_mul_diagonal] at hmat
  have hone : (Matrix.diagonal (fun k => d k * (d k)⁻¹) : Matrix (Fin 4) (Fin 4) K) = 1 := by
    rw [← Matrix.diagonal_one]
    congr 1
    funext k
    exact mul_inv_cancel₀ (hd0 k)
  rw [hone, Matrix.mul_one] at hmat
  exact blockMat4_injective i hmat

theorem exists_block_conj4 (h : UnitaryFieldData p f K) {Δ : GL (Fin 4) K}
    (hΔ : ((Δ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).IsDiag)
    (hΔu : (((Δ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).map h.bar)ᵀ *
      ((Δ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = 1)
    (ψ : K ≃+* K) (i : Fin 3) (y : Su K p f 2) :
    ∃ y' : Su K p f 2, Δ * glAut ψ ((blockEmb2 K p f 3 i y : Su K p f 4) : GL (Fin 4) K) * Δ⁻¹ =
      ((blockEmb2 K p f 3 i y' : Su K p f 4) : GL (Fin 4) K) := by
  classical
  obtain ⟨d, hDd⟩ : ∃ d : Fin 4 → K, Matrix.diagonal d = (Δ : Matrix (Fin 4) (Fin 4) K) :=
    ⟨_, hΔ.diagonal_diag⟩
  have hdn : ∀ k, h.bar (d k) * d k = 1 := by
    intro k
    have h1 := hΔu
    rw [← hDd, Matrix.diagonal_map (map_zero _), Matrix.diagonal_transpose,
      Matrix.diagonal_mul_diagonal] at h1
    have := congrFun (congrFun h1 k) k
    simpa using this
  have hd0 : ∀ k, d k ≠ 0 := by
    intro k h0
    have := hdn k
    rw [h0, map_zero, zero_mul] at this
    exact zero_ne_one this
  set d2 : Fin 2 → K := fun x => d (idx4 i x) with hd2
  let D2 : GL (Fin 2) K := ⟨Matrix.diagonal d2, Matrix.diagonal (fun x => (d2 x)⁻¹),
    by rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]; congr 1; ext x
       exact mul_inv_cancel₀ (hd0 _),
    by rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]; congr 1; ext x
       exact inv_mul_cancel₀ (hd0 _)⟩
  have hY : (y : GL (Fin 2) K) ∈ unitarySU p f K 2 := (GenLocU3Blk.suEquiv h 2 y).2
  have hY1 : glAut ψ (y : GL (Fin 2) K) ∈ unitarySU p f K 2 := by
    rw [unitarySU_eq_gramSU h 2] at hY ⊢
    exact glAut_mem_gramSU h (isPrimeFormGram_one (n := 2)) ψ (by simpa using hY)
  have hD2u : D2 ∈ primeFormUnitary h (idGram K 2) := by
    rw [mem_primeFormUnitary]
    change ((Matrix.diagonal d2).map h.bar)ᵀ * idGram K 2 * Matrix.diagonal d2 = idGram K 2
    simp only [idGram, Units.val_one, Matrix.mul_one]
    rw [Matrix.diagonal_map (map_zero _), Matrix.diagonal_transpose, Matrix.diagonal_mul_diagonal,
      ← Matrix.diagonal_one]
    congr 1; ext x
    exact hdn _
  have hY2 := KFU.conj_mem_unitarySU h hD2u hY1
  refine ⟨(GenLocU3Blk.suEquiv h 2).symm ⟨D2 * glAut ψ (y : GL (Fin 2) K) * D2⁻¹, hY2⟩, ?_⟩
  rw [mul_inv_eq_iff_eq_mul]
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, coe_glAut]
  rw [← hDd]
  change Matrix.diagonal d * ((blockMat 4 i.val (((y : Su K p f 2) : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)).map ψ) =
    blockMat 4 i.val ((D2 * glAut ψ (y : GL (Fin 2) K) * D2⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * Matrix.diagonal d
  rw [GenLocU3Blk.map_blockMat ψ i.val, diag_mul_blockMat4 d hd0 i]
  congr 2


theorem exists_frameBlock_conj (hK : Nat.card K = (p ^ f) ^ 2) (P : GL (Fin 4) K)
    (hP : ((P : Matrix (Fin 4) (Fin 4) K).map (· ^ (p ^ f)))ᵀ * (P : Matrix (Fin 4) (Fin 4) K) = 1) (i : Fin 3)
    (ψ : K ≃+* K) (A : GL (Fin 4) K) (d : Fin 4 → K) (hd : ∀ j, d j ^ (p ^ f) * d j = 1)
    (hA : ((P⁻¹ * A * glAut ψ P : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = Matrix.diagonal d)
    (x : Su K p f 2) :
    ∃ x' : Su K p f 2, A * glAut ψ (frameBlock hK P hP i x : GL (Fin 4) K) * A⁻¹ =
      (frameBlock hK P hP i x' : GL (Fin 4) K) := by
  have hΔu : (((P⁻¹ * A * glAut ψ P : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).map (fieldData hK).bar)ᵀ *
      ((P⁻¹ * A * glAut ψ P : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = 1 := by
    rw [hA, Matrix.diagonal_map (map_zero _), Matrix.diagonal_transpose, Matrix.diagonal_mul_diagonal,
      ← Matrix.diagonal_one]
    congr 1
    funext k
    exact hd k
  obtain ⟨x', hx'⟩ := exists_block_conj4 (fieldData hK) (Δ := P⁻¹ * A * glAut ψ P)
    (by rw [hA]; exact Matrix.isDiag_diagonal d) hΔu ψ i x
  refine ⟨x', ?_⟩
  show A * glAut ψ (P * ((blockEmb2 K p f 3 i x : Su K p f 4) : GL (Fin 4) K) * P⁻¹) * A⁻¹ =
    P * ((blockEmb2 K p f 3 i x' : Su K p f 4) : GL (Fin 4) K) * P⁻¹
  rw [← hx']
  simp only [map_mul, map_inv]
  group

theorem inBlock_twisted (hK : Nat.card K = (p ^ f) ^ 2) (P : GL (Fin 4) K)
    (hP : ((P : Matrix (Fin 4) (Fin 4) K).map (· ^ (p ^ f)))ᵀ * (P : Matrix (Fin 4) (Fin 4) K) = 1) (i : Fin 3)
    (ψ : K ≃+* K) (A : GL (Fin 4) K) (d : Fin 4 → K) (hd : ∀ j, d j ^ (p ^ f) * d j = 1)
    (hA : ((P⁻¹ * A * glAut ψ P : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = Matrix.diagonal d)
    (g g' : ↥(StatedSU 4 (p ^ f) K)) (hg : InBlock (p ^ f) P i.val g)
    (hg' : (g' : GL (Fin 4) K) = A * glAut ψ (g : GL (Fin 4) K) * A⁻¹) : InBlock (p ^ f) P i.val g' := by
  obtain ⟨x, rfl⟩ := exists_frameBlock_of_inBlock hK P hP i g hg
  obtain ⟨x', hx'⟩ := exists_frameBlock_conj hK P hP i ψ A d hd hA x
  have h1 : g' = frameBlock hK P hP i x' := Subtype.ext (by rw [hg']; exact hx')
  rw [h1]
  exact frameBlock_inBlock hK P hP i x'

end Diag4

section Su2

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]

theorem su2_map_bar (x : Su K p f 2) :
    ((x : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).map (· ^ (p ^ f)) =
      !![0, 1; -1, 0] * ((x : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * !![0, -1; 1, 0] := by
  obtain ⟨hdet, hu⟩ := su2_prop (p := p) (f := f) x
  set X : Matrix (Fin 2) (Fin 2) K := ((x : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) with hX
  have hinv : X⁻¹ = (X.map (· ^ (p ^ f)))ᵀ := Matrix.inv_eq_left_inv hu
  have hadj : X⁻¹ = Matrix.adjugate X := by
    rw [Matrix.inv_def, hdet, Ring.inverse_one, one_smul]
  rw [hadj, Matrix.adjugate_fin_two] at hinv
  have h00 := congrFun (congrFun hinv 0) 0
  have h01 := congrFun (congrFun hinv 0) 1
  have h10 := congrFun (congrFun hinv 1) 0
  have h11 := congrFun (congrFun hinv 1) 1
  simp at h00 h01 h10 h11
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct]
  · exact h00.symm
  · linear_combination -h10
  · linear_combination -h01
  · exact h11.symm

theorem commutant_su2_scalar (hK : Nat.card K = (p ^ f) ^ 2) (hp2 : p ≠ 2) (h5 : 3 ≤ p ^ f)
    (t : Matrix (Fin 2) (Fin 2) K)
    (h : ∀ g : Su K p f 2, t * ((g : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
      ((g : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * t) :
    ∃ lam : K, t = lam • (1 : Matrix (Fin 2) (Fin 2) K) := by
  have hσ := isUnitaryInvolution_unitaryInvolution (K := K) (p := p) (f := f) hK
  have hinv := hσ.invol
  obtain ⟨ε, hε, hε2⟩ := exists_unit_scalar_sq_ne_one hK h5
  obtain ⟨c, s, hc, hs, hcs, hs0⟩ := exists_rot_pair hK hp2 h5
  have hε' : unitaryInvolution K p f ε * ε = 1 := by rw [unitaryInvolution_apply K p f]; exact hε
  have hn1 : unitaryInvolution K p f ε * ε + unitaryInvolution K p f 0 * 0 = 1 := by
    rw [map_zero]; linear_combination hε'
  have hnorm : unitaryInvolution K p f c * c + unitaryInvolution K p f s * s = 1 := by
    rw [hc, hs]; linear_combination hcs
  have hd := h (su2Of hinv ε 0 hn1)
  have hr := h (su2Of hinv c s hnorm)
  rw [su2Of_apply] at hd
  rw [su2Of_apply, hs, hc] at hr
  have hd01 := congrFun (congrFun hd 0) 1
  have hd10 := congrFun (congrFun hd 1) 0
  have hr01 := congrFun (congrFun hr 0) 1
  simp [Matrix.mul_apply, Fin.sum_univ_two] at hd01 hd10 hr01
  have hσε : unitaryInvolution K p f ε = ε⁻¹ := eq_inv_of_mul_eq_one_left hε'
  have hε0 : ε ≠ 0 := by
    rintro rfl
    simp at hε'
  have hne : ε⁻¹ - ε ≠ 0 := by
    intro h0
    apply hε2
    field_simp at h0
    linear_combination -h0
  have e1 : (iterateFrobenius K p f) ε = ε⁻¹ := hσε
  rw [e1] at hd01 hd10
  have t01 : t 0 1 = 0 := by
    have : t 0 1 * (ε⁻¹ - ε) = 0 := by linear_combination hd01
    exact (mul_eq_zero.1 this).resolve_right hne
  have t10 : t 1 0 = 0 := by
    have : t 1 0 * (ε - ε⁻¹) = 0 := by linear_combination hd10
    exact (mul_eq_zero.1 this).resolve_right (by
      intro h0; apply hne; linear_combination -h0)
  have t00 : t 0 0 = t 1 1 := by
    rw [t01] at hr01
    have : s * (t 0 0 - t 1 1) = 0 := by linear_combination hr01
    have := (mul_eq_zero.1 this).resolve_left hs0
    linear_combination this
  refine ⟨t 0 0, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;> simp [t01, t10, t00]

theorem conj_ne_of_det (hK : Nat.card K = (p ^ f) ^ 2) (hp2 : p ≠ 2) (h5 : 3 ≤ p ^ f) (M : GL (Fin 2) K)
    (hMu : ((M : Matrix (Fin 2) (Fin 2) K).map (· ^ (p ^ f)))ᵀ * (M : Matrix (Fin 2) (Fin 2) K) = 1)
    (β : MulAut (Su K p f 2))
    (hβ : ∀ g : Su K p f 2, (((β g : Su K p f 2) : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
      (M : Matrix (Fin 2) (Fin 2) K) * ((g : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *
        ((M⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K))
    (hdet : ∀ lam : K, lam ^ (p ^ f) * lam = 1 → lam * lam ≠ (M : Matrix (Fin 2) (Fin 2) K).det)
    (s : Su K p f 2) : MulAut.conj s ≠ β := by
  intro hs
  have hconj : ∀ g : Su K p f 2, (s : GL (Fin 2) K) * (g : GL (Fin 2) K) * (s : GL (Fin 2) K)⁻¹ =
      M * (g : GL (Fin 2) K) * M⁻¹ := by
    intro g
    have h1 := hβ g
    rw [← hs, MulAut.conj_apply] at h1
    apply Units.ext
    simpa [Units.val_mul] using h1
  have hcomm : ∀ g : Su K p f 2, (((s : GL (Fin 2) K)⁻¹ * M : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *
      ((g : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = ((g : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *
      (((s : GL (Fin 2) K)⁻¹ * M : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) := by
    intro g
    have h' : ((s : GL (Fin 2) K)⁻¹ * M) * (g : GL (Fin 2) K) = (g : GL (Fin 2) K) * ((s : GL (Fin 2) K)⁻¹ * M) := by
      calc ((s : GL (Fin 2) K)⁻¹ * M) * (g : GL (Fin 2) K)
          = (s : GL (Fin 2) K)⁻¹ * (M * (g : GL (Fin 2) K) * M⁻¹) * M := by group
        _ = (s : GL (Fin 2) K)⁻¹ * ((s : GL (Fin 2) K) * (g : GL (Fin 2) K) * (s : GL (Fin 2) K)⁻¹) * M := by
          rw [hconj g]
        _ = (g : GL (Fin 2) K) * ((s : GL (Fin 2) K)⁻¹ * M) := by group
    simpa [Units.val_mul] using congrArg (fun u : GL (Fin 2) K => (u : Matrix (Fin 2) (Fin 2) K)) h'
  obtain ⟨lam, hlam⟩ := commutant_su2_scalar hK hp2 h5 _ hcomm
  have hM : (M : Matrix (Fin 2) (Fin 2) K) = lam • ((s : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) := by
    have : M = (s : GL (Fin 2) K) * ((s : GL (Fin 2) K)⁻¹ * M) := by group
    rw [this, Units.val_mul, hlam, Matrix.mul_smul, Matrix.mul_one]
  obtain ⟨hsd, hsu⟩ := su2_prop (p := p) (f := f) s
  have hdetM : (M : Matrix (Fin 2) (Fin 2) K).det = lam * lam := by
    rw [hM, Matrix.det_smul, hsd]
    simp [sq]
  have hN : lam ^ (p ^ f) * lam = 1 := by
    have h1 := hMu
    have hmap : ((lam • ((s : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)).map (· ^ (p ^ f))) =
        lam ^ (p ^ f) • (((s : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).map (· ^ (p ^ f))) := by
      ext i j
      simp [mul_pow]
    rw [hM, hmap, Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hsu] at h1
    have h2 := congrFun (congrFun h1 0) 0
    simpa using h2
  exact hdet lam hN hdetM.symm

theorem not_range_le_inn_of_block {A : Type} [Group A] (hK : Nat.card K = (p ^ f) ^ 2) (hp2 : p ≠ 2) (h5 : 3 ≤ p ^ f)
    (ψ : K ≃+* K) (hψ : ψ = RingEquiv.refl K ∨ ψ = unitaryInvolution K p f) (e : Fin 2 → K)
    (he : ∀ k, e k ^ (p ^ f) * e k = 1) (hne : ∀ lam : K, lam ^ (p ^ f) * lam = 1 → lam * lam ≠ e 0 * e 1)
    (β : A →* MulAut (Su K p f 2)) (a : A)
    (hβ : ∀ x : Su K p f 2, ((β a x : Su K p f 2) : GL (Fin 2) K).val =
      Matrix.diagonal e * ((x : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).map ψ *
        Matrix.diagonal (fun k => (e k)⁻¹)) :
    ¬ β.range ≤ (MulAut.conj : Su K p f 2 →* MulAut (Su K p f 2)).range := by
  intro hle
  obtain ⟨s, hs⟩ := hle ⟨a, rfl⟩
  have he0 : ∀ k, e k ≠ 0 := by
    intro k h0
    have := he k
    rw [h0, zero_pow (pow_ne_zero _ (Fact.out : p.Prime).ne_zero), zero_mul] at this
    exact zero_ne_one this
  let D2 : GL (Fin 2) K := ⟨Matrix.diagonal e, Matrix.diagonal (fun k => (e k)⁻¹),
    by rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]; congr 1; ext x
       exact mul_inv_cancel₀ (he0 _),
    by rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]; congr 1; ext x
       exact inv_mul_cancel₀ (he0 _)⟩
  have hq0 : p ^ f ≠ 0 := pow_ne_zero _ (Fact.out : p.Prime).ne_zero
  have hmap0 : ((Matrix.diagonal e).map (· ^ (p ^ f)) : Matrix (Fin 2) (Fin 2) K) =
      Matrix.diagonal (fun k => e k ^ (p ^ f)) := by
    ext i j
    by_cases hij : i = j <;> simp [hij, zero_pow hq0]
  rcases hψ with rfl | rfl
  · refine conj_ne_of_det hK hp2 h5 D2 ?_ (β a) ?_ ?_ s hs
    · change ((Matrix.diagonal e).map (· ^ (p ^ f)))ᵀ * Matrix.diagonal e = 1
      rw [hmap0, Matrix.diagonal_transpose, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
      congr 1
      funext k
      exact he k
    · intro g
      rw [hβ g]
      rfl
    · intro lam hlam
      change lam * lam ≠ (Matrix.diagonal e).det
      rw [Matrix.det_diagonal, Fin.prod_univ_two]
      exact hne lam hlam
  · have hodd : Odd (p ^ f) := ((Fact.out : p.Prime).odd_of_ne_two hp2).pow
    let J2 : GL (Fin 2) K := ⟨!![0, 1; -1, 0], !![0, -1; 1, 0],
      by ext i j; fin_cases i <;> fin_cases j <;> simp,
      by ext i j; fin_cases i <;> fin_cases j <;> simp⟩
    have hσfun : (⇑(unitaryInvolution K p f) : K → K) = fun x => x ^ (p ^ f) :=
      funext (unitaryInvolution_apply K p f)
    refine conj_ne_of_det hK hp2 h5 (D2 * J2) ?_ (β a) ?_ ?_ s hs
    · change (((Matrix.diagonal e * !![0, 1; -1, 0] : Matrix (Fin 2) (Fin 2) K)).map (· ^ (p ^ f)))ᵀ *
        (Matrix.diagonal e * !![0, 1; -1, 0]) = 1
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.diagonal_apply, Matrix.map_apply, zero_pow hq0, he 0]
      · rw [Odd.neg_pow hodd]
        linear_combination he 1
    · intro g
      rw [hβ g, hσfun, su2_map_bar g]
      change _ = (Matrix.diagonal e * !![0, 1; -1, 0]) * ((g : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *
        (!![0, -1; 1, 0] * Matrix.diagonal (fun k => (e k)⁻¹))
      simp only [Matrix.mul_assoc]
    · intro lam hlam
      change lam * lam ≠ (Matrix.diagonal e * !![0, 1; -1, 0] : Matrix (Fin 2) (Fin 2) K).det
      rw [Matrix.det_mul, Matrix.det_diagonal, Fin.prod_univ_two]
      simpa [Matrix.det_fin_two_of] using hne lam hlam

end Su2

end GenLocU4Gen

end CFSG.GH74.Generic.BProg.B2
