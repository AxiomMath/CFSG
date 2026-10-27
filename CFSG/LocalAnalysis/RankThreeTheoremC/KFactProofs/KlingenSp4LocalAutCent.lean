module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.KlingenSp4LocalLevi
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticHigherAutomorphismData
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticRepresentationOdd

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs

open Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.AGLEmbedding.KlingenSpFour

section Matrix

variable {K : Type} [Field K]

theorem ac_trace_siegel (S : Matrix (Fin 2) (Fin 2) K) :
    (fromBlocks 1 S 0 1 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K).trace = 4 := by
  simp [Matrix.trace, Fintype.sum_sum_type, Fin.sum_univ_two]
  norm_num

theorem ac_comm_of_scalar (M N : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) (hMN : M * N = 1)
    (hNM : N * M = 1) (h4 : (4 : K) ≠ 0) (S : Matrix (Fin 2) (Fin 2) K) (t : K)
    (h : M * fromBlocks 1 S 0 1 = t • (fromBlocks 1 S 0 1 * M)) :
    M * fromBlocks 1 S 0 1 = fromBlocks 1 S 0 1 * M := by
  set X : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K := fromBlocks 1 S 0 1 with hX
  have h1 : M * X * N = t • X := by
    rw [h, Matrix.smul_mul, Matrix.mul_assoc, hMN, Matrix.mul_one]
  have h2 : (M * X * N).trace = X.trace := by
    rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, hNM, Matrix.one_mul]
  rw [h1, Matrix.trace_smul, hX, ac_trace_siegel, smul_eq_mul] at h2
  have ht : t = 1 := mul_right_cancel₀ h4 (by rw [h2, one_mul])
  rw [ht, one_smul] at h
  exact h

theorem ac_scalar_of_comm (P : Matrix (Fin 2) (Fin 2) K)
    (h : ∀ a b c : K, P * S2 a b c = S2 a b c * P) : ∃ l : K, P = l • 1 := by
  refine ⟨P 0 0, ?_⟩
  have e1 := congr_fun (congr_fun (h 1 0 0) 0) 1
  have e2 := congr_fun (congr_fun (h 1 0 0) 1) 0
  have e3 := congr_fun (congr_fun (h 0 1 0) 0) 1
  simp [S2, Matrix.mul_apply, Fin.sum_univ_two] at e1 e2 e3
  ext i j
  fin_cases i <;> fin_cases j <;> simp [← e1, e2, e3, Matrix.one_apply]

theorem ac_block_form (M : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)
    (hcomm : ∀ a b c : K,
      M * fromBlocks 1 (S2 a b c) 0 1 = fromBlocks 1 (S2 a b c) 0 1 * M) :
    ∃ (l : K) (Q : Matrix (Fin 2) (Fin 2) K), M = fromBlocks (l • 1) Q 0 (l • 1) := by
  obtain ⟨P, Q, R, T, rfl⟩ : ∃ P Q R T : Matrix (Fin 2) (Fin 2) K, M = fromBlocks P Q R T :=
    ⟨_, _, _, _, (fromBlocks_toBlocks M).symm⟩
  have key : ∀ a b c : K, S2 a b c * R = 0 ∧ P * S2 a b c = S2 a b c * T := by
    intro a b c
    have h := hcomm a b c
    simp only [fromBlocks_multiply, Matrix.mul_one, Matrix.one_mul, Matrix.mul_zero,
      Matrix.zero_mul, add_zero, zero_add] at h
    obtain ⟨h1, h2, -, -⟩ := fromBlocks_inj.mp h
    exact ⟨by simpa using h1.symm, add_right_cancel (h2.trans (add_comm _ _))⟩
  have hone : (S2 1 0 1 : Matrix (Fin 2) (Fin 2) K) = 1 := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [S2]
  obtain ⟨hR, hPT⟩ := key 1 0 1
  rw [hone, Matrix.one_mul] at hR
  rw [hone, Matrix.mul_one, Matrix.one_mul] at hPT
  subst hR hPT
  obtain ⟨l, rfl⟩ := ac_scalar_of_comm P fun a b c => (key a b c).2
  exact ⟨l, Q, rfl⟩

theorem ac_sympl (l : K) (Q : Matrix (Fin 2) (Fin 2) K) (μ : K)
    (h : (fromBlocks (l • 1) Q 0 (l • 1) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)ᵀ *
      formJ 2 K * fromBlocks (l • 1) Q 0 (l • 1) = μ • formJ 2 K) :
    μ = l ^ 2 ∧ l • Qᵀ = l • Q := by
  simp only [formJ, fromBlocks_transpose, transpose_smul, transpose_one, transpose_zero,
    fromBlocks_multiply, fromBlocks_smul, Matrix.mul_zero, Matrix.zero_mul, Matrix.mul_one,
    Matrix.one_mul, Matrix.mul_neg, Matrix.neg_mul, zero_add, add_zero, smul_zero, smul_neg] at h
  obtain ⟨-, h2, -, h4⟩ := fromBlocks_inj.mp h
  refine ⟨?_, ?_⟩
  · have := congr_fun (congr_fun h2 0) 0
    simp [Matrix.smul_mul, Matrix.mul_smul, smul_smul] at this
    rw [← this]; ring
  · simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one] at h4
    exact (neg_add_eq_zero.mp h4).symm

theorem ac_form (M N : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) (hMN : M * N = 1)
    (hNM : N * M = 1) (h4 : (4 : K) ≠ 0) (μ : Kˣ)
    (hμ : Mᵀ * formJ 2 K * M = (μ : K) • formJ 2 K)
    (hX : ∀ a b c : K, ∃ t : K,
      M * fromBlocks 1 (S2 a b c) 0 1 = t • (fromBlocks 1 (S2 a b c) 0 1 * M)) :
    ∃ (l a b c : K), l ≠ 0 ∧ M = l • fromBlocks 1 (S2 a b c) 0 1 := by
  have hcomm : ∀ a b c : K,
      M * fromBlocks 1 (S2 a b c) 0 1 = fromBlocks 1 (S2 a b c) 0 1 * M := fun a b c => by
    obtain ⟨t, ht⟩ := hX a b c
    exact ac_comm_of_scalar M N hMN hNM h4 _ t ht
  obtain ⟨l, Q, rfl⟩ := ac_block_form M hcomm
  obtain ⟨hμl, hQ⟩ := ac_sympl l Q μ hμ
  have hl : l ≠ 0 := by
    rintro rfl
    exact μ.ne_zero (by rw [hμl]; ring)
  have hQs : Qᵀ = Q := smul_right_injective _ hl hQ
  obtain ⟨q₀, q₁, q₂, rfl⟩ : ∃ q₀ q₁ q₂ : K, Q = S2 q₀ q₁ q₂ := ⟨_, _, _, eq_S2_of_transpose_eq hQs⟩
  refine ⟨l, l⁻¹ * q₀, l⁻¹ * q₁, l⁻¹ * q₂, hl, ?_⟩
  rw [fromBlocks_smul, smul_zero]
  congr 1
  ext i j
  fin_cases i <;> fin_cases j <;> simp [S2, hl]

end Matrix

section Group

variable {r : ℕ} {K : Type} [Field K]

theorem ac_coe_scalar {ι : Type} [Fintype ι] [DecidableEq ι] (c : Kˣ) :
    ((GeneralLinearGroup.scalar ι c : GL ι K) : Matrix ι ι K) = (c : K) • (1 : Matrix ι ι K) := by
  rw [GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]

theorem ac_conj_fix (A : gsp r K) (g : StatedSp r K)
    (hg : conjAut r K A (proj r K g) = proj r K g) :
    ∃ t : K, ((A : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *
        ((g : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) =
      t • (((g : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *
        ((A : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)) := by
  rw [conjAut_proj] at hg
  have h1 := QuotientGroup.eq.mp hg.symm
  rw [Subgroup.mem_subgroupOf, StatedScalars, MonoidHom.mem_range] at h1
  obtain ⟨t, ht⟩ := h1
  refine ⟨t, ?_⟩
  have h2 : ((g⁻¹ * conjSp r K A g : StatedSp r K) : GL (Fin r ⊕ Fin r) K) =
      GeneralLinearGroup.scalar (Fin r ⊕ Fin r) t := ht.symm
  rw [Subgroup.coe_mul, Subgroup.coe_inv, coe_conjSp] at h2
  have h3 : (A : GL (Fin r ⊕ Fin r) K) * g * (A : GL (Fin r ⊕ Fin r) K)⁻¹ =
      g * GeneralLinearGroup.scalar (Fin r ⊕ Fin r) t := by
    rw [← h2]; group
  have h4 : (A : GL (Fin r ⊕ Fin r) K) * g =
      g * GeneralLinearGroup.scalar (Fin r ⊕ Fin r) t * A := by
    calc (A : GL (Fin r ⊕ Fin r) K) * g =
        ((A : GL (Fin r ⊕ Fin r) K) * g * (A : GL (Fin r ⊕ Fin r) K)⁻¹) *
          (A : GL (Fin r ⊕ Fin r) K) := by group
      _ = _ := by rw [h3]
  have h5 := congr_arg (fun x : GL (Fin r ⊕ Fin r) K =>
    (x : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)) h4
  simp only [Units.val_mul, ac_coe_scalar, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul]
    at h5
  exact h5

theorem ac_conjAut_eq (A : gsp 2 K) {l : K} (hl : l ≠ 0) (a b c : K)
    (hA : ((A : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) =
      l • fromBlocks 1 (S2 a b c) 0 1) :
    conjAut 2 K A = MulAut.conj (proj 2 K (xEl a b c)) := by
  set z : GL (Fin 2 ⊕ Fin 2) K := GeneralLinearGroup.scalar (Fin 2 ⊕ Fin 2) (Units.mk0 l hl)
    with hz
  have hzc : ∀ x : GL (Fin 2 ⊕ Fin 2) K, x * z = z * x := fun x =>
    Subgroup.mem_center_iff.mp (by
      rw [GeneralLinearGroup.center_eq_range_scalar]; exact ⟨_, rfl⟩) x
  have hAz : (A : GL (Fin 2 ⊕ Fin 2) K) =
      ((xEl a b c : StatedSp 2 K) : GL (Fin 2 ⊕ Fin 2) K) * z := by
    refine Units.ext ?_
    rw [Units.val_mul, coe_xEl, hA, hz, ac_coe_scalar, Units.val_mk0, Matrix.mul_smul,
      Matrix.mul_one]
  ext y
  obtain ⟨g, rfl⟩ := proj_surjective (r := 2) (K := K) y
  rw [conjAut_proj, MulAut.conj_apply, ← map_inv, ← map_mul, ← map_mul]
  congr 1
  refine Subtype.ext ?_
  rw [coe_conjSp, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, hAz]
  calc _ = ((xEl a b c : StatedSp 2 K) : GL (Fin 2 ⊕ Fin 2) K) * (z * g) *
        (z⁻¹ * ((xEl a b c : StatedSp 2 K) : GL (Fin 2 ⊕ Fin 2) K)⁻¹) := by group
    _ = _ := by rw [← hzc g]; group

end Group

theorem autCent_xS (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (α : MulAut (PSp4 p))
    (h : ∀ u ∈ (xS p).U, α u = u) : ∃ k ∈ (xS p).U, α = MulAut.conj k := by
  obtain ⟨A, σ, hα⟩ :=
    CFSG.ComponentClassification.CatalogueBSymplecticRepresentation.automorphism_standard
      (K := ZMod p) (r := 2) (by rw [ZMod.ringChar_zmod_n]; exact hp2) le_rfl α
  have hσ : σ = 1 := Subsingleton.elim _ _
  rw [hσ, map_one, mul_one] at hα
  have h4 : (4 : ZMod p) ≠ 0 := by
    have : (4 : ZMod p) = 2 * 2 := by norm_num
    rw [this]
    exact mul_ne_zero (two_ne_zero_zmod p hp2) (two_ne_zero_zmod p hp2)
  obtain ⟨μ, hμ⟩ := mem_gsp.mp A.2
  have hX : ∀ a b c : ZMod p, ∃ t : ZMod p,
      ((A : GL (Fin 2 ⊕ Fin 2) (ZMod p)) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (ZMod p)) *
          fromBlocks 1 (S2 a b c) 0 1 =
        t • (fromBlocks 1 (S2 a b c) 0 1 *
          ((A : GL (Fin 2 ⊕ Fin 2) (ZMod p)) :
            Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (ZMod p))) := fun a b c => by
    have := ac_conj_fix A (xEl a b c) (by rw [← hα]; exact h _ ⟨a, b, c, rfl⟩)
    simpa only [coe_xEl] using this
  have hMN : ((A : GL (Fin 2 ⊕ Fin 2) (ZMod p)) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2)
      (ZMod p)) * (((A : GL (Fin 2 ⊕ Fin 2) (ZMod p))⁻¹ : GL (Fin 2 ⊕ Fin 2) (ZMod p)) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (ZMod p)) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hNM : (((A : GL (Fin 2 ⊕ Fin 2) (ZMod p))⁻¹ : GL (Fin 2 ⊕ Fin 2) (ZMod p)) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (ZMod p)) *
        ((A : GL (Fin 2 ⊕ Fin 2) (ZMod p)) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2)
          (ZMod p)) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  obtain ⟨l, a, b, c, hl, hM⟩ := ac_form _ _ hMN hNM h4 μ hμ hX
  exact ⟨(xS p).x a b c, ⟨a, b, c, rfl⟩, hα.trans (ac_conjAut_eq A hl a b c hM)⟩

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs
