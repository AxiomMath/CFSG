module

public import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentA6ClPSpSmallBasic
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneSpNormal

public section

namespace CFSG.ComponentClassification.CatFC.PSpSmall

open Matrix Subgroup CFSG CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.ComponentClassification.Burgoyne.Sp (colMat exists_sp_of_gram inv_mul_mul_eq_of_cols
  exists_dual_pair bJ_eq bJ_mulVec_left bJ_mulVec_self form_similitude transpose_mul_formJ)

variable {K : Type} [Field K]

abbrev swapDiag (K : Type) [Field K] : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K :=
  diagonal (Sum.elim ![1, -1] ![1, -1])

theorem swapDiag_mul_self : swapDiag K * swapDiag K = 1 := by
  rw [swapDiag, diagonal_mul_diagonal, ← diagonal_one]
  congr 1
  ext x
  rcases x with x | x <;> fin_cases x <;> simp

theorem swapDiag_isSp : (swapDiag K)ᵀ * formJ 2 K * swapDiag K = formJ 2 K := by
  ext p q
  rw [swapDiag, diagonal_transpose, Matrix.mul_diagonal, Matrix.diagonal_mul]
  rcases p with p | p <;> rcases q with q | q <;> fin_cases p <;> fin_cases q <;>
    simp [formJ, Matrix.one_apply]

abbrev swapBlock (d : K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K :=
  fromBlocks !![0, d; 1, 0] 0 0 !![0, 1; d, 0]

theorem swapDiag_mul_swapBlock (d : K) :
    swapDiag K * swapBlock d = -(swapBlock d * swapDiag K) := by
  ext p q
  rw [swapDiag, Matrix.diagonal_mul, Matrix.neg_apply, Matrix.mul_diagonal]
  rcases p with p | p <;> rcases q with q | q <;> fin_cases p <;> fin_cases q <;>
    simp [swapBlock]

theorem exists_swap_of_selfAdjoint (h2 : (2 : K) ≠ 0) (A : gsp 2 K) {d : K} (hd : ∀ l : K, l ^ 2 ≠ d)
    (hAA : ((A : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *
      ((A : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) = d • 1)
    (hJ : ((A : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)ᵀ * formJ 2 K *
      ((A : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) = d • formJ 2 K) :
    ∃ g : StatedSp 2 K, g * g = 1 ∧
      ((g : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *
        ((A : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) =
      -(((A : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *
        ((g : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)) := by
  set M := ((A : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) with hM
  have hd0 : d ≠ 0 := fun h => hd 0 (by rw [h]; ring)
  have hJA : Mᵀ * formJ 2 K = formJ 2 K * M := transpose_mul_formJ hd0 hJ hAA
  set ω := pairedSympForm K 2 with hω
  have hMM : ∀ w, M *ᵥ (M *ᵥ w) = d • w := fun w => by
    rw [mulVec_mulVec, hAA, smul_mulVec, one_mulVec]
  have F2 : ∀ w w', ω (M *ᵥ w) (M *ᵥ w') = d * ω w w' := form_similitude hJ
  have F1 : ∀ w w', ω (M *ᵥ w) w' = ω w (M *ᵥ w') := fun w w' => by
    rw [← bJ_eq, ← bJ_eq]
    exact bJ_mulVec_left hJA w w'
  have F4 : ∀ w, ω (M *ᵥ w) w = 0 := fun w => by
    rw [← bJ_eq]
    exact bJ_mulVec_self h2 hJA w
  have Fswap : ∀ w w', ω w w' = -ω w' w := fun w w' =>
    (LinearMap.BilinForm.IsAlt.neg_eq pairedSympForm_isAlt w' w).symm
  have F3 : ∀ w, ω w w = 0 := fun w => pairedSympForm_isAlt w
  have F4' : ∀ w, ω w (M *ᵥ w) = 0 := fun w => by rw [Fswap, F4, neg_zero]
  have hsl : ∀ (c : K) w w', ω (c • w) w' = c * ω w w' := fun c w w' => by simp
  have hsr : ∀ (c : K) w w', ω w (c • w') = c * ω w w' := fun c w w' => by simp
  set v : Fin 2 ⊕ Fin 2 → K := Pi.single (Sum.inl 0) 1 with hv
  have hv0 : v ≠ 0 := by
    intro h
    have := congrFun h (Sum.inl 0)
    simp [hv] at this
  obtain ⟨x, hx1, hx2⟩ := exists_dual_pair (A := A) hd hJA hAA hv0
  rw [bJ_eq] at hx1 hx2
  set e₁ : Fin 2 ⊕ Fin 2 → K := M *ᵥ v with he₁
  set e₂ : Fin 2 ⊕ Fin 2 → K := M *ᵥ e₁ with he₂
  set f₁ : Fin 2 ⊕ Fin 2 → K := x with hf₁
  set f₂ : Fin 2 ⊕ Fin 2 → K := d⁻¹ • (M *ᵥ x) with hf₂
  have he₂v : e₂ = d • v := hMM v
  have g11 : ω e₁ e₁ = 0 := F3 _
  have g12 : ω e₁ e₂ = 0 := F4' _
  have g21 : ω e₂ e₁ = 0 := F4 _
  have g22 : ω e₂ e₂ = 0 := F3 _
  have a11 : ω e₁ f₁ = 1 := hx2
  have a12 : ω e₁ f₂ = 0 := by
    rw [hf₂, hsr, ← F1, ← he₂, he₂v, hsl, hx1]
    simp
  have a21 : ω e₂ f₁ = 0 := by
    rw [he₂v, hsl, hx1, mul_zero]
  have a22 : ω e₂ f₂ = 1 := by
    rw [hf₂, hsr, he₂, F2, a11]
    field_simp
  have b11 : ω f₁ e₁ = -1 := by rw [Fswap, a11]
  have b12 : ω f₁ e₂ = 0 := by rw [Fswap, a21, neg_zero]
  have b21 : ω f₂ e₁ = 0 := by rw [Fswap, a12, neg_zero]
  have b22 : ω f₂ e₂ = -1 := by rw [Fswap, a22]
  have k11 : ω f₁ f₁ = 0 := F3 _
  have k12 : ω f₁ f₂ = 0 := by rw [hf₂, hsr, F4', mul_zero]
  have k21 : ω f₂ f₁ = 0 := by rw [hf₂, hsl, F4, mul_zero]
  have k22 : ω f₂ f₂ = 0 := F3 _
  set u : Fin 2 ⊕ Fin 2 → Fin 2 ⊕ Fin 2 → K := Sum.elim ![e₁, e₂] ![f₁, f₂] with hu
  have hgram : ∀ p q, ω (u p) (u q) = formJ 2 K p q := by
    rintro (i | i) (j | j) <;> fin_cases i <;> fin_cases j <;>
      simp [hu, formJ, Matrix.one_apply, g11, g12, g21, g22, a11, a12, a21, a22, b11, b12, b21,
        b22, k11, k12, k21, k22]
  obtain ⟨H, hH⟩ := exists_sp_of_gram hgram
  have hMe₂ : M *ᵥ e₂ = d • e₁ := hMM e₁
  have hMf₁ : M *ᵥ f₁ = d • f₂ := by
    rw [hf₂, smul_smul, mul_inv_cancel₀ hd0, one_smul]
  have hMf₂ : M *ᵥ f₂ = f₁ := by
    rw [hf₂, mulVec_smul, hMM, smul_smul, inv_mul_cancel₀ hd0, one_smul]
  have hcols : ∀ c, M *ᵥ u c = ∑ d', swapBlock d d' c • u d' := by
    rintro (i | i) <;> fin_cases i <;>
      simp [hu, swapBlock, Fintype.sum_sum_type, Fin.sum_univ_two, he₂.symm, hMe₂, hMf₁, hMf₂]
  have hconj := inv_mul_mul_eq_of_cols (H := (H : GL (Fin 2 ⊕ Fin 2) K)) hH hcols
  let g₀ : StatedSp 2 K :=
    ⟨⟨swapDiag K, swapDiag K, swapDiag_mul_self, swapDiag_mul_self⟩,
      SymplecticTorusWeyl.mem_statedSp_iff.mpr swapDiag_isSp⟩
  have hg₀ : g₀ * g₀ = 1 := by
    apply Subtype.ext
    apply Units.ext
    exact swapDiag_mul_self
  refine ⟨H * g₀ * H⁻¹, ?_, ?_⟩
  · calc H * g₀ * H⁻¹ * (H * g₀ * H⁻¹) = H * (g₀ * g₀) * H⁻¹ := by group
      _ = 1 := by rw [hg₀]; group
  · set Hm : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K :=
      ((H : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) with hHm
    set Hi : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K :=
      (((H : GL (Fin 2 ⊕ Fin 2) K)⁻¹ : GL (Fin 2 ⊕ Fin 2) K) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) with hHi
    have hHmHi : Hm * Hi = 1 := by
      rw [hHm, hHi, ← Units.val_mul, mul_inv_cancel, Units.val_one]
    have hHiHm : Hi * Hm = 1 := by
      rw [hHm, hHi, ← Units.val_mul, inv_mul_cancel, Units.val_one]
    have e1 : M * Hm = Hm * swapBlock d := by
      calc M * Hm = (Hm * Hi) * M * Hm := by rw [hHmHi, Matrix.one_mul]
        _ = Hm * (Hi * M * Hm) := by simp only [Matrix.mul_assoc]
        _ = Hm * swapBlock d := by rw [hconj]
    have e2 : Hi * M = swapBlock d * Hi := by
      calc Hi * M = Hi * M * (Hm * Hi) := by rw [hHmHi, Matrix.mul_one]
        _ = (Hi * M * Hm) * Hi := by simp only [Matrix.mul_assoc]
        _ = swapBlock d * Hi := by rw [hconj]
    have hg : (((H * g₀ * H⁻¹ : StatedSp 2 K) : GL (Fin 2 ⊕ Fin 2) K) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) = Hm * swapDiag K * Hi := rfl
    rw [hg]
    calc Hm * swapDiag K * Hi * M = Hm * swapDiag K * (Hi * M) := by rw [Matrix.mul_assoc]
      _ = Hm * (swapDiag K * swapBlock d) * Hi := by rw [e2]; simp only [Matrix.mul_assoc]
      _ = -(Hm * swapBlock d * swapDiag K * Hi) := by
          rw [swapDiag_mul_swapBlock]; simp only [Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc]
      _ = -(M * (Hm * swapDiag K * Hi)) := by rw [← e1]; simp only [Matrix.mul_assoc]

end CFSG.ComponentClassification.CatFC.PSpSmall
