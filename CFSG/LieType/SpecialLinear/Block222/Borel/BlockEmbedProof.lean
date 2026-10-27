module

public import CFSG.LieType.SpecialLinear.Block222.Borel.BlockEmbedAux
public import CFSG.LieType.SpecialLinear.Block222.Borel.Std

public section

namespace CFSG.LieType.SpecialLinear

open Matrix CFSG.QuasithinUnique

noncomputable section

variable (c : ℕ) (F : Type) [Field F] (A : GL (Fin (c + 4)) F) (ε : ℕ)

theorem reindexAlgEquiv_map (σ : F ≃+* F)
    (M : Matrix (Fin (c + 4)) (Fin (c + 4)) F) :
    (Matrix.reindexAlgEquiv F F (e222 c).symm) (M.map σ) =
      ((Matrix.reindexAlgEquiv F F (e222 c).symm) M).map σ := by
  ext i j
  rfl

theorem coe_inv_eq_inv {n : ℕ} (h : SpecialLinearGroup (Fin n) F) :
    ((h⁻¹ : SpecialLinearGroup (Fin n) F) : Matrix (Fin n) (Fin n) F) =
      ((h : Matrix (Fin n) (Fin n) F))⁻¹ := by
  exact (Matrix.inv_eq_right_inv (by
    rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
      Matrix.SpecialLinearGroup.coe_one])).symm

theorem borelGraph_pow_eq_one_of_even {n : ℕ} (h : ε % 2 = 0) :
    (borelGraph n F) ^ ε = 1 := by
  rw [pow_eq_pow_mod (a := borelGraph n F) (n := 2) ε (borelGraph_mul_self n (F := F)), h,
    pow_zero]

theorem borelGraph_pow_eq_self_of_odd {n : ℕ} (h : ε % 2 = 1) :
    (borelGraph n F) ^ ε = borelGraph n F := by
  rw [pow_eq_pow_mod (a := borelGraph n F) (n := 2) ε (borelGraph_mul_self n (F := F)), h,
    pow_one]

theorem blockQuotient_of_blockDiagonal (hA : IsUpperGL A) (σ : F ≃+* F)
    (Q : SpecialLinearGroup (Fin (c + 4)) F)
    (x₁ : SpecialLinearGroup (Fin 2) F) (x₂ : SpecialLinearGroup (Fin c) F)
    (x₃ : SpecialLinearGroup (Fin 2) F)
    (hQ : (Matrix.reindexAlgEquiv F F (e222 c).symm)
        (Q : Matrix (Fin (c + 4)) (Fin (c + 4)) F) =
      Matrix.fromBlocks (x₁ : Matrix (Fin 2) (Fin 2) F) 0 0
        (Matrix.fromBlocks (x₂ : Matrix (Fin c) (Fin c) F) 0 0
          (x₃ : Matrix (Fin 2) (Fin 2) F)))
    (gε : SpecialLinearGroup (Fin 2) F × SpecialLinearGroup (Fin c) F ×
      SpecialLinearGroup (Fin 2) F)
    (h₁ : gε.1 = CFSG.QuasithinUnique.K1.stdAut (blockGL1 c F A hA) σ 0 x₁)
    (h₂ : gε.2.1 = CFSG.QuasithinUnique.K1.stdAut (blockGL2 c F A hA) σ 0 x₂)
    (h₃ : gε.2.2 = CFSG.QuasithinUnique.K1.stdAut (blockGL3 c F A hA) σ 0 x₃) :
    (blockEmbed222 c F gε)⁻¹ *
      CFSG.QuasithinUnique.K1.stdAut A σ 0 Q ∈ blockRadical222 c F := by
  let A₁ := blockMat11 c F (A : Matrix (Fin (c + 4)) (Fin (c + 4)) F)
  let A₁₂ := blockMat12 c F (A : Matrix (Fin (c + 4)) (Fin (c + 4)) F)
  let A₂ := blockMat22a c F (A : Matrix (Fin (c + 4)) (Fin (c + 4)) F)
  let A₂₃ := blockMat22b c F (A : Matrix (Fin (c + 4)) (Fin (c + 4)) F)
  let A₃ := blockMat33 c F (A : Matrix (Fin (c + 4)) (Fin (c + 4)) F)
  let A₁' := blockMat11 c F ((A⁻¹ : GL (Fin (c + 4)) F) :
    Matrix (Fin (c + 4)) (Fin (c + 4)) F)
  let A₁₂' := blockMat12 c F ((A⁻¹ : GL (Fin (c + 4)) F) :
    Matrix (Fin (c + 4)) (Fin (c + 4)) F)
  let A₂' := blockMat22a c F ((A⁻¹ : GL (Fin (c + 4)) F) :
    Matrix (Fin (c + 4)) (Fin (c + 4)) F)
  let A₂₃' := blockMat22b c F ((A⁻¹ : GL (Fin (c + 4)) F) :
    Matrix (Fin (c + 4)) (Fin (c + 4)) F)
  let A₃' := blockMat33 c F ((A⁻¹ : GL (Fin (c + 4)) F) :
    Matrix (Fin (c + 4)) (Fin (c + 4)) F)
  let S₁ : Matrix (Fin 2) (Fin 2) F := (x₁ : Matrix (Fin 2) (Fin 2) F).map σ
  let S₂ : Matrix (Fin c) (Fin c) F := (x₂ : Matrix (Fin c) (Fin c) F).map σ
  let S₃ : Matrix (Fin 2) (Fin 2) F := (x₃ : Matrix (Fin 2) (Fin 2) F).map σ
  have hRA : (Matrix.reindexAlgEquiv F F (e222 c).symm)
      (A : Matrix (Fin (c + 4)) (Fin (c + 4)) F) =
      Matrix.fromBlocks A₁ A₁₂ 0 (Matrix.fromBlocks A₂ A₂₃ 0 A₃) := by
    simpa only [A₁, A₁₂, A₂, A₂₃, A₃] using reindexAlgEquiv_eq_fromBlocks' c F A hA
  have hRA' : (Matrix.reindexAlgEquiv F F (e222 c).symm)
      ((A⁻¹ : GL (Fin (c + 4)) F) : Matrix (Fin (c + 4)) (Fin (c + 4)) F) =
      Matrix.fromBlocks A₁' A₁₂' 0 (Matrix.fromBlocks A₂' A₂₃' 0 A₃') := by
    simpa only [A₁', A₁₂', A₂', A₂₃', A₃'] using
      reindexAlgEquiv_eq_fromBlocks' c F A⁻¹ (isUpperGL_inv (F := F) (A := A) hA)
  have hRQ : (Matrix.reindexAlgEquiv F F (e222 c).symm)
      ((Q : Matrix (Fin (c + 4)) (Fin (c + 4)) F).map σ) =
      Matrix.fromBlocks S₁ 0 0 (Matrix.fromBlocks S₂ 0 0 S₃) := by
    rw [reindexAlgEquiv_map, hQ, Matrix.fromBlocks_map, Matrix.fromBlocks_map]
    simp [S₁, S₂, S₃, Matrix.map_zero]
  have hRX : (Matrix.reindexAlgEquiv F F (e222 c).symm)
      ((CFSG.QuasithinUnique.K1.stdAut A σ 0 Q :
        SpecialLinearGroup (Fin (c + 4)) F) :
        Matrix (Fin (c + 4)) (Fin (c + 4)) F) =
      Matrix.fromBlocks A₁ A₁₂ 0 (Matrix.fromBlocks A₂ A₂₃ 0 A₃) *
        Matrix.fromBlocks S₁ 0 0 (Matrix.fromBlocks S₂ 0 0 S₃) *
          Matrix.fromBlocks A₁' A₁₂' 0 (Matrix.fromBlocks A₂' A₂₃' 0 A₃') := by
    rw [CFSG.QuasithinUnique.K1.coe_stdAut_zero]
    rw [map_mul, map_mul, hRA, hRQ, hRA']
  have hRY : (Matrix.reindexAlgEquiv F F (e222 c).symm)
      ((blockEmbed222 c F gε : SpecialLinearGroup (Fin (c + 4)) F) :
        Matrix (Fin (c + 4)) (Fin (c + 4)) F) =
      Matrix.fromBlocks (gε.1 : Matrix (Fin 2) (Fin 2) F) 0 0
        (Matrix.fromBlocks (gε.2.1 : Matrix (Fin c) (Fin c) F) 0 0
          (gε.2.2 : Matrix (Fin 2) (Fin 2) F)) :=
    reindex_blockEmbed222 c F gε
  have hβ₁ : (gε.1 : Matrix (Fin 2) (Fin 2) F) = A₁ * S₁ * A₁' := by
    rw [h₁, CFSG.QuasithinUnique.K1.coe_stdAut_zero]
    simp only [A₁, A₁', S₁, blockGL1]
    rfl
  have hβ₂ : (gε.2.1 : Matrix (Fin c) (Fin c) F) = A₂ * S₂ * A₂' := by
    rw [h₂, CFSG.QuasithinUnique.K1.coe_stdAut_zero]
    simp only [A₂, A₂', S₂, blockGL2]
    rfl
  have hβ₃ : (gε.2.2 : Matrix (Fin 2) (Fin 2) F) = A₃ * S₃ * A₃' := by
    rw [h₃, CFSG.QuasithinUnique.K1.coe_stdAut_zero]
    simp only [A₃, A₃', S₃, blockGL3]
    rfl
  have hβ₁' : ((gε.1)⁻¹ : Matrix (Fin 2) (Fin 2) F) *
      (gε.1 : Matrix (Fin 2) (Fin 2) F) = 1 := by
    rw [← coe_inv_eq_inv (F := F) (n := 2), ← Matrix.SpecialLinearGroup.coe_mul,
      inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one]
  have hβ₂' : ((gε.2.1)⁻¹ : Matrix (Fin c) (Fin c) F) *
      (gε.2.1 : Matrix (Fin c) (Fin c) F) = 1 := by
    rw [← coe_inv_eq_inv (F := F) (n := c), ← Matrix.SpecialLinearGroup.coe_mul,
      inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one]
  have hβ₃' : ((gε.2.2)⁻¹ : Matrix (Fin 2) (Fin 2) F) *
      (gε.2.2 : Matrix (Fin 2) (Fin 2) F) = 1 := by
    rw [← coe_inv_eq_inv (F := F) (n := 2), ← Matrix.SpecialLinearGroup.coe_mul,
      inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one]
  have hβ₁'' : (gε.1 : Matrix (Fin 2) (Fin 2) F) *
      ((gε.1)⁻¹ : Matrix (Fin 2) (Fin 2) F) = 1 := by
    rw [← coe_inv_eq_inv (F := F) (n := 2), ← Matrix.SpecialLinearGroup.coe_mul,
      mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]
  have hβ₂'' : (gε.2.1 : Matrix (Fin c) (Fin c) F) *
      ((gε.2.1)⁻¹ : Matrix (Fin c) (Fin c) F) = 1 := by
    rw [← coe_inv_eq_inv (F := F) (n := c), ← Matrix.SpecialLinearGroup.coe_mul,
      mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]
  have hβ₃'' : (gε.2.2 : Matrix (Fin 2) (Fin 2) F) *
      ((gε.2.2)⁻¹ : Matrix (Fin 2) (Fin 2) F) = 1 := by
    rw [← coe_inv_eq_inv (F := F) (n := 2), ← Matrix.SpecialLinearGroup.coe_mul,
      mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]
  obtain ⟨B, E, hBE⟩ := exists_fromBlocks_quotient (F := F)
    A₁ A₁₂ A₂ A₂₃ A₃ A₁' A₁₂' A₂' A₂₃' A₃' S₁ S₂ S₃
    (gε.1 : Matrix (Fin 2) (Fin 2) F) ((gε.1)⁻¹ : Matrix (Fin 2) (Fin 2) F)
    (gε.2.1 : Matrix (Fin c) (Fin c) F) ((gε.2.1)⁻¹ : Matrix (Fin c) (Fin c) F)
    (gε.2.2 : Matrix (Fin 2) (Fin 2) F) ((gε.2.2)⁻¹ : Matrix (Fin 2) (Fin 2) F)
    hβ₁ hβ₂ hβ₃ hβ₁' hβ₂' hβ₃' hβ₁'' hβ₂'' hβ₃''
  have hRYinv : (Matrix.reindexAlgEquiv F F (e222 c).symm)
      ((blockEmbed222 c F gε⁻¹ : SpecialLinearGroup (Fin (c + 4)) F) :
        Matrix (Fin (c + 4)) (Fin (c + 4)) F) =
      Matrix.fromBlocks ((gε.1)⁻¹ : Matrix (Fin 2) (Fin 2) F) 0 0
        (Matrix.fromBlocks ((gε.2.1)⁻¹ : Matrix (Fin c) (Fin c) F) 0 0
          ((gε.2.2)⁻¹ : Matrix (Fin 2) (Fin 2) F)) := by
    rw [reindex_blockEmbed222 c F (gε⁻¹)]
    simp only [Prod.fst_inv, Prod.snd_inv, coe_inv_eq_inv (F := F) (n := 2),
      coe_inv_eq_inv (F := F) (n := c)]
  have hYinv : (Matrix.fromBlocks (gε.1 : Matrix (Fin 2) (Fin 2) F) 0 0
      (Matrix.fromBlocks (gε.2.1 : Matrix (Fin c) (Fin c) F) 0 0
        (gε.2.2 : Matrix (Fin 2) (Fin 2) F)))⁻¹ =
      Matrix.fromBlocks ((gε.1)⁻¹ : Matrix (Fin 2) (Fin 2) F) 0 0
        (Matrix.fromBlocks ((gε.2.1)⁻¹ : Matrix (Fin c) (Fin c) F) 0 0
          ((gε.2.2)⁻¹ : Matrix (Fin 2) (Fin 2) F)) := by
    apply inv_fromBlocks_diag
    · exact hβ₁''
    · rw [Matrix.fromBlocks_multiply, hβ₂'', hβ₃'']
      simp [Matrix.fromBlocks_one]
  refine mem_blockRadical222_of_reindex_eq_upForm (B := B) (E := E) ?_
  rw [show ((blockEmbed222 c F gε)⁻¹ *
      CFSG.QuasithinUnique.K1.stdAut A σ 0 Q : SpecialLinearGroup (Fin (c + 4)) F) =
      ((blockEmbed222 c F gε)⁻¹ : SpecialLinearGroup (Fin (c + 4)) F) *
        CFSG.QuasithinUnique.K1.stdAut A σ 0 Q from rfl]
  have hbinv : (blockEmbed222 c F gε)⁻¹ = blockEmbed222 c F gε⁻¹ :=
    (map_inv (blockEmbed222 c F) gε).symm
  rw [Matrix.SpecialLinearGroup.coe_mul, map_mul, hbinv, hRYinv, hRX, ← hYinv]
  simpa [upFormMat] using hBE


theorem borelStd_blockEmbed222 (hA : IsUpperGL A) (σ : F ≃+* F) (ε : ℕ)
    (g : SpecialLinearGroup (Fin 2) F × SpecialLinearGroup (Fin c) F ×
      SpecialLinearGroup (Fin 2) F) :
    (blockEmbed222 c F (blockStd222 c F A hA σ ε g))⁻¹ *
      borelStd (c + 4) F A σ ε (blockEmbed222 c F g) ∈ blockRadical222 c F := by
  rcases Nat.mod_two_eq_zero_or_one ε with hε | hε
  · have hγ : (borelGraph (c + 4) F) ^ ε = 1 :=
      borelGraph_pow_eq_one_of_even (n := c + 4) (F := F) (ε := ε) hε
    have hstd : borelStd (c + 4) F A σ ε = CFSG.QuasithinUnique.K1.stdAut A σ 0 := by
      rw [borelStd, hγ, mul_one]
    have hbs : blockStd222 c F A hA σ ε = blockStd222Even c F A hA σ := by
      rw [blockStd222, if_pos hε]
    rw [hstd, hbs]
    exact blockQuotient_of_blockDiagonal c F A hA σ (blockEmbed222 c F g)
      g.1 g.2.1 g.2.2 (reindex_blockEmbed222 c F g)
      (blockStd222Even c F A hA σ g) rfl rfl rfl
  · have hγ : (borelGraph (c + 4) F) ^ ε = borelGraph (c + 4) F :=
      borelGraph_pow_eq_self_of_odd (n := c + 4) (F := F) (ε := ε) hε
    have hstd : borelStd (c + 4) F A σ ε =
        CFSG.QuasithinUnique.K1.stdAut A σ 0 * borelGraph (c + 4) F := by
      rw [borelStd, hγ]
    have hbs : blockStd222 c F A hA σ ε = blockStd222Odd c F A hA σ := by
      rw [blockStd222, if_neg (by omega)]
    rw [hstd, hbs, MulAut.mul_apply]
    exact blockQuotient_of_blockDiagonal c F A hA σ
      (borelGraph (c + 4) F (blockEmbed222 c F g))
      (borelGraph 2 F g.2.2) (borelGraph c F g.2.1) (borelGraph 2 F g.1)
      (reindex_borelGraph_blockEmbed222 c F g)
      (blockStd222Odd c F A hA σ g)
      (by rw [blockStd222Odd_apply]) (by rw [blockStd222Odd_apply])
      (by rw [blockStd222Odd_apply])


end

end CFSG.LieType.SpecialLinear