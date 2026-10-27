module

public import CFSG.LieType.Universal.SymplecticExtras.Matrices
public import CFSG.LargeExtraspecial.A2ModCfgSL

public section

namespace CFSG.LargeExtraspecial.A2Mod.FrC

open Matrix CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.Symplectic

variable {k : ℕ} {F : Type} [Field F]

theorem mem_statedSp_iff {g : GL (Fin k ⊕ Fin k) F} :
    g ∈ StatedSp k F ↔ (g : Matrix (Fin k ⊕ Fin k) (Fin k ⊕ Fin k) F)ᵀ * fromBlocks 0 1 (-1) 0 *
      (g : Matrix (Fin k ⊕ Fin k) (Fin k ⊕ Fin k) F) = fromBlocks 0 1 (-1) 0 :=
  CFSG.Open.StatedAPI.mem_statedSp_iff

theorem ext_mat {x y : StatedSp k F} (h : SpExtras.mat k F x = SpExtras.mat k F y) : x = y :=
  SpExtras.mat_injective h

@[expose] noncomputable def upper (S : Matrix (Fin k) (Fin k) F) (hS : Sᵀ = S) : StatedSp k F :=
  ⟨⟨fromBlocks 1 S 0 1, fromBlocks 1 (-S) 0 1, by simp [fromBlocks_multiply],
    by simp [fromBlocks_multiply]⟩, by
      rw [mem_statedSp_iff]
      simp [fromBlocks_transpose, fromBlocks_multiply, hS]⟩

@[expose] noncomputable def lower (S : Matrix (Fin k) (Fin k) F) (hS : Sᵀ = S) : StatedSp k F :=
  ⟨⟨fromBlocks 1 0 S 1, fromBlocks 1 0 (-S) 1, by simp [fromBlocks_multiply],
    by simp [fromBlocks_multiply]⟩, by
      rw [mem_statedSp_iff]
      simp [fromBlocks_transpose, fromBlocks_multiply, hS]⟩

@[simp]
theorem mat_upper (S : Matrix (Fin k) (Fin k) F) (hS : Sᵀ = S) :
    SpExtras.mat k F (upper S hS) = fromBlocks 1 S 0 1 :=
  rfl

@[simp]
theorem mat_lower (S : Matrix (Fin k) (Fin k) F) (hS : Sᵀ = S) :
    SpExtras.mat k F (lower S hS) = fromBlocks 1 0 S 1 :=
  rfl

theorem transpose_add_of {S S' : Matrix (Fin k) (Fin k) F} (hS : Sᵀ = S) (hS' : S'ᵀ = S') :
    (S + S')ᵀ = S + S' := by
  rw [transpose_add, hS, hS']

theorem upper_mul_upper {S S' : Matrix (Fin k) (Fin k) F} (hS : Sᵀ = S) (hS' : S'ᵀ = S') :
    upper S hS * upper S' hS' = upper (S + S') (transpose_add_of hS hS') :=
  ext_mat (by simp [fromBlocks_multiply, add_comm])

theorem lower_mul_lower {S S' : Matrix (Fin k) (Fin k) F} (hS : Sᵀ = S) (hS' : S'ᵀ = S') :
    lower S hS * lower S' hS' = lower (S + S') (transpose_add_of hS hS') :=
  ext_mat (by simp [fromBlocks_multiply, add_comm])

theorem add_self_eq_zero [CharP F 2] {ι : Type*} (S : Matrix ι ι F) : S + S = 0 := by
  ext a b
  rw [Matrix.add_apply, CharTwo.add_self_eq_zero, Matrix.zero_apply]

theorem upper_inv [CharP F 2] {S : Matrix (Fin k) (Fin k) F} (hS : Sᵀ = S) :
    (upper S hS)⁻¹ = upper S hS := by
  refine inv_eq_of_mul_eq_one_right (ext_mat ?_)
  simp only [map_mul, mat_upper, fromBlocks_multiply, map_one]
  simp [← fromBlocks_one, add_self_eq_zero]

theorem lower_inv [CharP F 2] {S : Matrix (Fin k) (Fin k) F} (hS : Sᵀ = S) :
    (lower S hS)⁻¹ = lower S hS := by
  refine inv_eq_of_mul_eq_one_right (ext_mat ?_)
  simp only [map_mul, mat_lower, fromBlocks_multiply, map_one]
  simp [← fromBlocks_one, add_self_eq_zero]

@[expose] noncomputable def leviElt (A : SpecialLinearGroup (Fin k) F) : StatedSp k F :=
  ⟨⟨fromBlocks (A : Matrix (Fin k) (Fin k) F) 0 0
        ((A⁻¹ : SpecialLinearGroup (Fin k) F) : Matrix (Fin k) (Fin k) F)ᵀ,
      fromBlocks ((A⁻¹ : SpecialLinearGroup (Fin k) F) : Matrix (Fin k) (Fin k) F) 0 0
        (A : Matrix (Fin k) (Fin k) F)ᵀ, by
        rw [fromBlocks_multiply]
        simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, ← transpose_mul,
          sl_coe_mul_coe_inv, transpose_one, fromBlocks_one], by
        rw [fromBlocks_multiply]
        simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, ← transpose_mul,
          sl_coe_inv_mul_coe, transpose_one, fromBlocks_one]⟩, by
      rw [mem_statedSp_iff]
      simp only [fromBlocks_transpose, transpose_zero, transpose_transpose,
        fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Matrix.mul_one,
        Matrix.mul_neg, Matrix.neg_mul, ← transpose_mul, sl_coe_inv_mul_coe, transpose_one,
        neg_zero]⟩

@[simp]
theorem mat_leviElt (A : SpecialLinearGroup (Fin k) F) :
    SpExtras.mat k F (leviElt A) = fromBlocks (A : Matrix (Fin k) (Fin k) F) 0 0
      ((A⁻¹ : SpecialLinearGroup (Fin k) F) : Matrix (Fin k) (Fin k) F)ᵀ :=
  rfl

@[expose] noncomputable def levi : SpecialLinearGroup (Fin k) F →* StatedSp k F where
  toFun := leviElt
  map_one' := ext_mat (by
    simp only [mat_leviElt, map_one, inv_one, Matrix.SpecialLinearGroup.coe_one, transpose_one,
      fromBlocks_one])
  map_mul' A B := ext_mat (by
    simp only [map_mul, mat_leviElt, fromBlocks_multiply, _root_.mul_inv_rev,
      Matrix.SpecialLinearGroup.coe_mul, transpose_mul, Matrix.mul_zero, Matrix.zero_mul, add_zero,
      zero_add])

@[simp]
theorem mat_levi (A : SpecialLinearGroup (Fin k) F) :
    SpExtras.mat k F (levi A) = fromBlocks (A : Matrix (Fin k) (Fin k) F) 0 0
      ((A⁻¹ : SpecialLinearGroup (Fin k) F) : Matrix (Fin k) (Fin k) F)ᵀ :=
  rfl

theorem levi_conj_upper (A : SpecialLinearGroup (Fin k) F) {S : Matrix (Fin k) (Fin k) F}
    (hS : Sᵀ = S) (h : ((A : Matrix (Fin k) (Fin k) F) * S * (A : Matrix (Fin k) (Fin k) F)ᵀ)ᵀ =
      (A : Matrix (Fin k) (Fin k) F) * S * (A : Matrix (Fin k) (Fin k) F)ᵀ) :
    levi A * upper S hS * (levi A)⁻¹ = upper _ h := by
  refine ext_mat ?_
  rw [← map_inv, map_mul, map_mul, mat_levi, mat_levi, mat_upper, mat_upper, inv_inv,
    fromBlocks_multiply, fromBlocks_multiply]
  simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Matrix.mul_one,
    sl_coe_mul_coe_inv, Matrix.mul_assoc, ← transpose_mul, transpose_one]

theorem levi_conj_lower (A : SpecialLinearGroup (Fin k) F) {S : Matrix (Fin k) (Fin k) F}
    (hS : Sᵀ = S) (h : (((A⁻¹ : SpecialLinearGroup (Fin k) F) : Matrix (Fin k) (Fin k) F)ᵀ * S *
      ((A⁻¹ : SpecialLinearGroup (Fin k) F) : Matrix (Fin k) (Fin k) F))ᵀ =
      ((A⁻¹ : SpecialLinearGroup (Fin k) F) : Matrix (Fin k) (Fin k) F)ᵀ * S *
        ((A⁻¹ : SpecialLinearGroup (Fin k) F) : Matrix (Fin k) (Fin k) F)) :
    levi A * lower S hS * (levi A)⁻¹ = lower _ h := by
  refine ext_mat ?_
  rw [← map_inv, map_mul, map_mul, mat_levi, mat_levi, mat_lower, mat_lower, inv_inv,
    fromBlocks_multiply, fromBlocks_multiply]
  simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Matrix.mul_one,
    sl_coe_mul_coe_inv, Matrix.mul_assoc, ← transpose_mul, transpose_one]

@[expose] noncomputable def jElt : StatedSp k F :=
  ⟨⟨fromBlocks 0 1 (-1) 0, fromBlocks 0 (-1) 1 0, by simp [fromBlocks_multiply, ← fromBlocks_one],
    by simp [fromBlocks_multiply, ← fromBlocks_one]⟩, by
      rw [mem_statedSp_iff]
      simp [fromBlocks_transpose, fromBlocks_multiply]⟩

@[simp]
theorem mat_jElt : SpExtras.mat k F jElt = fromBlocks 0 1 (-1) 0 :=
  rfl

theorem mat_jElt_inv : SpExtras.mat k F jElt⁻¹ = fromBlocks 0 (-1) 1 0 :=
  rfl

theorem jElt_conj_of_mat {x y : StatedSp k F} {A B : Matrix (Fin k) (Fin k) F}
    (hx : SpExtras.mat k F x = fromBlocks A 0 0 B) (hy : SpExtras.mat k F y = fromBlocks B 0 0 A) :
    jElt * x * jElt⁻¹ = y := by
  refine ext_mat ?_
  rw [map_mul, map_mul, mat_jElt, mat_jElt_inv, hx, hy, fromBlocks_multiply, fromBlocks_multiply]
  simp

section CharTwo

variable [CharP F 2]

@[expose] noncomputable def levZ : SpecialLinearGroup (Fin k) (ZMod 2) →* StatedSp k F :=
  levi.comp (SpecialLinearGroup.map (ZMod.castHom (dvd_refl 2) F))

theorem map_one_add_vecMulVec (v φ : Fin k → ZMod 2) :
    (1 + vecMulVec v φ).map (ZMod.castHom (dvd_refl 2) F) =
      1 + vecMulVec (fun a => ZMod.castHom (dvd_refl 2) F (v a))
        (fun a => ZMod.castHom (dvd_refl 2) F (φ a)) := by
  rw [Matrix.map_add _ (map_add _), Matrix.map_one _ (map_zero _) (map_one _)]
  congr 1
  ext a b
  simp [vecMulVec_apply]

theorem mat_levZ_tv {v φ : Fin k → ZMod 2} (h : φ ⬝ᵥ v = 0) :
    SpExtras.mat k F (levZ (tv v φ)) =
      fromBlocks (1 + vecMulVec (fun a => ZMod.castHom (dvd_refl 2) F (v a))
          (fun a => ZMod.castHom (dvd_refl 2) F (φ a))) 0 0
        (1 + vecMulVec (fun a => ZMod.castHom (dvd_refl 2) F (φ a))
          (fun a => ZMod.castHom (dvd_refl 2) F (v a))) := by
  have hinv : (tv v φ)⁻¹ = tv v φ := by
    rw [tv_inv h]
    congr 1
    funext a
    exact CharTwo.neg_eq (φ a)
  rw [levZ, MonoidHom.comp_apply, mat_levi, ← map_inv, hinv,
    Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, coe_tv h,
    map_one_add_vecMulVec, transpose_add, transpose_one, transpose_vecMulVec]

theorem jElt_conj_levZ_tv {v φ : Fin k → ZMod 2} (h : φ ⬝ᵥ v = 0) :
    jElt * levZ (tv v φ) * jElt⁻¹ = (levZ (tv φ v) : StatedSp k F) :=
  jElt_conj_of_mat (mat_levZ_tv h) (mat_levZ_tv (by rwa [dotProduct_comm]))

theorem mat_levZ_elemTv {i j : Fin k} (hij : i ≠ j) :
    SpExtras.mat k F (levZ (elemTv i j)) =
      fromBlocks (1 + single i j (1 : F)) 0 0 (1 + single j i (1 : F)) := by
  have hc : ∀ l : Fin k, (fun a => ZMod.castHom (dvd_refl 2) F
      ((Pi.single l (1 : ZMod 2) : Fin k → ZMod 2) a)) = Pi.single l (1 : F) := fun l => by
    funext a
    by_cases ha : a = l
    · subst ha
      simp
    · simp [ha]
  rw [elemTv, mat_levZ_tv (single_dotProduct_single_of_ne hij), hc, hc,
    ← single_eq_single_vecMulVec_single, ← single_eq_single_vecMulVec_single]

theorem ofNat_two_eq_zero : (2 : F) = 0 := CharTwo.two_eq_zero

theorem ofNat_three_eq_one : (3 : F) = 1 := by
  rw [show (3 : F) = 2 + 1 by norm_num, ofNat_two_eq_zero, zero_add]

theorem ofNat_four_eq_zero : (4 : F) = 0 := by
  rw [show (4 : F) = 2 * 2 by norm_num, ofNat_two_eq_zero, zero_mul]

end CharTwo

end CFSG.LargeExtraspecial.A2Mod.FrC
