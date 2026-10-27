module

public import CFSG.HardMathSupport.U4FF.ClassLocSound

public section

namespace CFSG.HardMathSupport.U4FF

open Matrix
open scoped MatrixGroups
open CFSG.QuasithinUnique.Setup.X7 (permMat)
open CFSG.QuasithinUnique.Setup.X7b (exists_perm_conj)

variable {k : Type*} [Field k] [CharP k 2]

private theorem perm_fin4_invol : ∀ σ : Equiv.Perm (Fin 4), σ * σ = 1 → σ ≠ 1 →
    σ = Equiv.swap 2 3 ∨ σ = Equiv.swap 1 2 ∨ σ = Equiv.swap 1 3 ∨ σ = Equiv.swap 0 1 ∨
      σ = Equiv.swap 0 1 * Equiv.swap 2 3 ∨ σ = Equiv.swap 0 2 ∨
      σ = Equiv.swap 0 2 * Equiv.swap 1 3 ∨ σ = Equiv.swap 0 3 ∨
      σ = Equiv.swap 0 3 * Equiv.swap 1 2 := by
  decide

private theorem permMat_map_castHom (σ : Equiv.Perm (Fin 4)) :
    (permMat (ZMod 2) σ).map (ZMod.castHom (dvd_refl 2) k) = permMat k σ := by
  ext i j
  by_cases h : σ j = i <;> simp [permMat, h]

private theorem one_add_single03_map :
    (1 + Matrix.single 0 3 1 : Matrix (Fin 4) (Fin 4) (ZMod 2)).map
        (ZMod.castHom (dvd_refl 2) k) = 1 + Matrix.single 0 3 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.one_apply, Matrix.single_apply]

private theorem one_add_single02_single13_map :
    (1 + Matrix.single 0 2 1 + Matrix.single 1 3 1 : Matrix (Fin 4) (Fin 4) (ZMod 2)).map
        (ZMod.castHom (dvd_refl 2) k) = 1 + Matrix.single 0 2 1 + Matrix.single 1 3 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.one_apply, Matrix.single_apply]

private theorem witness_gen (σ : Equiv.Perm (Fin 4)) (P Q N : Matrix (Fin 4) (Fin 4) (ZMod 2))
    (hPQ : P * Q = 1) (hQP : Q * P = 1) (h : permMat (ZMod 2) σ * P = P * N) :
    P.map (ZMod.castHom (dvd_refl 2) k) * Q.map (ZMod.castHom (dvd_refl 2) k) = 1 ∧
      Q.map (ZMod.castHom (dvd_refl 2) k) * P.map (ZMod.castHom (dvd_refl 2) k) = 1 ∧
      permMat k σ * P.map (ZMod.castHom (dvd_refl 2) k) =
        P.map (ZMod.castHom (dvd_refl 2) k) * N.map (ZMod.castHom (dvd_refl 2) k) := by
  have hone : (1 : Matrix (Fin 4) (Fin 4) (ZMod 2)).map (ZMod.castHom (dvd_refl 2) k) = 1 :=
    Matrix.map_one _ (map_zero _) (map_one _)
  refine ⟨?_, ?_, ?_⟩
  · rw [← Matrix.map_mul, hPQ, hone]
  · rw [← Matrix.map_mul, hQP, hone]
  · rw [← permMat_map_castHom, ← Matrix.map_mul, ← Matrix.map_mul, h]

private theorem witness_one (σ : Equiv.Perm (Fin 4)) (P Q : Matrix (Fin 4) (Fin 4) (ZMod 2))
    (hPQ : P * Q = 1) (hQP : Q * P = 1)
    (h : permMat (ZMod 2) σ * P = P * (1 + Matrix.single 0 3 1)) :
    ∃ P' Q' : Matrix (Fin 4) (Fin 4) k, P' * Q' = 1 ∧ Q' * P' = 1 ∧
      permMat k σ * P' = P' * (1 + Matrix.single 0 3 1) := by
  obtain ⟨h1, h2, h3⟩ := witness_gen (k := k) σ P Q _ hPQ hQP h
  refine ⟨P.map (ZMod.castHom (dvd_refl 2) k), Q.map (ZMod.castHom (dvd_refl 2) k), h1, h2, ?_⟩
  rw [h3, one_add_single03_map]

private theorem witness_two (σ : Equiv.Perm (Fin 4)) (P Q : Matrix (Fin 4) (Fin 4) (ZMod 2))
    (hPQ : P * Q = 1) (hQP : Q * P = 1)
    (h : permMat (ZMod 2) σ * P = P * (1 + Matrix.single 0 2 1 + Matrix.single 1 3 1)) :
    ∃ P' Q' : Matrix (Fin 4) (Fin 4) k, P' * Q' = 1 ∧ Q' * P' = 1 ∧
      permMat k σ * P' = P' * (1 + Matrix.single 0 2 1 + Matrix.single 1 3 1) := by
  obtain ⟨h1, h2, h3⟩ := witness_gen (k := k) σ P Q _ hPQ hQP h
  refine ⟨P.map (ZMod.castHom (dvd_refl 2) k), Q.map (ZMod.castHom (dvd_refl 2) k), h1, h2, ?_⟩
  rw [h3, one_add_single02_single13_map]

private theorem invol_perm_normal_form (σ : Equiv.Perm (Fin 4)) (hσ : σ * σ = 1) (hne : σ ≠ 1) :
    ∃ P Q : Matrix (Fin 4) (Fin 4) k, P * Q = 1 ∧ Q * P = 1 ∧
      (permMat k σ * P = P * (1 + Matrix.single 0 3 1) ∨
        permMat k σ * P = P * (1 + Matrix.single 0 2 1 + Matrix.single 1 3 1)) := by
  rcases perm_fin4_invol σ hσ hne with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · obtain ⟨P, Q, h1, h2, h3⟩ := witness_one (k := k) (Equiv.swap 2 3)
      !![0, 0, 1, 0; 0, 1, 0, 0; 1, 0, 0, 0; 1, 0, 0, 1]
      !![0, 0, 1, 0; 0, 1, 0, 0; 1, 0, 0, 0; 0, 0, 1, 1] (by decide) (by decide) (by decide)
    exact ⟨P, Q, h1, h2, Or.inl h3⟩
  · obtain ⟨P, Q, h1, h2, h3⟩ := witness_one (k := k) (Equiv.swap 1 2)
      !![0, 0, 1, 0; 1, 0, 0, 0; 1, 0, 0, 1; 0, 1, 0, 0]
      !![0, 1, 0, 0; 0, 0, 0, 1; 1, 0, 0, 0; 0, 1, 1, 0] (by decide) (by decide) (by decide)
    exact ⟨P, Q, h1, h2, Or.inl h3⟩
  · obtain ⟨P, Q, h1, h2, h3⟩ := witness_one (k := k) (Equiv.swap 1 3)
      !![0, 0, 1, 0; 1, 0, 0, 0; 0, 1, 0, 0; 1, 0, 0, 1]
      !![0, 1, 0, 0; 0, 0, 1, 0; 1, 0, 0, 0; 0, 1, 0, 1] (by decide) (by decide) (by decide)
    exact ⟨P, Q, h1, h2, Or.inl h3⟩
  · obtain ⟨P, Q, h1, h2, h3⟩ := witness_one (k := k) (Equiv.swap 0 1)
      !![1, 0, 0, 0; 1, 0, 0, 1; 0, 0, 1, 0; 0, 1, 0, 0]
      !![1, 0, 0, 0; 0, 0, 0, 1; 0, 0, 1, 0; 1, 1, 0, 0] (by decide) (by decide) (by decide)
    exact ⟨P, Q, h1, h2, Or.inl h3⟩
  · obtain ⟨P, Q, h1, h2, h3⟩ := witness_two (k := k) (Equiv.swap 0 1 * Equiv.swap 2 3)
      !![0, 1, 0, 0; 0, 1, 0, 1; 1, 0, 0, 0; 1, 0, 1, 0]
      !![0, 0, 1, 0; 1, 0, 0, 0; 0, 0, 1, 1; 1, 1, 0, 0] (by decide) (by decide) (by decide)
    exact ⟨P, Q, h1, h2, Or.inr h3⟩
  · obtain ⟨P, Q, h1, h2, h3⟩ := witness_one (k := k) (Equiv.swap 0 2)
      !![1, 0, 0, 0; 0, 0, 1, 0; 1, 0, 0, 1; 0, 1, 0, 0]
      !![1, 0, 0, 0; 0, 0, 0, 1; 0, 1, 0, 0; 1, 0, 1, 0] (by decide) (by decide) (by decide)
    exact ⟨P, Q, h1, h2, Or.inl h3⟩
  · obtain ⟨P, Q, h1, h2, h3⟩ := witness_two (k := k) (Equiv.swap 0 2 * Equiv.swap 1 3)
      !![0, 1, 0, 0; 1, 0, 0, 0; 0, 1, 0, 1; 1, 0, 1, 0]
      !![0, 1, 0, 0; 1, 0, 0, 0; 0, 1, 0, 1; 1, 0, 1, 0] (by decide) (by decide) (by decide)
    exact ⟨P, Q, h1, h2, Or.inr h3⟩
  · obtain ⟨P, Q, h1, h2, h3⟩ := witness_one (k := k) (Equiv.swap 0 3)
      !![1, 0, 0, 0; 0, 0, 1, 0; 0, 1, 0, 0; 1, 0, 0, 1]
      !![1, 0, 0, 0; 0, 0, 1, 0; 0, 1, 0, 0; 1, 0, 0, 1] (by decide) (by decide) (by decide)
    exact ⟨P, Q, h1, h2, Or.inl h3⟩
  · obtain ⟨P, Q, h1, h2, h3⟩ := witness_two (k := k) (Equiv.swap 0 3 * Equiv.swap 1 2)
      !![0, 1, 0, 0; 1, 0, 0, 0; 1, 0, 1, 0; 0, 1, 0, 1]
      !![0, 1, 0, 0; 1, 0, 0, 0; 0, 1, 1, 0; 1, 0, 0, 1] (by decide) (by decide) (by decide)
    exact ⟨P, Q, h1, h2, Or.inr h3⟩

theorem involution_normal_form (z : Matrix (Fin 4) (Fin 4) k) (hz : z * z = 1) (hne : z ≠ 1) :
    ∃ P : GL (Fin 4) k,
      ((P⁻¹ : GL (Fin 4) k) : Matrix (Fin 4) (Fin 4) k) * z * (P : Matrix (Fin 4) (Fin 4) k) =
          1 + Matrix.single 0 3 1 ∨
      ((P⁻¹ : GL (Fin 4) k) : Matrix (Fin 4) (Fin 4) k) * z * (P : Matrix (Fin 4) (Fin 4) k) =
          1 + Matrix.single 0 2 1 + Matrix.single 1 3 1 := by
  obtain ⟨σ, P, Q, hσ, hPQ, hQP, hzP⟩ := exists_perm_conj (k := k) hz
  have hσ1 : σ ≠ 1 := by
    rintro rfl
    apply hne
    have hid : permMat k (1 : Equiv.Perm (Fin 4)) = 1 := by
      ext i j
      simp [permMat, Matrix.one_apply, eq_comm]
    rw [hid, Matrix.mul_one] at hzP
    calc z = z * (P * Q) := by rw [hPQ, Matrix.mul_one]
      _ = z * P * Q := (Matrix.mul_assoc _ _ _).symm
      _ = P * Q := by rw [hzP]
      _ = 1 := hPQ
  obtain ⟨P1, Q1, h1, h2, h3⟩ := invol_perm_normal_form (k := k) σ hσ hσ1
  have hPP : (P * P1) * (Q1 * Q) = 1 := by
    calc (P * P1) * (Q1 * Q) = P * ((P1 * Q1) * Q) := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [h1, Matrix.one_mul, hPQ]
  have hQP' : (Q1 * Q) * (P * P1) = 1 := by
    calc (Q1 * Q) * (P * P1) = Q1 * ((Q * P) * P1) := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hQP, Matrix.one_mul, h2]
  have key : ∀ N : Matrix (Fin 4) (Fin 4) k, permMat k σ * P1 = P1 * N →
      ∃ P' : GL (Fin 4) k, ((P'⁻¹ : GL (Fin 4) k) : Matrix (Fin 4) (Fin 4) k) * z *
        (P' : Matrix (Fin 4) (Fin 4) k) = N := by
    intro N hN
    refine ⟨Units.mk (P * P1) (Q1 * Q) hPP hQP', ?_⟩
    have hzP' : z * (P * P1) = (P * P1) * N := by
      calc z * (P * P1) = (z * P) * P1 := (Matrix.mul_assoc _ _ _).symm
        _ = (P * permMat k σ) * P1 := by rw [hzP]
        _ = P * (permMat k σ * P1) := Matrix.mul_assoc _ _ _
        _ = P * (P1 * N) := by rw [hN]
        _ = (P * P1) * N := (Matrix.mul_assoc _ _ _).symm
    show (Q1 * Q) * z * (P * P1) = N
    calc (Q1 * Q) * z * (P * P1) = (Q1 * Q) * (z * (P * P1)) := Matrix.mul_assoc _ _ _
      _ = (Q1 * Q) * ((P * P1) * N) := by rw [hzP']
      _ = ((Q1 * Q) * (P * P1)) * N := (Matrix.mul_assoc _ _ _).symm
      _ = N := by rw [hQP', Matrix.one_mul]
  rcases h3 with h3 | h3
  · obtain ⟨P', hP'⟩ := key _ h3
    exact ⟨P', Or.inl hP'⟩
  · obtain ⟨P', hP'⟩ := key _ h3
    exact ⟨P', Or.inr hP'⟩

private theorem sl_ext {A B : SL(4, k)}
    (h : (A : Matrix (Fin 4) (Fin 4) k) = (B : Matrix (Fin 4) (Fin 4) k)) : A = B :=
  Subtype.ext h

private theorem exists_sl_conj [Finite k] (z N P Q : Matrix (Fin 4) (Fin 4) k)
    (hPQ : P * Q = 1) (hQP : Q * P = 1) (hN : Q * z * P = N) :
    ∃ P0 : SL(4, k), (P0 : Matrix (Fin 4) (Fin 4) k) * z *
      ((P0⁻¹ : SL(4, k)) : Matrix (Fin 4) (Fin 4) k) = N := by
  have h2 : (2 : k) = 0 := by exact_mod_cast CharP.cast_eq_zero k 2
  have hinj : Function.Injective (fun x : k => x ^ 4) := by
    intro x y hxy
    have hxy' : x ^ 4 = y ^ 4 := hxy
    have h4 : (x - y) ^ 4 = 0 := by
      linear_combination hxy' + (-2 * x ^ 3 * y + 3 * x ^ 2 * y ^ 2 - 2 * x * y ^ 3 + y ^ 4) * h2
    exact sub_eq_zero.mp ((pow_eq_zero_iff (by norm_num : (4 : ℕ) ≠ 0)).mp h4)
  obtain ⟨c, hc⟩ := Finite.surjective_of_injective hinj Q.det
  have hc' : c ^ 4 = Q.det := hc
  have hdet : P.det * Q.det = 1 := by rw [← Matrix.det_mul, hPQ, Matrix.det_one]
  have hQ0 : Q.det ≠ 0 := by
    intro h
    rw [h, mul_zero] at hdet
    exact zero_ne_one hdet
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [zero_pow (by norm_num : (4 : ℕ) ≠ 0)] at hc'
    exact hQ0 hc'.symm
  have hdet0 : (c⁻¹ • Q).det = 1 := by
    rw [Matrix.det_smul, Fintype.card_fin, inv_pow, hc', inv_mul_cancel₀ hQ0]
  have hdetB : (c • P).det = 1 := by
    rw [Matrix.det_smul, Fintype.card_fin, hc', mul_comm Q.det P.det, hdet]
  obtain ⟨P0, hP0⟩ : ∃ P0 : SL(4, k), (P0 : Matrix (Fin 4) (Fin 4) k) = c⁻¹ • Q :=
    ⟨⟨c⁻¹ • Q, hdet0⟩, rfl⟩
  obtain ⟨B0, hB0⟩ : ∃ B0 : SL(4, k), (B0 : Matrix (Fin 4) (Fin 4) k) = c • P :=
    ⟨⟨c • P, hdetB⟩, rfl⟩
  have hPB : P0 * B0 = 1 := by
    apply sl_ext
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one, hP0, hB0]
    simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_inv_cancel₀ hc0,
      inv_mul_cancel₀ hc0, one_smul]
    exact hQP
  refine ⟨P0, ?_⟩
  rw [inv_eq_of_mul_eq_one_right hPB, hP0, hB0]
  simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_inv_cancel₀ hc0,
    inv_mul_cancel₀ hc0, one_smul]
  exact hN

private theorem a1_coe : ((a1 k : SL(4, k)) : Matrix (Fin 4) (Fin 4) k) =
    1 + Matrix.single 0 3 1 := rfl

private theorem a2_coe : ((a2 k : SL(4, k)) : Matrix (Fin 4) (Fin 4) k) =
    1 + Matrix.single 0 2 1 + Matrix.single 1 3 1 := by
  simp only [a2, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.transvection_coe]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_four, Matrix.single_apply, Matrix.one_apply]

theorem involution_conj_a [Finite k] (g : SL(4, k)) (hg : g * g = 1) (hne : g ≠ 1) :
    ∃ P : SL(4, k), P * g * P⁻¹ = a1 k ∨ P * g * P⁻¹ = a2 k := by
  have hz : (g : Matrix (Fin 4) (Fin 4) k) * (g : Matrix (Fin 4) (Fin 4) k) = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, hg, Matrix.SpecialLinearGroup.coe_one]
  have hne' : (g : Matrix (Fin 4) (Fin 4) k) ≠ 1 := by
    intro h
    apply hne
    apply sl_ext
    rw [h, Matrix.SpecialLinearGroup.coe_one]
  obtain ⟨P, hP⟩ := involution_normal_form (k := k) _ hz hne'
  rcases hP with hP | hP
  · obtain ⟨P0, hP0⟩ := exists_sl_conj (k := k) _ _ _ _ (Units.mul_inv P) (Units.inv_mul P) hP
    refine ⟨P0, Or.inl (sl_ext ?_)⟩
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, hP0, a1_coe]
  · obtain ⟨P0, hP0⟩ := exists_sl_conj (k := k) _ _ _ _ (Units.mul_inv P) (Units.inv_mul P) hP
    refine ⟨P0, Or.inr (sl_ext ?_)⟩
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, hP0, a2_coe]

end CFSG.HardMathSupport.U4FF
