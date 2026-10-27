module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.ClassicalInvolution.Models.SymplecticPairs.Basic
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup Matrix CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_injective)

variable {K : Type} [Field K] {N : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]

theorem gram_transpose_eq_neg : (gram K N)ᵀ = -gram K N := by
  rw [CFSG.ClassicalInvolution.Models.SymplecticPairs.gram, fromBlocks_transpose, fromBlocks_neg]
  simp

section Frame

variable (A : Matrix (Fin N ⊕ Fin N) ι K) (G : Matrix ι ι K)

@[expose] def frameInv : Matrix ι (Fin N ⊕ Fin N) K := -(G * Aᵀ * gram K N)

@[expose] def frameMat (X : Matrix ι ι K) : Matrix (Fin N ⊕ Fin N) (Fin N ⊕ Fin N) K :=
  1 + A * (X - 1) * frameInv A G

variable {A G}

theorem frameMat_one : frameMat A G 1 = 1 := by
  rw [frameMat, sub_self, Matrix.mul_zero, Matrix.zero_mul, add_zero]

theorem frameInv_mul (hG : Aᵀ * gram K N * A = G) (hGG : G * G = -1) : frameInv A G * A = 1 := by
  rw [frameInv, Matrix.neg_mul, Matrix.mul_assoc G, Matrix.mul_assoc G, hG, hGG, neg_neg]

theorem transpose_mul_gram_eq_mul_frameInv (hGG : G * G = -1) :
    Aᵀ * gram K N = G * frameInv A G := by
  rw [frameInv, Matrix.mul_neg, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hGG, Matrix.neg_mul,
    Matrix.neg_mul, Matrix.one_mul, neg_neg]

omit [Fintype ι] [DecidableEq ι] in
theorem frameGram_transpose (hG : Aᵀ * gram K N * A = G) : Gᵀ = -G := by
  rw [← hG, transpose_mul, transpose_mul, transpose_transpose, gram_transpose_eq_neg,
    Matrix.neg_mul, Matrix.mul_neg, Matrix.mul_assoc]

theorem frameInv_transpose_mul (hG : Aᵀ * gram K N * A = G) (hGG : G * G = -1) :
    (frameInv A G)ᵀ * G = gram K N * A := by
  rw [frameInv, transpose_neg, transpose_mul, transpose_mul, transpose_transpose,
    frameGram_transpose hG, gram_transpose_eq_neg]
  simp only [Matrix.neg_mul, Matrix.mul_neg, neg_neg, Matrix.mul_assoc, hGG, Matrix.mul_one]

theorem frameMat_mul (hG : Aᵀ * gram K N * A = G) (hGG : G * G = -1) (X Y : Matrix ι ι K) :
    frameMat A G (X * Y) = frameMat A G X * frameMat A G Y := by
  have hBA := frameInv_mul hG hGG
  set B := frameInv A G
  have e1 : X * Y - 1 = (X - 1) + (Y - 1) + (X - 1) * (Y - 1) := by noncomm_ring
  have e2 : A * (X - 1) * B * (A * (Y - 1) * B) = A * ((X - 1) * (Y - 1)) * B := by
    calc A * (X - 1) * B * (A * (Y - 1) * B) = A * (X - 1) * (B * A) * (Y - 1) * B := by
          simp only [Matrix.mul_assoc]
      _ = A * ((X - 1) * (Y - 1)) * B := by
          rw [hBA, Matrix.mul_one]
          simp only [Matrix.mul_assoc]
  have e3 : A * (X * Y - 1) * B =
      A * (X - 1) * B + A * (Y - 1) * B + A * (X - 1) * B * (A * (Y - 1) * B) := by
    rw [e2, e1]
    simp only [Matrix.mul_add, Matrix.add_mul]
  simp only [frameMat]
  rw [e3]
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one]
  abel

theorem frameMat_symplectic (hG : Aᵀ * gram K N * A = G) (hGG : G * G = -1) {X : Matrix ι ι K}
    (hX : Xᵀ * G * X = G) : (frameMat A G X)ᵀ * gram K N * frameMat A G X = gram K N := by
  have hBA := frameInv_mul hG hGG
  have hAJ := transpose_mul_gram_eq_mul_frameInv (A := A) hGG
  have hBG := frameInv_transpose_mul hG hGG
  set B := frameInv A G
  set J : Matrix (Fin N ⊕ Fin N) (Fin N ⊕ Fin N) K := gram K N
  set Y := X - 1 with hY
  have hkey : Yᵀ * G + G * Y + Yᵀ * G * Y = 0 := by
    have : Yᵀ * G + G * Y + Yᵀ * G * Y = Xᵀ * G * X - G := by
      rw [hY, transpose_sub, transpose_one]
      noncomm_ring
    rw [this, hX, sub_self]
  have htr : (frameMat A G X)ᵀ = 1 + Bᵀ * Yᵀ * Aᵀ := by
    rw [frameMat, transpose_add, transpose_one, transpose_mul, transpose_mul, Matrix.mul_assoc]
  have hJA : J * A = Bᵀ * G := hBG.symm
  rw [htr, frameMat]
  calc (1 + Bᵀ * Yᵀ * Aᵀ) * J * (1 + A * Y * B) =
      J + Bᵀ * Yᵀ * (Aᵀ * J) + (J * A) * Y * B + Bᵀ * Yᵀ * (Aᵀ * J) * A * Y * B := by
        simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one,
          Matrix.mul_assoc]
        abel
    _ = J + Bᵀ * (Yᵀ * G + G * Y + Yᵀ * G * Y) * B := by
        rw [hAJ, hJA]
        have e : Bᵀ * Yᵀ * (G * B) * A * Y * B = Bᵀ * (Yᵀ * G * Y) * B := by
          calc Bᵀ * Yᵀ * (G * B) * A * Y * B = Bᵀ * Yᵀ * G * (B * A) * Y * B := by
                simp only [Matrix.mul_assoc]
            _ = _ := by rw [hBA, Matrix.mul_one]; simp only [Matrix.mul_assoc]
        rw [e]
        simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
        abel
    _ = J := by rw [hkey, Matrix.mul_zero, Matrix.zero_mul, add_zero]

theorem frameInv_sandwich (hBA : frameInv A G * A = 1) (Y : Matrix ι ι K) :
    frameInv A G * (A * Y * frameInv A G) * A = Y := by
  calc frameInv A G * (A * Y * frameInv A G) * A =
      (frameInv A G * A) * Y * (frameInv A G * A) := by simp only [Matrix.mul_assoc]
    _ = Y := by rw [hBA, Matrix.one_mul, Matrix.mul_one]

theorem frameInv_mul_mat (hG : Aᵀ * gram K N * A = G) (hGG : G * G = -1) {s : StatedSp N K}
    {D D' : Matrix ι ι K} (hD : mat N K s * A = A * D) (hD' : mat N K s⁻¹ * A = A * D') :
    frameInv A G * mat N K s = D * frameInv A G := by
  have hBA := frameInv_mul hG hGG
  have hAJ := transpose_mul_gram_eq_mul_frameInv (A := A) hGG
  set S := mat N K s with hSdef
  set S' := mat N K s⁻¹ with hS'def
  have hS'S : S' * S = 1 := by rw [hSdef, hS'def, ← map_mul, inv_mul_cancel, map_one]
  have hS' : S'ᵀ * gram K N * S' = gram K N := mat_transpose_mul_gram_mul s⁻¹
  have hJS : gram K N * S = S'ᵀ * gram K N := by
    calc gram K N * S = (S'ᵀ * gram K N * S') * S := by rw [hS']
      _ = S'ᵀ * gram K N * (S' * S) := by simp only [Matrix.mul_assoc]
      _ = S'ᵀ * gram K N := by rw [hS'S, Matrix.mul_one]
  have hD'D : D' * D = 1 := by
    have e : A * (D' * D) = A := by
      calc A * (D' * D) = (A * D') * D := by rw [Matrix.mul_assoc]
        _ = S' * A * D := by rw [hD']
        _ = S' * (S * A) := by rw [Matrix.mul_assoc, ← hD]
        _ = (S' * S) * A := by rw [Matrix.mul_assoc]
        _ = A := by rw [hS'S, Matrix.one_mul]
    calc D' * D = frameInv A G * (A * (D' * D)) := by
          rw [← Matrix.mul_assoc, hBA, Matrix.one_mul]
      _ = 1 := by rw [e, hBA]
  have hGD' : D'ᵀ * G * D' = G := by
    calc D'ᵀ * G * D' = D'ᵀ * (Aᵀ * gram K N * A) * D' := by rw [hG]
      _ = (A * D')ᵀ * gram K N * (A * D') := by
          rw [transpose_mul]
          simp only [Matrix.mul_assoc]
      _ = (S' * A)ᵀ * gram K N * (S' * A) := by rw [hD']
      _ = Aᵀ * (S'ᵀ * gram K N * S') * A := by
          rw [transpose_mul]
          simp only [Matrix.mul_assoc]
      _ = G := by rw [hS', hG]
  have hD'G : D'ᵀ * G = G * D := by
    calc D'ᵀ * G = D'ᵀ * G * (D' * D) := by rw [hD'D, Matrix.mul_one]
      _ = (D'ᵀ * G * D') * D := by simp only [Matrix.mul_assoc]
      _ = G * D := by rw [hGD']
  calc frameInv A G * S = -(G * Aᵀ * (gram K N * S)) := by
        rw [frameInv, Matrix.neg_mul]
        simp only [Matrix.mul_assoc]
    _ = -(G * (S' * A)ᵀ * gram K N) := by
        rw [hJS, transpose_mul]
        simp only [Matrix.mul_assoc]
    _ = -(G * D'ᵀ * (Aᵀ * gram K N)) := by
        rw [hD', transpose_mul]
        simp only [Matrix.mul_assoc]
    _ = -(G * (D'ᵀ * G) * frameInv A G) := by
        rw [hAJ]
        simp only [Matrix.mul_assoc]
    _ = D * frameInv A G := by
        rw [hD'G, ← Matrix.mul_assoc, hGG]
        simp

theorem commute_frameMat {S : Matrix (Fin N ⊕ Fin N) (Fin N ⊕ Fin N) K} {D X : Matrix ι ι K}
    (hA : S * A = A * D) (hB : frameInv A G * S = D * frameInv A G) (hX : D * X = X * D) :
    S * frameMat A G X = frameMat A G X * S := by
  have hX' : D * (X - 1) = (X - 1) * D := by
    rw [Matrix.mul_sub, Matrix.sub_mul, hX, Matrix.mul_one, Matrix.one_mul]
  rw [frameMat, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul]
  congr 1
  calc S * (A * (X - 1) * frameInv A G) = (S * A) * (X - 1) * frameInv A G := by
        simp only [Matrix.mul_assoc]
    _ = A * (D * (X - 1)) * frameInv A G := by
        rw [hA]
        simp only [Matrix.mul_assoc]
    _ = A * (X - 1) * (D * frameInv A G) := by
        rw [hX']
        simp only [Matrix.mul_assoc]
    _ = A * (X - 1) * frameInv A G * S := by
        rw [← hB]
        simp only [Matrix.mul_assoc]

theorem commute_of_commute_frameMat (hG : Aᵀ * gram K N * A = G) (hGG : G * G = -1)
    {S : Matrix (Fin N ⊕ Fin N) (Fin N ⊕ Fin N) K} {D X : Matrix ι ι K}
    (hA : S * A = A * D) (hB : frameInv A G * S = D * frameInv A G)
    (h : S * frameMat A G X = frameMat A G X * S) : D * X = X * D := by
  have hBA := frameInv_mul hG hGG
  have h1 : S * frameMat A G X = S + A * (D * (X - 1)) * frameInv A G := by
    rw [frameMat, Matrix.mul_add, Matrix.mul_one, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hA]
    simp only [Matrix.mul_assoc]
  have h2 : frameMat A G X * S = S + A * ((X - 1) * D) * frameInv A G := by
    rw [frameMat, Matrix.add_mul, Matrix.one_mul, Matrix.mul_assoc _ (frameInv A G), hB]
    simp only [Matrix.mul_assoc]
  rw [h1, h2] at h
  have e := add_left_cancel h
  have e2 : D * (X - 1) = (X - 1) * D := by
    rw [← frameInv_sandwich hBA (D * (X - 1)), e, frameInv_sandwich hBA]
  have e3 : D * X - D = X * D - D := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul] at e2
    exact e2
  exact sub_left_injective e3

variable (A G) in
@[expose] noncomputable def frameHom {m : ℕ} (hG : Aᵀ * gram K N * A = G) (hGG : G * G = -1)
    (ρ : StatedSp m K →* Matrix ι ι K) (hρ : ∀ g, (ρ g)ᵀ * G * ρ g = G) :
    StatedSp m K →* StatedSp N K where
  toFun g := ofSymplecticMat (frameMat A G (ρ g)) (frameMat_symplectic hG hGG (hρ g))
  map_one' := mat_injective (by rw [mat_ofSymplecticMat, map_one, map_one, frameMat_one])
  map_mul' g h := mat_injective (by
    rw [map_mul (mat N K)]
    change frameMat A G (ρ (g * h)) = frameMat A G (ρ g) * frameMat A G (ρ h)
    rw [map_mul, frameMat_mul hG hGG])

theorem mat_frameHom {m : ℕ} (hG : Aᵀ * gram K N * A = G) (hGG : G * G = -1)
    (ρ : StatedSp m K →* Matrix ι ι K) (hρ : ∀ g, (ρ g)ᵀ * G * ρ g = G) (g : StatedSp m K) :
    mat N K (frameHom A G hG hGG ρ hρ g) = frameMat A G (ρ g) := rfl

end Frame

section Columns

@[expose] def colMat (u : ι → Fin N ⊕ Fin N → K) : Matrix (Fin N ⊕ Fin N) ι K :=
  Matrix.of fun r c => u c r

@[expose] def spForm (x y : Fin N ⊕ Fin N → K) : K := x ⬝ᵥ (gram K N *ᵥ y)

omit [Fintype ι] [DecidableEq ι] in
theorem colMat_gram_apply (u : ι → Fin N ⊕ Fin N → K) (c c' : ι) :
    ((colMat u)ᵀ * gram K N * colMat u) c c' = spForm (u c) (u c') := by
  simp only [spForm, Matrix.mul_apply, transpose_apply, colMat, of_apply, dotProduct, mulVec,
    Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun r _ => ?_
  ring

omit [Fintype ι] [DecidableEq ι] in
theorem mul_colMat (M : Matrix (Fin N ⊕ Fin N) (Fin N ⊕ Fin N) K) (u : ι → Fin N ⊕ Fin N → K) :
    M * colMat u = colMat (fun c => M *ᵥ u c) := by
  ext r c
  simp [colMat, Matrix.mul_apply, mulVec, dotProduct]

omit [DecidableEq ι] in
theorem colMat_mul (u : ι → Fin N ⊕ Fin N → K) (D : Matrix ι ι K) :
    colMat u * D = colMat (fun c => ∑ c', D c' c • u c') := by
  ext r c
  simp [colMat, Matrix.mul_apply, Finset.sum_apply, mul_comm]

end Columns

section Form

variable {x y z : Fin N ⊕ Fin N → K}

theorem gram_mulVec_inl (y : Fin N ⊕ Fin N → K) (i : Fin N) :
    (gram K N *ᵥ y) (Sum.inl i) = y (Sum.inr i) := by
  simp [CFSG.ClassicalInvolution.Models.SymplecticPairs.gram, mulVec, dotProduct,
    Fintype.sum_sum_type, Matrix.one_apply]

theorem gram_mulVec_inr (y : Fin N ⊕ Fin N → K) (i : Fin N) :
    (gram K N *ᵥ y) (Sum.inr i) = -y (Sum.inl i) := by
  simp [CFSG.ClassicalInvolution.Models.SymplecticPairs.gram, mulVec, dotProduct,
    Fintype.sum_sum_type, Matrix.one_apply]

theorem spForm_apply (x y : Fin N ⊕ Fin N → K) :
    spForm x y = ∑ i, (x (Sum.inl i) * y (Sum.inr i) - x (Sum.inr i) * y (Sum.inl i)) := by
  rw [spForm, dotProduct, Fintype.sum_sum_type, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [gram_mulVec_inl, gram_mulVec_inr]
  ring

theorem spForm_add_left : spForm (x + y) z = spForm x z + spForm y z := by
  simp only [spForm, add_dotProduct]

theorem spForm_add_right : spForm x (y + z) = spForm x y + spForm x z := by
  simp only [spForm, mulVec_add, dotProduct_add]

theorem spForm_smul_left (c : K) : spForm (c • x) y = c * spForm x y := by
  simp only [spForm, smul_dotProduct, smul_eq_mul]

theorem spForm_smul_right (c : K) : spForm x (c • y) = c * spForm x y := by
  simp only [spForm, mulVec_smul, dotProduct_smul, smul_eq_mul]

theorem spForm_sub_left : spForm (x - y) z = spForm x z - spForm y z := by
  simp only [spForm, sub_dotProduct]

theorem spForm_sub_right : spForm x (y - z) = spForm x y - spForm x z := by
  simp only [spForm, mulVec_sub, dotProduct_sub]

theorem spForm_swap : spForm y x = -spForm x y := by
  rw [spForm_apply, spForm_apply, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

theorem spForm_mat_mulVec (g : StatedSp N K) (x y : Fin N ⊕ Fin N → K) :
    spForm (mat N K g *ᵥ x) (mat N K g *ᵥ y) = spForm x y := by
  rw [spForm, spForm, ← vecMul_transpose (mat N K g) x, ← dotProduct_mulVec x (mat N K g)ᵀ]
  congr 1
  rw [mulVec_mulVec, mulVec_mulVec, mat_transpose_mul_gram_mul]

end Form

end CFSG.SeitzReduction.SymplecticPilot
