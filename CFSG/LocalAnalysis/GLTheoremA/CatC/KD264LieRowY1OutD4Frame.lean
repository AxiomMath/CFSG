module

public import CFSG.Open.StatedDefs
public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie

open CFSG.Open Matrix
open scoped commutatorElement

abbrev D4Model (K : Type) [Field K] : Type :=
  StatedProj (StatedOmega (StatedQuadPlus 4 K))

abbrev Ix4 : Type := Fin 4 ⊕ Fin 4

@[expose] def ixEquiv : Ix4 ≃ Fin 2 × Fin 4 where
  toFun i := i.elim (fun k => (0, k)) (fun k => (1, k))
  invFun p := if p.1 = 0 then Sum.inl p.2 else Sum.inr p.2
  left_inv i := by
    rcases i with k | k <;> simp
  right_inv p := by
    obtain ⟨b, k⟩ := p
    fin_cases b <;> simp

theorem ixEquiv_inl (k : Fin 4) : ixEquiv (Sum.inl k) = (0, k) := rfl

theorem ixEquiv_inr (k : Fin 4) : ixEquiv (Sum.inr k) = (1, k) := rfl

@[expose] def mRot : Matrix (Fin 2) (Fin 2) ℤ := !![0, -1; 1, -1]

@[expose] def nRot : Matrix (Fin 2) (Fin 2) ℤ := !![0, 1; -1, -1]

@[expose] def sRefM : Matrix (Fin 2) (Fin 2) ℤ := !![-1, 1; 0, 1]

@[expose] def sRefN : Matrix (Fin 2) (Fin 2) ℤ := !![-1, -1; 0, 1]

@[expose] def powM : Fin 3 → Matrix (Fin 2) (Fin 2) ℤ := ![1, mRot, mRot * mRot]

@[expose] def powN : Fin 3 → Matrix (Fin 2) (Fin 2) ℤ := ![1, nRot, nRot * nRot]

@[expose] def tabZ (k : Fin 4) (n : Fin 3) : Matrix (Fin 2) (Fin 2) ℤ :=
  if k.val % 2 = 0 then powM n else powN n

@[expose] def sTab (k : Fin 4) : Matrix (Fin 2) (Fin 2) ℤ :=
  if k.val % 2 = 0 then sRefM else sRefN

theorem powM_add (a b : Fin 3) : powM (a + b) = powM a * powM b := by
  fin_cases a <;> fin_cases b <;> decide

theorem powN_add (a b : Fin 3) : powN (a + b) = powN a * powN b := by
  fin_cases a <;> fin_cases b <;> decide

theorem tabZ_add (k : Fin 4) (a b : Fin 3) : tabZ k (a + b) = tabZ k a * tabZ k b := by
  unfold tabZ
  split_ifs
  · exact powM_add a b
  · exact powN_add a b

theorem tabZ_zero (k : Fin 4) : tabZ k 0 = 1 := by
  unfold tabZ
  split_ifs <;> rfl

theorem sTab_mul (k : Fin 4) (n : Fin 3) : sTab k * tabZ k n * sTab k = tabZ k (-n) := by
  unfold sTab tabZ
  split_ifs <;> fin_cases n <;> decide

theorem sTab_mul_self (k : Fin 4) : sTab k * sTab k = 1 := by
  unfold sTab
  split_ifs <;> decide

@[expose] def Dblk (t : Fin 4 → Fin 3) : Matrix (Fin 2 × Fin 4) (Fin 2 × Fin 4) ℤ :=
  Matrix.blockDiagonal fun k => tabZ k (t k)

@[expose] def Sblk : Matrix (Fin 2 × Fin 4) (Fin 2 × Fin 4) ℤ :=
  Matrix.blockDiagonal fun k => sTab k

@[expose] def Dint (t : Fin 4 → Fin 3) : Matrix Ix4 Ix4 ℤ := (Dblk t).submatrix ixEquiv ixEquiv

@[expose] def Sint : Matrix Ix4 Ix4 ℤ := Sblk.submatrix ixEquiv ixEquiv

theorem blockDiagonal_const_one :
    (Matrix.blockDiagonal fun _ : Fin 4 => (1 : Matrix (Fin 2) (Fin 2) ℤ)) =
      (1 : Matrix (Fin 2 × Fin 4) (Fin 2 × Fin 4) ℤ) :=
  Matrix.blockDiagonal_one

theorem Dint_add (s t : Fin 4 → Fin 3) : Dint (s + t) = Dint s * Dint t := by
  unfold Dint Dblk
  rw [Matrix.submatrix_mul_equiv, ← Matrix.blockDiagonal_mul]
  have h : (fun k : Fin 4 => tabZ k ((s + t) k)) = fun k => tabZ k (s k) * tabZ k (t k) := by
    funext k
    exact tabZ_add k (s k) (t k)
  rw [h]

theorem Dint_zero : Dint 0 = 1 := by
  unfold Dint Dblk
  have h : (fun k : Fin 4 => tabZ k ((0 : Fin 4 → Fin 3) k)) = fun _ => 1 := by
    funext k
    exact tabZ_zero k
  rw [h, blockDiagonal_const_one, Matrix.submatrix_one_equiv]

theorem Sint_mul_self : Sint * Sint = 1 := by
  unfold Sint Sblk
  rw [Matrix.submatrix_mul_equiv, ← Matrix.blockDiagonal_mul]
  have h : (fun k : Fin 4 => sTab k * sTab k) = fun _ => 1 := by
    funext k
    exact sTab_mul_self k
  rw [h, blockDiagonal_const_one, Matrix.submatrix_one_equiv]

theorem Sint_mul_Dint_mul_Sint (t : Fin 4 → Fin 3) : Sint * Dint t * Sint = Dint (-t) := by
  unfold Sint Dint Sblk Dblk
  rw [Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv, ← Matrix.blockDiagonal_mul,
    ← Matrix.blockDiagonal_mul]
  have h : (fun k : Fin 4 => sTab k * tabZ k (t k) * sTab k) = fun k => tabZ k ((-t) k) := by
    funext k
    exact sTab_mul k (t k)
  rw [h]

@[expose] def d4Pz : Matrix Ix4 Ix4 ℤ :=
  Matrix.fromBlocks !![1, 1, 0, 0; 0, 0, 0, 0; 0, 0, 1, 1; 0, 0, 0, 0]
    !![-1, 0, 0, 0; 1, 1, 0, 0; 0, 0, -1, 0; 0, 0, 1, 1]
    !![1, -1, 0, 0; 0, -1, 0, 0; 0, 0, 1, -1; 0, 0, 0, -1]
    !![0, 0, 0, 0; 1, -1, 0, 0; 0, 0, 0, 0; 0, 0, 1, -1]

@[expose] def d4Pinvz : Matrix Ix4 Ix4 ℤ :=
  Matrix.fromBlocks !![2, 1, 0, 0; 2, 1, 0, 0; 0, 0, 2, 1; 0, 0, 2, 1]
    !![1, 1, 0, 0; -2, 1, 0, 0; 0, 0, 1, 1; 0, 0, -2, 1]
    !![1, 2, 0, 0; -1, 1, 0, 0; 0, 0, 1, 2; 0, 0, -1, 1]
    !![-1, 2, 0, 0; 1, -2, 0, 0; 0, 0, -1, 2; 0, 0, 1, -2]

@[expose] def d4PK (K : Type) [Field K] : Matrix Ix4 Ix4 K := d4Pz.map (Int.castRingHom K)

@[expose] def d4PinvK (K : Type) [Field K] : Matrix Ix4 Ix4 K := d4Pinvz.map (Int.castRingHom K)

@[expose] def d4PiK (K : Type) [Field K] : Matrix Ix4 Ix4 K := (3 : K)⁻¹ • d4PinvK K

theorem d4PK_mul_PinvK (K : Type) [Field K] :
    d4PK K * d4PinvK K = (3 : K) • (1 : Matrix Ix4 Ix4 K) := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [d4PK, d4PinvK, d4Pz, d4Pinvz, Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_four,
      Matrix.one_apply] <;> norm_num

theorem d4PinvK_mul_PK (K : Type) [Field K] :
    d4PinvK K * d4PK K = (3 : K) • (1 : Matrix Ix4 Ix4 K) := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [d4PK, d4PinvK, d4Pz, d4Pinvz, Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_four,
      Matrix.one_apply] <;> norm_num

theorem d4PK_mul_PiK {K : Type} [Field K] (h3 : (3 : K) ≠ 0) : d4PK K * d4PiK K = 1 := by
  unfold d4PiK
  rw [Matrix.mul_smul, d4PK_mul_PinvK, smul_smul, inv_mul_cancel₀ h3, one_smul]

theorem d4PiK_mul_PK {K : Type} [Field K] (h3 : (3 : K) ≠ 0) : d4PiK K * d4PK K = 1 := by
  unfold d4PiK
  rw [Matrix.smul_mul, d4PinvK_mul_PK, smul_smul, inv_mul_cancel₀ h3, one_smul]

@[expose] def d4DK (K : Type) [Field K] (t : Fin 4 → Fin 3) : Matrix Ix4 Ix4 K :=
  (Dint t).map (Int.castRingHom K)

@[expose] def d4SK (K : Type) [Field K] : Matrix Ix4 Ix4 K := Sint.map (Int.castRingHom K)

@[expose] def d4FK (K : Type) [Field K] (t : Fin 4 → Fin 3) : Matrix Ix4 Ix4 K :=
  d4PK K * d4DK K t * d4PiK K

@[expose] def d4SigK (K : Type) [Field K] : Matrix Ix4 Ix4 K := d4PK K * d4SK K * d4PiK K

theorem d4DK_add (K : Type) [Field K] (s t : Fin 4 → Fin 3) :
    d4DK K (s + t) = d4DK K s * d4DK K t := by
  unfold d4DK
  rw [Dint_add, Matrix.map_mul]

theorem d4DK_zero (K : Type) [Field K] : d4DK K 0 = 1 := by
  unfold d4DK
  rw [Dint_zero, Matrix.map_one (Int.castRingHom K) (map_zero _) (map_one _)]

theorem d4SK_mul_self (K : Type) [Field K] : d4SK K * d4SK K = 1 := by
  unfold d4SK
  rw [← Matrix.map_mul, Sint_mul_self, Matrix.map_one (Int.castRingHom K) (map_zero _) (map_one _)]

theorem d4SK_DK_SK (K : Type) [Field K] (t : Fin 4 → Fin 3) :
    d4SK K * d4DK K t * d4SK K = d4DK K (-t) := by
  unfold d4SK d4DK
  rw [← Matrix.map_mul, ← Matrix.map_mul, Sint_mul_Dint_mul_Sint]

theorem d4conj_mul {R ι : Type} [Semiring R] [Fintype ι] [DecidableEq ι] {A B X Y : Matrix ι ι R}
    (hBA : B * A = 1) : A * X * B * (A * Y * B) = A * (X * Y) * B := by
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc B A, hBA, Matrix.one_mul]

theorem d4conj_back {R ι : Type} [Semiring R] [Fintype ι] [DecidableEq ι] {A B X : Matrix ι ι R}
    (hBA : B * A = 1) : B * (A * X * B) * A = X := by
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc B A, hBA, Matrix.one_mul, Matrix.mul_one]

theorem d4FK_mulVec (K : Type) [Field K] (t : Fin 4 → Fin 3) (v : Ix4 → K) :
    d4FK K t *ᵥ v = d4PK K *ᵥ (d4DK K t *ᵥ (d4PiK K *ᵥ v)) := by
  simp only [d4FK, Matrix.mulVec_mulVec, Matrix.mul_assoc]

theorem d4Sig_mulVec (K : Type) [Field K] (v : Ix4 → K) :
    d4SigK K *ᵥ v = d4PK K *ᵥ (d4SK K *ᵥ (d4PiK K *ᵥ v)) := by
  simp only [d4SigK, Matrix.mulVec_mulVec, Matrix.mul_assoc]

theorem d4FK_zero (K : Type) [Field K] (h3 : (3 : K) ≠ 0) : d4FK K 0 = 1 := by
  unfold d4FK
  rw [d4DK_zero, Matrix.mul_one, d4PK_mul_PiK h3]

theorem d4FK_add (K : Type) [Field K] (h3 : (3 : K) ≠ 0) (s t : Fin 4 → Fin 3) :
    d4FK K (s + t) = d4FK K s * d4FK K t := by
  unfold d4FK
  rw [d4conj_mul (A := d4PK K) (B := d4PiK K) (X := d4DK K s) (Y := d4DK K t) (d4PiK_mul_PK h3),
    d4DK_add]

theorem d4FK_mul_neg (K : Type) [Field K] (h3 : (3 : K) ≠ 0) (t : Fin 4 → Fin 3) :
    d4FK K t * d4FK K (-t) = 1 := by
  rw [← d4FK_add K h3, add_neg_cancel, d4FK_zero K h3]

theorem d4FK_neg_mul (K : Type) [Field K] (h3 : (3 : K) ≠ 0) (t : Fin 4 → Fin 3) :
    d4FK K (-t) * d4FK K t = 1 := by
  rw [← d4FK_add K h3, neg_add_cancel, d4FK_zero K h3]

theorem d4Sig_sq (K : Type) [Field K] (h3 : (3 : K) ≠ 0) : d4SigK K * d4SigK K = 1 := by
  unfold d4SigK
  rw [d4conj_mul (A := d4PK K) (B := d4PiK K) (X := d4SK K) (Y := d4SK K) (d4PiK_mul_PK h3),
    d4SK_mul_self, mul_one, d4PK_mul_PiK h3]

theorem d4_four (t : Fin 4 → Fin 3) : t + t + (t + t) = t := by
  have key : ∀ x : Fin 3, x + x + (x + x) = x := by decide
  funext k
  exact key (t k)

theorem d4FK_comm (K : Type) [Field K] (h3 : (3 : K) ≠ 0) (t : Fin 4 → Fin 3) :
    d4FK K t * d4SigK K * d4FK K (-t) * d4SigK K = d4FK K (t + t) := by
  have hmid : d4DK K t * d4SK K * d4DK K (-t) * d4SK K = d4DK K (t + t) := by
    have h1 : d4DK K t * d4SK K * d4DK K (-t) * d4SK K =
        d4DK K t * (d4SK K * d4DK K (-t) * d4SK K) := by
      simp only [Matrix.mul_assoc]
    rw [h1, d4SK_DK_SK, neg_neg, d4DK_add]
  unfold d4FK d4SigK
  rw [d4conj_mul (A := d4PK K) (B := d4PiK K) (X := d4DK K t) (Y := d4SK K) (d4PiK_mul_PK h3),
    d4conj_mul (A := d4PK K) (B := d4PiK K) (X := d4DK K t * d4SK K) (Y := d4DK K (-t))
      (d4PiK_mul_PK h3),
    d4conj_mul (A := d4PK K) (B := d4PiK K) (X := d4DK K t * d4SK K * d4DK K (-t)) (Y := d4SK K)
      (d4PiK_mul_PK h3), hmid]

@[expose] def d4gE {K : Type} [Field K] (x y : K) : K := x * x - x * y + y * y

@[expose] def d4gO {K : Type} [Field K] (x y : K) : K := -(x * x + x * y + y * y)

@[expose] def d4Qn {K : Type} [Field K] (v : Ix4 → K) : K :=
  d4gE (v (Sum.inl 0)) (v (Sum.inr 0)) + d4gO (v (Sum.inl 1)) (v (Sum.inr 1)) +
    d4gE (v (Sum.inl 2)) (v (Sum.inr 2)) + d4gO (v (Sum.inl 3)) (v (Sum.inr 3))

theorem d4gE_tab {K : Type} [Field K] (k : Fin 4) (hk : k.val % 2 = 0) (n : Fin 3) (x y : K) :
    d4gE (((tabZ k n 0 0 : ℤ) : K) * x + ((tabZ k n 0 1 : ℤ) : K) * y)
      (((tabZ k n 1 0 : ℤ) : K) * x + ((tabZ k n 1 1 : ℤ) : K) * y) = d4gE x y := by
  unfold tabZ
  rw [if_pos hk]
  fin_cases n <;> simp [powM, mRot, d4gE, Matrix.mul_fin_two] <;> ring

theorem d4gO_tab {K : Type} [Field K] (k : Fin 4) (hk : ¬ k.val % 2 = 0) (n : Fin 3) (x y : K) :
    d4gO (((tabZ k n 0 0 : ℤ) : K) * x + ((tabZ k n 0 1 : ℤ) : K) * y)
      (((tabZ k n 1 0 : ℤ) : K) * x + ((tabZ k n 1 1 : ℤ) : K) * y) = d4gO x y := by
  unfold tabZ
  rw [if_neg hk]
  fin_cases n <;> simp [powN, nRot, d4gO, Matrix.mul_fin_two] <;> ring

theorem d4gE_sTab {K : Type} [Field K] (k : Fin 4) (hk : k.val % 2 = 0) (x y : K) :
    d4gE (((sTab k 0 0 : ℤ) : K) * x + ((sTab k 0 1 : ℤ) : K) * y)
      (((sTab k 1 0 : ℤ) : K) * x + ((sTab k 1 1 : ℤ) : K) * y) = d4gE x y := by
  unfold sTab
  rw [if_pos hk]
  simp [sRefM, d4gE] <;> ring

theorem d4gO_sTab {K : Type} [Field K] (k : Fin 4) (hk : ¬ k.val % 2 = 0) (x y : K) :
    d4gO (((sTab k 0 0 : ℤ) : K) * x + ((sTab k 0 1 : ℤ) : K) * y)
      (((sTab k 1 0 : ℤ) : K) * x + ((sTab k 1 1 : ℤ) : K) * y) = d4gO x y := by
  unfold sTab
  rw [if_neg hk]
  simp [sRefN, d4gO] <;> ring

theorem d4DK_mulVec_inl (K : Type) [Field K] (t : Fin 4 → Fin 3) (v : Ix4 → K) (k : Fin 4) :
    (d4DK K t *ᵥ v) (Sum.inl k) =
      ((tabZ k (t k) 0 0 : ℤ) : K) * v (Sum.inl k) + ((tabZ k (t k) 0 1 : ℤ) : K) * v (Sum.inr k) := by
  fin_cases k <;> simp [Matrix.mulVec, dotProduct, d4DK, Fin.sum_univ_four, Dint, Dblk, Fintype.sum_sum_type, ixEquiv_inl,
    ixEquiv_inr, Matrix.blockDiagonal_apply, Finset.sum_ite_eq, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]

theorem d4DK_mulVec_inr (K : Type) [Field K] (t : Fin 4 → Fin 3) (v : Ix4 → K) (k : Fin 4) :
    (d4DK K t *ᵥ v) (Sum.inr k) =
      ((tabZ k (t k) 1 0 : ℤ) : K) * v (Sum.inl k) + ((tabZ k (t k) 1 1 : ℤ) : K) * v (Sum.inr k) := by
  fin_cases k <;> simp [Matrix.mulVec, dotProduct, d4DK, Fin.sum_univ_four, Dint, Dblk, Fintype.sum_sum_type, ixEquiv_inl,
    ixEquiv_inr, Matrix.blockDiagonal_apply, Finset.sum_ite_eq, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]

theorem d4SK_mulVec_inl (K : Type) [Field K] (v : Ix4 → K) (k : Fin 4) :
    (d4SK K *ᵥ v) (Sum.inl k) =
      ((sTab k 0 0 : ℤ) : K) * v (Sum.inl k) + ((sTab k 0 1 : ℤ) : K) * v (Sum.inr k) := by
  fin_cases k <;> simp [Matrix.mulVec, dotProduct, d4SK, Fin.sum_univ_four, Sint, Sblk, Fintype.sum_sum_type, ixEquiv_inl,
    ixEquiv_inr, Matrix.blockDiagonal_apply, Finset.sum_ite_eq, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]

theorem d4SK_mulVec_inr (K : Type) [Field K] (v : Ix4 → K) (k : Fin 4) :
    (d4SK K *ᵥ v) (Sum.inr k) =
      ((sTab k 1 0 : ℤ) : K) * v (Sum.inl k) + ((sTab k 1 1 : ℤ) : K) * v (Sum.inr k) := by
  fin_cases k <;> simp [Matrix.mulVec, dotProduct, d4SK, Fin.sum_univ_four, Sint, Sblk, Fintype.sum_sum_type, ixEquiv_inl,
    ixEquiv_inr, Matrix.blockDiagonal_apply, Finset.sum_ite_eq, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]

theorem d4Qn_DK (K : Type) [Field K] (t : Fin 4 → Fin 3) (v : Ix4 → K) :
    d4Qn (d4DK K t *ᵥ v) = d4Qn v := by
  unfold d4Qn
  simp only [d4DK_mulVec_inl, d4DK_mulVec_inr]
  rw [d4gE_tab 0 (by decide) (t 0), d4gO_tab 1 (by decide) (t 1),
    d4gE_tab 2 (by decide) (t 2), d4gO_tab 3 (by decide) (t 3)]

theorem d4Qn_SK (K : Type) [Field K] (v : Ix4 → K) :
    d4Qn (d4SK K *ᵥ v) = d4Qn v := by
  unfold d4Qn
  simp only [d4SK_mulVec_inl, d4SK_mulVec_inr]
  rw [d4gE_sTab 0 (by decide), d4gO_sTab 1 (by decide), d4gE_sTab 2 (by decide),
    d4gO_sTab 3 (by decide)]

theorem d4StQ_PK (K : Type) [Field K] (w : Ix4 → K) :
    StatedQuadPlus 4 K (d4PK K *ᵥ w) = d4Qn w := by
  simp [StatedQuadPlus, CFSG.MatrixModel.plusQuadCore, d4Qn, d4gE, d4gO, Matrix.mulVec, dotProduct,
    d4PK, d4Pz, Fintype.sum_sum_type, Fin.sum_univ_four] <;> ring

theorem d4FK_iso (K : Type) [Field K] (h3 : (3 : K) ≠ 0) (t : Fin 4 → Fin 3) (v : Ix4 → K) :
    StatedQuadPlus 4 K (d4FK K t *ᵥ v) = StatedQuadPlus 4 K v := by
  rw [d4FK_mulVec, d4StQ_PK, d4Qn_DK, ← d4StQ_PK, Matrix.mulVec_mulVec, d4PK_mul_PiK h3,
    Matrix.one_mulVec]

theorem d4Sig_iso (K : Type) [Field K] (h3 : (3 : K) ≠ 0) (v : Ix4 → K) :
    StatedQuadPlus 4 K (d4SigK K *ᵥ v) = StatedQuadPlus 4 K v := by
  rw [d4Sig_mulVec, d4StQ_PK, d4Qn_SK, ← d4StQ_PK, Matrix.mulVec_mulVec, d4PK_mul_PiK h3,
    Matrix.one_mulVec]

@[expose] def d4GL (K : Type) [Field K] (h3 : (3 : K) ≠ 0) (t : Fin 4 → Fin 3) :
    Matrix.GeneralLinearGroup Ix4 K :=
  Units.mk (d4FK K t) (d4FK K (-t)) (d4FK_mul_neg K h3 t) (d4FK_neg_mul K h3 t)

@[expose] def d4GLσ (K : Type) [Field K] (h3 : (3 : K) ≠ 0) : Matrix.GeneralLinearGroup Ix4 K :=
  Units.mk (d4SigK K) (d4SigK K) (d4Sig_sq K h3) (d4Sig_sq K h3)

theorem d4GL_comm (K : Type) [Field K] (h3 : (3 : K) ≠ 0) (t : Fin 4 → Fin 3) :
    ⁅d4GL K h3 t, d4GLσ K h3⁆ = d4GL K h3 (t + t) := by
  apply Units.ext
  rw [commutatorElement_def]
  simp only [Units.val_mul]
  exact d4FK_comm K h3 t

theorem d4GL_mem_core (K : Type) [Field K] (h3 : (3 : K) ≠ 0) (t : Fin 4 → Fin 3) :
    d4GL K h3 t ∈ CFSG.MatrixModel.isometryCore (StatedQuadPlus 4 K) :=
  Subgroup.subset_closure (fun v => d4FK_iso K h3 t v)

theorem d4GLσ_mem_core (K : Type) [Field K] (h3 : (3 : K) ≠ 0) :
    d4GLσ K h3 ∈ CFSG.MatrixModel.isometryCore (StatedQuadPlus 4 K) :=
  Subgroup.subset_closure (fun v => d4Sig_iso K h3 v)

theorem d4GL_mem_omega (K : Type) [Field K] (h3 : (3 : K) ≠ 0) (t : Fin 4 → Fin 3) :
    d4GL K h3 t ∈ StatedOmega (StatedQuadPlus 4 K) := by
  have hc := Subgroup.commutator_mem_commutator (d4GL_mem_core K h3 t) (d4GLσ_mem_core K h3)
  rw [d4GL_comm K h3 t] at hc
  have heq : d4GL K h3 t = d4GL K h3 (t + t) * d4GL K h3 (t + t) := by
    apply Units.ext
    show d4FK K t = d4FK K (t + t) * d4FK K (t + t)
    rw [← d4FK_add K h3, d4_four]
  rw [heq]
  exact mul_mem hc hc

theorem d4GL_zero (K : Type) [Field K] (h3 : (3 : K) ≠ 0) : d4GL K h3 0 = 1 :=
  Units.ext (d4FK_zero K h3)

theorem d4GL_add (K : Type) [Field K] (h3 : (3 : K) ≠ 0) (s t : Fin 4 → Fin 3) :
    d4GL K h3 (s + t) = d4GL K h3 s * d4GL K h3 t :=
  Units.ext (d4FK_add K h3 s t)

@[expose] def d4Psi (K : Type) [Field K] (h3 : (3 : K) ≠ 0) :
    Multiplicative (Fin 4 → Fin 3) →* ↥(StatedOmega (StatedQuadPlus 4 K)) where
  toFun g := ⟨d4GL K h3 (Multiplicative.toAdd g), d4GL_mem_omega K h3 _⟩
  map_one' := Subtype.ext (d4GL_zero K h3)
  map_mul' a b := Subtype.ext (d4GL_add K h3 (Multiplicative.toAdd a) (Multiplicative.toAdd b))

@[expose] def d4phi (K : Type) [Field K] (h3 : (3 : K) ≠ 0) :
    Multiplicative (Fin 4 → Fin 3) →* D4Model K :=
  (QuotientGroup.mk' ((StatedScalars Ix4 K).subgroupOf (StatedOmega (StatedQuadPlus 4 K)))).comp
    (d4Psi K h3)

theorem tab01_cast_ne (K : Type) [Field K] (k : Fin 4) (n : Fin 3) (hn : n ≠ 0) :
    ((tabZ k n 0 1 : ℤ) : K) ≠ 0 := by
  revert hn
  fin_cases k <;> fin_cases n <;> simp [tabZ, powM, powN, mRot, nRot, Matrix.mul_fin_two]

theorem d4DK_eq_conj (K : Type) [Field K] (h3 : (3 : K) ≠ 0) (t : Fin 4 → Fin 3) :
    d4PiK K * d4FK K t * d4PK K = d4DK K t := by
  unfold d4FK
  exact d4conj_back (A := d4PK K) (B := d4PiK K) (X := d4DK K t) (d4PiK_mul_PK h3)

theorem d4phi_injective (K : Type) [Field K] (h3 : (3 : K) ≠ 0) :
    Function.Injective (d4phi K h3) := by
  rw [injective_iff_map_eq_one]
  intro a ha
  have hmem : d4Psi K h3 a ∈ (StatedScalars Ix4 K).subgroupOf (StatedOmega (StatedQuadPlus 4 K)) :=
    (QuotientGroup.eq_one_iff _).mp ha
  rw [Subgroup.mem_subgroupOf] at hmem
  obtain ⟨c, hc⟩ := MonoidHom.mem_range.mp hmem
  have hFK : d4FK K (Multiplicative.toAdd a) = (c : K) • (1 : Matrix Ix4 Ix4 K) := by
    have h1 : d4FK K (Multiplicative.toAdd a) =
        ((Matrix.GeneralLinearGroup.scalar Ix4 c : Matrix.GeneralLinearGroup Ix4 K) :
          Matrix Ix4 Ix4 K) := by
      rw [hc]
      rfl
    rw [h1]
    ext i j
    simp [Matrix.GeneralLinearGroup.scalar, Matrix.scalar_apply, Matrix.diagonal_apply,
      Matrix.one_apply, Matrix.smul_apply]
  have hD : d4DK K (Multiplicative.toAdd a) = (c : K) • (1 : Matrix Ix4 Ix4 K) := by
    rw [← d4DK_eq_conj K h3, hFK]
    simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, d4PiK_mul_PK h3]
  have ht : Multiplicative.toAdd a = 0 := by
    funext k
    by_contra hk
    have hent := congrFun (congrFun hD (Sum.inl k)) (Sum.inr k)
    simp [d4DK, Dint, Dblk, ixEquiv_inl, ixEquiv_inr, Matrix.blockDiagonal_apply,
      Matrix.one_apply] at hent
    exact tab01_cast_ne K k _ hk hent
  exact toAdd_eq_zero.mp ht

theorem d4_card_range (K : Type) [Field K] (h3 : (3 : K) ≠ 0) :
    Nat.card (d4phi K h3).range = 3 ^ 4 := by
  rw [Nat.card_congr (MonoidHom.ofInjective (d4phi_injective K h3)).toEquiv.symm,
    Nat.card_congr Multiplicative.ofAdd.symm]
  simp [Nat.card_fun, Nat.card_eq_fintype_card]

theorem d4_pow_three (a : Multiplicative (Fin 4 → Fin 3)) : a ^ 3 = 1 := by
  apply toAdd_eq_zero.mp
  rw [toAdd_pow]
  funext k
  have key : ∀ x : Fin 3, (3 : ℕ) • x = 0 := by decide
  exact key _

theorem d4_isElemAbelian (K : Type) [Field K] (h3 : (3 : K) ≠ 0) :
    CFSG.Open.IsElemAbelian 3 (d4phi K h3).range := by
  refine ⟨⟨⟨fun x y => ?_⟩⟩, fun x hx => ?_⟩
  · obtain ⟨a, ha⟩ := MonoidHom.mem_range.mp x.2
    obtain ⟨b, hb⟩ := MonoidHom.mem_range.mp y.2
    apply Subtype.ext
    show (x : D4Model K) * (y : D4Model K) = (y : D4Model K) * (x : D4Model K)
    rw [← ha, ← hb, ← map_mul, ← map_mul, mul_comm]
  · obtain ⟨a, rfl⟩ := MonoidHom.mem_range.mp hx
    rw [← map_pow, d4_pow_three, map_one]

theorem d4Model_exists_card81 (K : Type) [Field K] (h3 : (3 : K) ≠ 0) :
    ∃ E : Subgroup (D4Model K), CFSG.Open.IsElemAbelian 3 E ∧ Nat.card E = 3 ^ 4 :=
  ⟨(d4phi K h3).range, d4_isElemAbelian K h3, d4_card_range K h3⟩

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie

end
