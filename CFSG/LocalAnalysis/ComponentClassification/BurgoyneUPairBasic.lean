module

public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherHermitian

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.U

open Matrix CFSG Subgroup CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

variable {K : Type} [Field K] {m : ℕ}

variable (K m) in
abbrev prFin : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K ≃ₐ[K]
    Matrix (Fin (m + m)) (Fin (m + m)) K :=
  Matrix.reindexAlgEquiv K K finSumFinEquiv

theorem prFin_apply (X : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) (a b : Fin m ⊕ Fin m) :
    prFin K m X (finSumFinEquiv a) (finSumFinEquiv b) = X a b := by
  simp [prFin, Matrix.coe_reindexAlgEquiv, reindex_apply]

theorem prFin_transpose (X : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) :
    (prFin K m X)ᵀ = prFin K m Xᵀ := by
  ext a b
  simp [prFin, Matrix.coe_reindexAlgEquiv, reindex_apply]

theorem prFin_map (φ : K →+* K) (X : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) :
    (prFin K m X).map φ = prFin K m (X.map φ) := by
  ext a b
  simp [prFin, Matrix.coe_reindexAlgEquiv, reindex_apply]

theorem det_prFin (X : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) :
    (prFin K m X).det = X.det := by
  simp [prFin, Matrix.coe_reindexAlgEquiv]

variable (m) in
@[expose] def prW (l : K) : Matrix (Fin (m + m)) (Fin (m + m)) K :=
  prFin K m (fromBlocks 1 1 (l • 1) (-l • 1))

variable (m) in
@[expose] def prWi (l : K) : Matrix (Fin (m + m)) (Fin (m + m)) K :=
  prFin K m ((2 : K)⁻¹ • fromBlocks 1 (l⁻¹ • 1) 1 (-l⁻¹ • 1))

theorem prW_mul_prWi (h2 : (2 : K) ≠ 0) {l : K} (hl : l ≠ 0) : prW m l * prWi m l = 1 := by
  rw [prW, prWi, ← map_mul, ← map_one (prFin K m)]
  congr 1
  rw [Matrix.mul_smul, fromBlocks_multiply, fromBlocks_smul, ← fromBlocks_one]
  congr 1 <;> ext i j <;> by_cases hij : i = j <;>
    simp [hij, one_apply, Matrix.smul_apply] <;> field_simp <;> ring

theorem prWi_mul_prW (h2 : (2 : K) ≠ 0) {l : K} (hl : l ≠ 0) : prWi m l * prW m l = 1 :=
  mul_eq_one_comm.1 (prW_mul_prWi h2 hl)

variable (m) in
@[expose] def prA (l : K) : Matrix (Fin (m + m)) (Fin (m + m)) K :=
  prFin K m (fromBlocks 0 1 ((l ^ 2) • 1) 0)

variable (m) in
@[expose] def prPhi (l : K) (G G' : Matrix (Fin m) (Fin m) K) :
    Matrix (Fin (m + m)) (Fin (m + m)) K :=
  prW m l * prFin K m (fromBlocks G 0 0 G') * prWi m l

theorem prPhi_mul (h2 : (2 : K) ≠ 0) {l : K} (hl : l ≠ 0) (G G' H H' : Matrix (Fin m) (Fin m) K) :
    prPhi m l G G' * prPhi m l H H' = prPhi m l (G * H) (G' * H') := by
  rw [prPhi, prPhi, prPhi]
  calc prW m l * prFin K m (fromBlocks G 0 0 G') * prWi m l *
        (prW m l * prFin K m (fromBlocks H 0 0 H') * prWi m l) =
      prW m l * prFin K m (fromBlocks G 0 0 G') * (prWi m l * prW m l) *
        prFin K m (fromBlocks H 0 0 H') * prWi m l := by simp only [Matrix.mul_assoc]
    _ = prW m l * prFin K m (fromBlocks (G * H) 0 0 (G' * H')) * prWi m l := by
      rw [prWi_mul_prW h2 hl, Matrix.mul_one, Matrix.mul_assoc (prW m l), ← map_mul,
        fromBlocks_multiply]
      simp

theorem prPhi_one (h2 : (2 : K) ≠ 0) {l : K} (hl : l ≠ 0) : prPhi m l 1 1 = 1 := by
  rw [prPhi, fromBlocks_one, map_one, Matrix.mul_one, prW_mul_prWi h2 hl]

theorem prA_eq_prPhi (h2 : (2 : K) ≠ 0) {l : K} (hl : l ≠ 0) :
    prA m l = prPhi m l (l • 1) (-(l • 1)) := by
  rw [prPhi, prW, prWi, ← map_mul, ← map_mul, prA]
  congr 1
  rw [fromBlocks_multiply, Matrix.mul_smul, fromBlocks_multiply, fromBlocks_smul]
  congr 1 <;> ext i j <;> by_cases hij : i = j <;>
    simp [hij, one_apply, Matrix.smul_apply] <;> field_simp <;> ring

theorem prPhi_eq (h2 : (2 : K) ≠ 0) {l : K} (hl : l ≠ 0) (G G' : Matrix (Fin m) (Fin m) K) :
    prPhi m l G G' = prFin K m (fromBlocks ((2 : K)⁻¹ • (G + G')) ((2 * l)⁻¹ • (G - G'))
      (((2 : K)⁻¹ * l) • (G - G')) ((2 : K)⁻¹ • (G + G'))) := by
  rw [prPhi, prW, prWi, ← map_mul, ← map_mul]
  congr 1
  rw [fromBlocks_multiply, Matrix.mul_smul, fromBlocks_multiply, fromBlocks_smul]
  congr 1 <;> ext i j <;>
    simp [Matrix.smul_apply, Matrix.add_apply, Matrix.sub_apply, h2] <;> field_simp <;> ring

theorem det_prPhi (h2 : (2 : K) ≠ 0) {l : K} (hl : l ≠ 0) (G G' : Matrix (Fin m) (Fin m) K) :
    (prPhi m l G G').det = G.det * G'.det := by
  have e1 := congrArg Matrix.det (prW_mul_prWi (m := m) h2 hl)
  rw [det_mul, det_one] at e1
  rw [prPhi, det_mul, det_mul, det_prFin, det_fromBlocks_zero₂₁]
  linear_combination G.det * G'.det * e1

theorem exists_prPhi_of_commute (h2 : (2 : K) ≠ 0) {l : K} (hl : l ≠ 0)
    {D : Matrix (Fin (m + m)) (Fin (m + m)) K} (hD : D * prA m l = prA m l * D) :
    ∃ G G' : Matrix (Fin m) (Fin m) K, D = prPhi m l G G' := by
  set Y := (prFin K m).symm (prWi m l * D * prW m l) with hY
  have hDY : D = prW m l * prFin K m Y * prWi m l := by
    rw [hY, AlgEquiv.apply_symm_apply]
    calc D = (prW m l * prWi m l) * D * (prW m l * prWi m l) := by
          rw [prW_mul_prWi h2 hl, Matrix.one_mul, Matrix.mul_one]
      _ = _ := by simp only [Matrix.mul_assoc]
  have hYc : Y * fromBlocks (l • 1) 0 0 (-(l • 1)) = fromBlocks (l • 1) 0 0 (-(l • 1)) * Y := by
    apply (prFin K m).injective
    rw [map_mul, map_mul]
    have e := hD
    rw [prA_eq_prPhi h2 hl, prPhi, hDY] at e
    have key : ∀ X Z : Matrix (Fin (m + m)) (Fin (m + m)) K,
        prW m l * X * prWi m l * (prW m l * Z * prWi m l) = prW m l * (X * Z) * prWi m l := by
      intro X Z
      calc prW m l * X * prWi m l * (prW m l * Z * prWi m l) =
          prW m l * X * (prWi m l * prW m l) * Z * prWi m l := by simp only [Matrix.mul_assoc]
        _ = _ := by rw [prWi_mul_prW h2 hl, Matrix.mul_one]; simp only [Matrix.mul_assoc]
    rw [key, key] at e
    calc prFin K m Y * prFin K m (fromBlocks (l • 1) 0 0 (-(l • 1))) =
        prWi m l * (prW m l * (prFin K m Y * prFin K m (fromBlocks (l • 1) 0 0 (-(l • 1)))) *
          prWi m l) * prW m l := by
          simp only [← Matrix.mul_assoc, prWi_mul_prW h2 hl, Matrix.one_mul]
          rw [Matrix.mul_assoc _ (prWi m l), prWi_mul_prW h2 hl, Matrix.mul_one]
      _ = prWi m l * (prW m l * (prFin K m (fromBlocks (l • 1) 0 0 (-(l • 1))) *
          prFin K m Y) * prWi m l) * prW m l := by rw [e]
      _ = _ := by
          simp only [← Matrix.mul_assoc, prWi_mul_prW h2 hl, Matrix.one_mul]
          rw [Matrix.mul_assoc _ (prWi m l), prWi_mul_prW h2 hl, Matrix.mul_one]
  rw [← fromBlocks_toBlocks Y, fromBlocks_multiply, fromBlocks_multiply] at hYc
  simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Matrix.mul_smul,
    Matrix.smul_mul, Matrix.mul_one, Matrix.one_mul, Matrix.mul_neg, Matrix.neg_mul] at hYc
  obtain ⟨-, h12, h21, -⟩ := fromBlocks_inj.1 hYc
  have hz : ∀ Z : Matrix (Fin m) (Fin m) K, -(l • Z) = l • Z → Z = 0 := by
    intro Z hZ
    have : (2 * l) • Z = 0 := by
      rw [mul_smul, two_smul]
      calc l • Z + l • Z = -(l • Z) + l • Z := by rw [hZ]
        _ = 0 := neg_add_cancel _
    exact (smul_eq_zero.1 this).resolve_left (mul_ne_zero h2 hl)
  have h12' : Y.toBlocks₁₂ = 0 := hz _ h12
  have h21' : Y.toBlocks₂₁ = 0 := hz _ h21.symm
  have hYb : Y = fromBlocks Y.toBlocks₁₁ 0 0 Y.toBlocks₂₂ := by
    conv_lhs => rw [← fromBlocks_toBlocks Y]
    rw [h12', h21']
  refine ⟨Y.toBlocks₁₁, Y.toBlocks₂₂, ?_⟩
  rw [hDY, prPhi, ← hYb]

section Unitary

variable {p f : ℕ} (h : UnitaryFieldData p f K)

theorem conjT_mul {ι : Type} [Fintype ι] (A B : Matrix ι ι K) :
    ((A * B).map h.bar)ᵀ = (B.map h.bar)ᵀ * (A.map h.bar)ᵀ := by
  rw [Matrix.map_mul, transpose_mul]

theorem conjT_conjT {ι : Type} (A : Matrix ι ι K) : (((A.map h.bar)ᵀ).map h.bar)ᵀ = A := by
  ext i j
  simp [h.bar_bar]

theorem smul_one_map (c : K) :
    ((c • (1 : Matrix (Fin m) (Fin m) K)).map h.bar)ᵀ = h.bar c • 1 := by
  ext i j
  by_cases hij : i = j
  · subst hij
    simp
  · simp [one_apply, hij, Ne.symm hij]

theorem prW_gram {l : K} (hN : h.norm l = -1) :
    ((prW m l).map h.bar)ᵀ * prW m l = (2 : K) • prFin K m (fromBlocks 0 1 1 0) := by
  have hN' : h.bar l * l = -1 := by rw [mul_comm]; exact hN
  rw [prW, prFin_map, prFin_transpose, ← map_mul, ← map_smul]
  congr 1
  have e1 : ((1 : Matrix (Fin m) (Fin m) K).map h.bar)ᵀ = 1 := by
    rw [Matrix.map_one _ (map_zero h.bar) (map_one h.bar), transpose_one]
  rw [fromBlocks_map, fromBlocks_transpose, e1, smul_one_map h, smul_one_map h, map_neg,
    fromBlocks_multiply, fromBlocks_smul]
  have hN0 : l * h.bar l = -1 := hN
  congr 1 <;> ext i j <;> by_cases hij : i = j <;>
    simp [hij, one_apply, Matrix.smul_apply] <;>
    first | linear_combination hN0 | linear_combination -hN0

theorem diag_gram_iff (G G' : Matrix (Fin m) (Fin m) K) :
    ((prFin K m (fromBlocks G 0 0 G')).map h.bar)ᵀ * prFin K m (fromBlocks 0 1 1 0) *
        prFin K m (fromBlocks G 0 0 G') = prFin K m (fromBlocks 0 1 1 0) ↔
      (G.map h.bar)ᵀ * G' = 1 := by
  rw [prFin_map, prFin_transpose, ← map_mul, ← map_mul, (prFin K m).injective.eq_iff,
    fromBlocks_map, fromBlocks_transpose, fromBlocks_multiply, fromBlocks_multiply]
  simp only [Matrix.map_zero _ (map_zero h.bar), transpose_zero, Matrix.zero_mul,
    Matrix.mul_zero, add_zero, zero_add, Matrix.mul_one]
  constructor
  · intro e
    exact (fromBlocks_inj.1 e).2.1
  · intro e
    have e' : (G'.map h.bar)ᵀ * G = 1 := by
      have := congrArg (fun M => (M.map h.bar)ᵀ) e
      simp only [conjT_mul, conjT_conjT, Matrix.map_one _ (map_zero h.bar) (map_one h.bar),
        transpose_one] at this
      exact this
    rw [e, e']

theorem prPhi_conjT_mul {l : K} (hN : h.norm l = -1)
    (G G' : Matrix (Fin m) (Fin m) K) :
    ((prPhi m l G G').map h.bar)ᵀ * prPhi m l G G' = ((prWi m l).map h.bar)ᵀ *
      (((prFin K m (fromBlocks G 0 0 G')).map h.bar)ᵀ *
        ((2 : K) • prFin K m (fromBlocks 0 1 1 0)) * prFin K m (fromBlocks G 0 0 G')) *
      prWi m l := by
  rw [prPhi, conjT_mul, conjT_mul, ← prW_gram h hN]
  simp only [Matrix.mul_assoc]

theorem prPhi_unitary_iff (h2 : (2 : K) ≠ 0) {l : K} (hl : l ≠ 0) (hN : h.norm l = -1)
    (G G' : Matrix (Fin m) (Fin m) K) :
    ((prPhi m l G G').map h.bar)ᵀ * prPhi m l G G' = 1 ↔ (G.map h.bar)ᵀ * G' = 1 := by
  rw [← diag_gram_iff h G G', prPhi_conjT_mul h hN]
  have hWW : ((prW m l).map h.bar)ᵀ * ((prWi m l).map h.bar)ᵀ = 1 := by
    rw [← conjT_mul, prWi_mul_prW h2 hl, Matrix.map_one _ (map_zero h.bar) (map_one h.bar),
      transpose_one]
  have hWW' : ((prWi m l).map h.bar)ᵀ * ((prW m l).map h.bar)ᵀ = 1 := mul_eq_one_comm.1 hWW
  set X := prFin K m (fromBlocks G 0 0 G') with hX
  set C₀ := prFin K m (fromBlocks (0 : Matrix (Fin m) (Fin m) K) 1 1 0) with hC₀
  rw [Matrix.mul_smul, Matrix.smul_mul]
  constructor
  · intro e
    have e2 : (2 : K) • ((X.map h.bar)ᵀ * C₀ * X) = (2 : K) • C₀ := by
      calc (2 : K) • ((X.map h.bar)ᵀ * C₀ * X) =
          ((prW m l).map h.bar)ᵀ * (((prWi m l).map h.bar)ᵀ *
            ((2 : K) • ((X.map h.bar)ᵀ * C₀ * X)) * prWi m l) * prW m l := by
            simp only [← Matrix.mul_assoc, hWW, Matrix.one_mul]
            rw [Matrix.mul_assoc _ (prWi m l), prWi_mul_prW h2 hl, Matrix.mul_one]
        _ = ((prW m l).map h.bar)ᵀ * prW m l := by rw [e, Matrix.mul_one]
        _ = (2 : K) • C₀ := prW_gram h hN
    have := congrArg (fun M => (2 : K)⁻¹ • M) e2
    simp only [smul_smul, inv_mul_cancel₀ h2, one_smul] at this
    exact this
  · intro e
    rw [show (X.map h.bar)ᵀ * C₀ * X = C₀ from e]
    calc ((prWi m l).map h.bar)ᵀ * ((2 : K) • C₀) * prWi m l =
        ((prWi m l).map h.bar)ᵀ * (((prW m l).map h.bar)ᵀ * prW m l) * prWi m l := by
          rw [prW_gram h hN]
      _ = 1 := by
          rw [← Matrix.mul_assoc, hWW', Matrix.one_mul, prW_mul_prWi h2 hl]

end Unitary

end CFSG.ComponentClassification.Burgoyne.U
