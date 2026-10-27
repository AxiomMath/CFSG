module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4NoPSpUAlt
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4TBlocks

public noncomputable section

namespace CFSG.ComponentClassification.GSThmB

namespace Catalog7L4EU

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ComponentClassification.CatFactsL4U4 CFSG.LinearGroups
open CFSG.ComponentClassification.CatFactsL4U4.UnitaryOut (uStar uStar_mul uStar_one)
open CFSG.ComponentClassification.CatFactsL4U4.UnitaryConj (stdG exists_dual_pair uStar_mul_apply)
open CFSG.ComponentClassification.CatFactsL4U4.HBlocks (X1 blk IsBD ul lr)
open CFSG.ComponentClassification.CatFactsL4U4.TBlocks (bd)

variable {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K)

theorem exists_hyperbolic_basis_of_eigen (V₁ V₂ : Submodule K (Fin 4 → K))
    (hd1 : Module.finrank K V₁ = 2) (hd2 : Module.finrank K V₂ = 2)
    (hiso1 : ∀ v ∈ V₁, ∀ w ∈ V₁, stdHermForm h 4 v w = 0)
    (hiso2 : ∀ v ∈ V₂, ∀ w ∈ V₂, stdHermForm h 4 v w = 0)
    (hpair : ∀ w ∈ V₂, (∀ v ∈ V₁, stdHermForm h 4 v w = 0) → w = 0)
    {M : Matrix (Fin 4) (Fin 4) K} {l : K} (heig1 : ∀ v ∈ V₁, M *ᵥ v = l • v)
    (heig2 : ∀ w ∈ V₂, M *ᵥ w = -l • w) :
    ∃ Q : Matrix (Fin 4) (Fin 4) K, uStar h Q * Q = stdG ∧ M * Q = Q * X1 l := by
  classical
  obtain ⟨e, g, he, hg, hdual⟩ := exists_dual_pair h V₁ V₂ hd1 hd2 hpair
  set col : Fin 4 → Fin 4 → K := ![e 0, e 1, g 0, g 1] with hcol
  set Q : Matrix (Fin 4) (Fin 4) K := Matrix.of fun i j => col j i with hQ
  have hQcol : ∀ j, (fun k => Q k j) = col j := fun j => rfl
  refine ⟨Q, ?_, ?_⟩
  · ext a b
    rw [uStar_mul_apply, hQcol, hQcol]
    have hge : ∀ a b, stdHermForm h 4 (g a) (e b) = if a = b then 1 else 0 := by
      intro a b
      rw [← (stdHermForm_isSymm h 4).eq, hdual]
      by_cases hab : b = a
      · subst hab; simp
      · simp [hab, Ne.symm hab]
    have hee : ∀ a b, stdHermForm h 4 (e a) (e b) = 0 := fun a b => hiso1 _ (he a) _ (he b)
    have hgg : ∀ a b, stdHermForm h 4 (g a) (g b) = 0 := fun a b => hiso2 _ (hg a) _ (hg b)
    fin_cases a <;> fin_cases b <;> simp [hcol, stdG, hdual, hge, hee, hgg]
  · ext i j
    rw [Matrix.mul_apply, Matrix.mul_apply]
    change (M *ᵥ col j) i = _
    fin_cases j <;> simp [hcol, X1, hQ, heig1 _ (he _), heig2 _ (hg _), Fin.sum_univ_four,
      mul_comm]

omit h in
theorem stdG_mul_stdG : (stdG : Matrix (Fin 4) (Fin 4) K) * stdG = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [stdG, Matrix.mul_apply, Fin.sum_univ_four]

omit h in
theorem transpose_stdG : (stdG : Matrix (Fin 4) (Fin 4) K)ᵀ = stdG := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [stdG]

theorem map_stdG : (stdG : Matrix (Fin 4) (Fin 4) K).map h.bar = stdG := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [stdG]

theorem uStar_stdG : uStar h (stdG : Matrix (Fin 4) (Fin 4) K) = stdG := by
  rw [uStar, map_stdG, transpose_stdG]

theorem map_map_bar (M : Matrix (Fin 4) (Fin 4) K) : (M.map h.bar).map h.bar = M := by
  ext i j
  simp [h.bar_bar]

variable {h}

theorem mul_stdG_mul_uStar {Q : Matrix (Fin 4) (Fin 4) K} (hQ : uStar h Q * Q = stdG) :
    Q * stdG * uStar h Q = 1 := by
  have h1 : (stdG * uStar h Q) * Q = 1 := by rw [Matrix.mul_assoc, hQ, stdG_mul_stdG]
  have h2 := mul_eq_one_comm.mp h1
  rwa [← Matrix.mul_assoc] at h2

theorem bar_mul_stdG_mul_transpose {Q : Matrix (Fin 4) (Fin 4) K} (hQ : uStar h Q * Q = stdG) :
    Q.map h.bar * stdG * Qᵀ = 1 := by
  have h1 := congrArg (fun M => M.map h.bar) (mul_stdG_mul_uStar hQ)
  simp only [Matrix.map_mul, map_stdG, uStar, Matrix.map_one _ (map_zero h.bar)
    (map_one h.bar)] at h1
  rwa [Matrix.transpose_map, map_map_bar] at h1

theorem transpose_mul_bar {Q : Matrix (Fin 4) (Fin 4) K} (hQ : uStar h Q * Q = stdG) :
    Qᵀ * Q.map h.bar = stdG := by
  have h1 := congrArg Matrix.transpose hQ
  rwa [Matrix.transpose_mul, uStar, Matrix.transpose_transpose, transpose_stdG] at h1

theorem stdG_transpose_bar {Q Y Z : Matrix (Fin 4) (Fin 4) K} (hQ : uStar h Q * Q = stdG)
    (hYZ : Y * Q = Q * Z) : stdG * Qᵀ * Y.map h.bar = Z.map h.bar * stdG * Qᵀ := by
  have h1 := congrArg (fun M => M.map h.bar) hYZ
  simp only [Matrix.map_mul] at h1
  have hb := bar_mul_stdG_mul_transpose hQ
  have ht := transpose_mul_bar hQ
  calc stdG * Qᵀ * Y.map h.bar = stdG * Qᵀ * Y.map h.bar * (Q.map h.bar * stdG * Qᵀ) := by
        rw [hb, Matrix.mul_one]
    _ = stdG * Qᵀ * (Y.map h.bar * Q.map h.bar) * stdG * Qᵀ := by simp only [Matrix.mul_assoc]
    _ = stdG * (Qᵀ * Q.map h.bar) * Z.map h.bar * stdG * Qᵀ := by
        rw [h1]; simp only [Matrix.mul_assoc]
    _ = Z.map h.bar * stdG * Qᵀ := by
        rw [ht, stdG_mul_stdG, Matrix.one_mul]

variable (h)

@[expose] def swapN (c : K) : Matrix (Fin 4) (Fin 4) K := blk 0 c (h.bar c)⁻¹ 0

theorem swapN_unitary {c : K} (hc : c ≠ 0) : uStar h (swapN h c) * stdG * swapN h c = stdG := by
  have hb : h.bar c ≠ 0 := fun h0 => hc ((map_eq_zero h.bar).1 h0)
  have hbb : h.bar (h.bar c)⁻¹ = c⁻¹ := by rw [map_inv₀, h.bar_bar]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [swapN, blk, uStar, stdG, Matrix.mul_apply, Fin.sum_univ_four, hbb, hc, hb]

theorem swapN_mul_bar {c : K} (hc : c ≠ 0) : swapN h c * (swapN h c).map h.bar = -1 := by
  have hb : h.bar c ≠ 0 := fun h0 => hc ((map_eq_zero h.bar).1 h0)
  have hbb : h.bar (h.bar c)⁻¹ = c⁻¹ := by rw [map_inv₀, h.bar_bar]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [swapN, blk, Matrix.mul_apply, Fin.sum_univ_four, hbb, hc, hb]

theorem swapN_X1 (c : K) {l : K} (hl : l ≠ 0) :
    swapN h c * (X1 l).map h.bar = (-(h.bar l) / l) • (X1 l * swapN h c) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [swapN, blk, X1, Matrix.mul_apply, Fin.sum_univ_four] <;> field_simp

theorem eq_smul_adjugate {k k' : Matrix (Fin 2) (Fin 2) K} (hkk : uStar h k * k' = 1)
    (hdet : k.det = 1 ∨ k.det = -1) : k' = k.det • adjugate (uStar h k) := by
  have hbd : (uStar h k).det = k.det := by
    rw [uStar, det_transpose, show k.map h.bar = h.bar.mapMatrix k from rfl, ← RingHom.map_det]
    rcases hdet with hd | hd <;> rw [hd] <;> simp
  have h1 : adjugate (uStar h k) * (uStar h k * k') = adjugate (uStar h k) := by
    rw [hkk, Matrix.mul_one]
  rw [← Matrix.mul_assoc, adjugate_mul, hbd, Matrix.smul_mul, Matrix.one_mul] at h1
  have hdd : k.det * k.det = 1 := by rcases hdet with hd | hd <;> rw [hd] <;> ring
  calc k' = (k.det * k.det) • k' := by rw [hdd, one_smul]
    _ = k.det • adjugate (uStar h k) := by rw [← smul_smul, h1]

theorem swapN_bd (c : K) {k k' : Matrix (Fin 2) (Fin 2) K}
    (hkk : uStar h k * k' = 1) (hdet : k.det = 1 ∨ k.det = -1) :
    swapN h c * (bd k k').map h.bar = k.det • (bd k k' * swapN h c) := by
  have hk' := eq_smul_adjugate h hkk hdet
  have hdb : h.bar k.det = k.det := by rcases hdet with hd | hd <;> rw [hd] <;> simp
  have hdd : k.det * k.det = 1 := by rcases hdet with hd | hd <;> rw [hd] <;> ring
  rw [hk']
  generalize k.det = δ at hdb hdd ⊢
  obtain ⟨a, b, c₁, d₁, rfl⟩ : ∃ a b c₁ d₁ : K, k = !![a, b; c₁, d₁] :=
    ⟨_, _, _, _, Matrix.eta_fin_two k⟩
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [swapN, blk, bd, uStar, adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_four, hdb,
      h.bar_bar] <;>
    first
      | ring1
      | linear_combination (-(h.bar c)⁻¹ * h.bar c₁) * hdd
      | linear_combination (-(h.bar c)⁻¹ * h.bar d₁) * hdd
      | linear_combination ((h.bar c)⁻¹ * h.bar a) * hdd
      | linear_combination ((h.bar c)⁻¹ * h.bar b) * hdd
      | linear_combination ((h.bar c)⁻¹ * h.bar c₁) * hdd
      | linear_combination ((h.bar c)⁻¹ * h.bar d₁) * hdd
      | linear_combination (-(h.bar c)⁻¹ * h.bar a) * hdd
      | linear_combination (-(h.bar c)⁻¹ * h.bar b) * hdd

theorem det_swapN (c : K) : (swapN h c).det = (c * (h.bar c)⁻¹) ^ 2 := by
  rw [Matrix.det_succ_row_zero]
  simp [swapN, blk, Fin.sum_univ_succ, Matrix.det_succ_row_zero, Matrix.submatrix, Fin.succAbove]
  ring

@[expose] def gtMat (t : K) : Matrix (Fin 4) (Fin 4) K := bd !![t, 0; 0, 1] !![t⁻¹, 0; 0, 1]

theorem gtMat_unitary {t : K} (ht : t ≠ 0) (htb : h.bar t = t) :
    uStar h (gtMat t) * stdG * gtMat t = stdG := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [gtMat, bd, uStar, stdG, Matrix.mul_apply, Fin.sum_univ_four, htb, ht]

omit [Field K] in
theorem det_gtMat {t : K} [Field K] (ht : t ≠ 0) : (gtMat t).det = 1 := by
  rw [gtMat, TBlocks.det_bd, det_fin_two_of, det_fin_two_of]
  field_simp
  ring

theorem gtMat_X1 (t l : K) : gtMat t * X1 l = X1 l * gtMat t := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [gtMat, bd, X1, Matrix.mul_apply, Fin.sum_univ_four] <;>
    ring

theorem swapN_gtMat_ne {c : K} (hc : c ≠ 0) {t : K} (ht : t ≠ 0) (htb : h.bar t = t)
    (ht2 : t ^ 2 ≠ 1) (s : K) : swapN h c * (gtMat t).map h.bar ≠ s • (gtMat t * swapN h c) := by
  intro he
  have e12 := congrFun (congrFun he 1) 2
  have e21 := congrFun (congrFun he 2) 1
  simp [swapN, blk, gtMat, bd, Matrix.mul_apply, Fin.sum_univ_four, htb] at e12 e21
  have hb : h.bar c ≠ 0 := fun h0 => hc ((map_eq_zero h.bar).1 h0)
  have hs' : s = t⁻¹ := by
    have : (s - t⁻¹) * c = 0 := by linear_combination -e12
    exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_right hc)
  have hs'' : s * t⁻¹ = 1 := by
    have hbi : (h.bar c)⁻¹ ≠ 0 := inv_ne_zero hb
    have : (s * t⁻¹ - 1) * (h.bar c)⁻¹ = 0 := by linear_combination -e21
    exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_right hbi)
  apply ht2
  rw [hs'] at hs''
  field_simp at hs''
  first | linear_combination hs'' | linear_combination -hs''

@[expose] def swapM (Q : Matrix (Fin 4) (Fin 4) K) (c : K) : Matrix (Fin 4) (Fin 4) K :=
  Q * swapN h c * stdG * Qᵀ

variable {h}

theorem swapM_unitary {Q : Matrix (Fin 4) (Fin 4) K} (hQ : uStar h Q * Q = stdG) {c : K}
    (hc : c ≠ 0) : uStar h (swapM h Q c) * swapM h Q c = 1 := by
  have hN := swapN_unitary h hc
  have hb := bar_mul_stdG_mul_transpose hQ
  have hu : uStar h (swapM h Q c) = Q.map h.bar * stdG * uStar h (swapN h c) * uStar h Q := by
    rw [swapM, uStar_mul, uStar_mul, uStar_mul, uStar_stdG]
    simp only [uStar, Matrix.transpose_transpose, Matrix.transpose_map, Matrix.mul_assoc]
  rw [hu, swapM]
  calc Q.map h.bar * stdG * uStar h (swapN h c) * uStar h Q * (Q * swapN h c * stdG * Qᵀ) =
      Q.map h.bar * stdG * (uStar h (swapN h c) * (uStar h Q * Q) * swapN h c) * stdG * Qᵀ := by
        simp only [Matrix.mul_assoc]
    _ = Q.map h.bar * stdG * stdG * stdG * Qᵀ := by rw [hQ, hN]
    _ = 1 := by
        rw [Matrix.mul_assoc (Q.map h.bar) stdG stdG, stdG_mul_stdG, Matrix.mul_one, hb]

theorem swapM_mul_bar {Q : Matrix (Fin 4) (Fin 4) K} (hQ : uStar h Q * Q = stdG) {c : K}
    (hc : c ≠ 0) : swapM h Q c * (swapM h Q c).map h.bar = -1 := by
  have ht := transpose_mul_bar hQ
  have hN := swapN_mul_bar h hc
  have h1 := mul_stdG_mul_uStar hQ
  have hm : (swapM h Q c).map h.bar = Q.map h.bar * (swapN h c).map h.bar * stdG * uStar h Q := by
    rw [swapM]
    simp only [Matrix.map_mul, map_stdG, uStar, Matrix.transpose_map]
  rw [hm, swapM]
  calc Q * swapN h c * stdG * Qᵀ * (Q.map h.bar * (swapN h c).map h.bar * stdG * uStar h Q) =
      Q * swapN h c * stdG * (Qᵀ * Q.map h.bar) * (swapN h c).map h.bar * stdG * uStar h Q := by
        simp only [Matrix.mul_assoc]
    _ = Q * (swapN h c * (swapN h c).map h.bar) * stdG * uStar h Q := by
        rw [ht]
        simp only [Matrix.mul_assoc]
        rw [← Matrix.mul_assoc stdG stdG, stdG_mul_stdG, Matrix.one_mul]
    _ = -1 := by
        rw [hN, Matrix.mul_neg, Matrix.mul_one, Matrix.neg_mul, Matrix.neg_mul, h1]

theorem swapM_rel {Q : Matrix (Fin 4) (Fin 4) K} (hQ : uStar h Q * Q = stdG) {c : K}
    {Y Z : Matrix (Fin 4) (Fin 4) K} (hYZ : Y * Q = Q * Z) {s : K}
    (hs : swapN h c * Z.map h.bar = s • (Z * swapN h c)) :
    swapM h Q c * Y.map h.bar = s • (Y * swapM h Q c) := by
  have h1 := stdG_transpose_bar hQ hYZ
  rw [swapM]
  calc Q * swapN h c * stdG * Qᵀ * Y.map h.bar = Q * swapN h c * (stdG * Qᵀ * Y.map h.bar) := by
        simp only [Matrix.mul_assoc]
    _ = Q * (swapN h c * Z.map h.bar) * stdG * Qᵀ := by rw [h1]; simp only [Matrix.mul_assoc]
    _ = s • (Q * Z * swapN h c * stdG * Qᵀ) := by
        rw [hs, Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_mul]
        simp only [Matrix.mul_assoc]
    _ = s • (Y * (Q * swapN h c * stdG * Qᵀ)) := by
        rw [← hYZ]; simp only [Matrix.mul_assoc]

theorem swapN_rel_of_swapM {Q : Matrix (Fin 4) (Fin 4) K} (hQ : uStar h Q * Q = stdG) {c : K}
    {Y Z : Matrix (Fin 4) (Fin 4) K} (hYZ : Y * Q = Q * Z) {s : K}
    (hs : swapM h Q c * Y.map h.bar = s • (Y * swapM h Q c)) :
    swapN h c * Z.map h.bar = s • (Z * swapN h c) := by
  have h1 := stdG_transpose_bar hQ hYZ
  have hQi : stdG * uStar h Q * Q = 1 := by rw [Matrix.mul_assoc, hQ, stdG_mul_stdG]
  have hb := bar_mul_stdG_mul_transpose hQ
  have hZ : Z = stdG * uStar h Q * Y * Q := by
    rw [Matrix.mul_assoc _ Y Q, hYZ, ← Matrix.mul_assoc, hQi, Matrix.one_mul]
  have e := congrArg (fun M => stdG * uStar h Q * M * Q.map h.bar) hs
  rw [swapM] at e
  have lhs : stdG * uStar h Q * (Q * swapN h c * stdG * Qᵀ * Y.map h.bar) * Q.map h.bar =
      swapN h c * Z.map h.bar := by
    calc stdG * uStar h Q * (Q * swapN h c * stdG * Qᵀ * Y.map h.bar) * Q.map h.bar =
        (stdG * uStar h Q * Q) * swapN h c * (stdG * Qᵀ * Y.map h.bar) * Q.map h.bar := by
          simp only [Matrix.mul_assoc]
      _ = swapN h c * Z.map h.bar * (stdG * Qᵀ * Q.map h.bar) := by
          rw [hQi, Matrix.one_mul, h1]; simp only [Matrix.mul_assoc]
      _ = swapN h c * Z.map h.bar := by
          rw [Matrix.mul_assoc stdG, transpose_mul_bar hQ, stdG_mul_stdG, Matrix.mul_one]
  have rhs : stdG * uStar h Q * (s • (Y * (Q * swapN h c * stdG * Qᵀ))) * Q.map h.bar =
      s • (Z * swapN h c) := by
    rw [Matrix.mul_smul, Matrix.smul_mul]
    congr 1
    calc stdG * uStar h Q * (Y * (Q * swapN h c * stdG * Qᵀ)) * Q.map h.bar =
        (stdG * uStar h Q * Y * Q) * swapN h c * (stdG * (Qᵀ * Q.map h.bar)) := by
          simp only [Matrix.mul_assoc]
      _ = Z * swapN h c := by
          rw [← hZ, transpose_mul_bar hQ, stdG_mul_stdG, Matrix.mul_one]
  rw [lhs, rhs] at e
  exact e

theorem det_swapM {Q : Matrix (Fin 4) (Fin 4) K} (c : K) :
    (swapM h Q c).det = (Q.det * (c * (h.bar c)⁻¹)) ^ 2 := by
  rw [swapM, det_mul, det_mul, det_mul, det_transpose, det_swapN,
    show (stdG : Matrix (Fin 4) (Fin 4) K).det = 1 from UnitaryConj.det_stdG]
  ring

end Catalog7L4EU

end CFSG.ComponentClassification.GSThmB
