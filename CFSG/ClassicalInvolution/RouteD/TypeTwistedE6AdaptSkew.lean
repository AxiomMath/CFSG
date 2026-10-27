module

public import CFSG.ClassicalInvolution.RouteD.TypeTwistedE6AdaptBar

public section

namespace CFSG.ClassicalInvolution.RouteD.NonClassical

open Matrix CFSG.Open CFSG.ClassicalGroups.Unitary CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Phan CFSG.ClassicalInvolution.Models CFSG.LieType.Universal.Unitary
  CFSG.ClassicalInvolution.ModelFacts.UnitaryAut CFSG.ClassicalInvolution.RouteD
  CFSG.ClassicalInvolution.RouteD.Exotic Module
open CFSG.LieType.BorelTits (unitaryInvolution unitaryInvolution_apply)
open scoped MatrixGroups

variable {p f : ℕ} [Fact p.Prime]

section Skew

theorem skew_block_comm {K : Type} [Field K] (σ : K ≃+* K) (Gm : Matrix (Fin 6) (Fin 6) K)
    (hGb : ∀ i j : Fin 6, (i.val < 2 ↔ ¬ j.val < 2) → Gm i j = 0)
    (b : K) (h00 : Gm 0 0 = 0) (h01 : Gm 0 1 = b) (h10 : Gm 1 0 = -b) (h11 : Gm 1 1 = 0)
    (X : Matrix (Fin 2) (Fin 2) K)
    (h00' : σ (X 0 0) = X 1 1) (h01' : σ (X 0 1) = -X 1 0) (h10' : σ (X 1 0) = -X 0 1)
    (h11' : σ (X 1 1) = X 0 0) :
    Gm * σ.mapMatrix (blockMat 6 0 X) = blockMat 6 0 X * Gm := by
  have z02 : Gm 0 2 = 0 := hGb 0 2 (by decide)
  have z20 : Gm 2 0 = 0 := hGb 2 0 (by decide)
  have z03 : Gm 0 3 = 0 := hGb 0 3 (by decide)
  have z30 : Gm 3 0 = 0 := hGb 3 0 (by decide)
  have z04 : Gm 0 4 = 0 := hGb 0 4 (by decide)
  have z40 : Gm 4 0 = 0 := hGb 4 0 (by decide)
  have z05 : Gm 0 5 = 0 := hGb 0 5 (by decide)
  have z50 : Gm 5 0 = 0 := hGb 5 0 (by decide)
  have z12 : Gm 1 2 = 0 := hGb 1 2 (by decide)
  have z21 : Gm 2 1 = 0 := hGb 2 1 (by decide)
  have z13 : Gm 1 3 = 0 := hGb 1 3 (by decide)
  have z31 : Gm 3 1 = 0 := hGb 3 1 (by decide)
  have z14 : Gm 1 4 = 0 := hGb 1 4 (by decide)
  have z41 : Gm 4 1 = 0 := hGb 4 1 (by decide)
  have z15 : Gm 1 5 = 0 := hGb 1 5 (by decide)
  have z51 : Gm 5 1 = 0 := hGb 5 1 (by decide)
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_succ, blockMat_apply, RingEquiv.mapMatrix_apply,
      Matrix.one_apply, h00, h01, h10, h11, h00', h01', h10', h11', z02, z20, z03, z30, z04, z40,
      z05, z50, z12, z21, z13, z31, z14, z41, z15, z51] <;> ring

theorem su2_entries {K : Type} [Field K] (σ : K ≃+* K) (X : Matrix (Fin 2) (Fin 2) K)
    (hu : conjTr σ X * X = 1) (hd : X.det = 1) :
    σ (X 0 0) = X 1 1 ∧ σ (X 0 1) = -X 1 0 ∧ σ (X 1 0) = -X 0 1 ∧ σ (X 1 1) = X 0 0 := by
  have h1 : X * Matrix.adjugate X = 1 := by rw [Matrix.mul_adjugate, hd, one_smul]
  have h2 : conjTr σ X = Matrix.adjugate X := left_inv_eq_right_inv hu h1
  rw [Matrix.adjugate_fin_two] at h2
  have e00 := congrFun (congrFun h2 0) 0
  have e01 := congrFun (congrFun h2 0) 1
  have e10 := congrFun (congrFun h2 1) 0
  have e11 := congrFun (congrFun h2 1) 1
  simp [conjTr] at e00 e01 e10 e11
  exact ⟨e00, e10, e01, e11⟩

theorem suMat_te6Inv_eq : suMat (te6Inv p f) =
    Matrix.diagonal (fun r : Fin 6 => if r.val < 2 then (-1 : GaloisField p (2 * f)) else 1) := by
  show zMat (GaloisField p (2 * f)) (5 + 1) (nodePair 5 0 (by norm_num)).1 = _
  have hmem : ∀ r : Fin (5 + 1), r ∈ (nodePair 5 0 (by norm_num)).1 ↔ r.val < 2 := by
    intro r
    simp only [nodePair, natPair, Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff]
    omega
  rw [zMat]
  congr 1
  funext r
  simp only [hmem]

theorem te6Node_eq_rootSU2 (hp2 : p ≠ 2) :
    te6Node p f = rootSU2 (GaloisField p (2 * f)) p f (by norm_num : 2 ≤ 5 + 1) := by
  have h2 : (2 : GaloisField p (2 * f)) ≠ 0 := two_ne_zero_te6 hp2
  rw [rootSU2_eq_longRootGroupSU h2]
  show longRootGroupSU (GaloisField p (2 * f)) p f
      (zMat (GaloisField p (2 * f)) (5 + 1) (nodePair 5 0 (by norm_num)).1) = _
  congr 1
  rw [negBlock_eq_diagonal]
  have hmem : ∀ r : Fin (5 + 1), r ∈ (nodePair 5 0 (by norm_num)).1 ↔ r.val < 2 := by
    intro r
    simp only [nodePair, natPair, Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff]
    omega
  rw [zMat]
  congr 1
  funext r
  simp only [hmem, zero_le, true_and]

theorem alpha_fixes_te6Node_of_skew (hp2 : p ≠ 2)
    {g : GL (Fin 6) (GaloisField p (2 * f))}
    {α : Su (GaloisField p (2 * f)) p f 6 →* Su (GaloisField p (2 * f)) p f 6}
    (hmat : ∀ x : Su (GaloisField p (2 * f)) p f 6,
      ((α x : GL (Fin 6) (GaloisField p (2 * f))) :
        Matrix (Fin 6) (Fin 6) (GaloisField p (2 * f))) =
        (g : Matrix (Fin 6) (Fin 6) (GaloisField p (2 * f))) *
          (unitaryInvolution (GaloisField p (2 * f)) p f).mapMatrix
            ((x : GL (Fin 6) (GaloisField p (2 * f))) :
              Matrix (Fin 6) (Fin 6) (GaloisField p (2 * f))) *
          ((g⁻¹ : GL (Fin 6) (GaloisField p (2 * f))) :
            Matrix (Fin 6) (Fin 6) (GaloisField p (2 * f))))
    (hiso : conjTr (unitaryInvolution (GaloisField p (2 * f)) p f)
      (g : Matrix (Fin 6) (Fin 6) (GaloisField p (2 * f))) *
        (g : Matrix (Fin 6) (Fin 6) (GaloisField p (2 * f))) = 1)
    (hμ : (g : Matrix (Fin 6) (Fin 6) (GaloisField p (2 * f))) *
      (unitaryInvolution (GaloisField p (2 * f)) p f).mapMatrix
        (g : Matrix (Fin 6) (Fin 6) (GaloisField p (2 * f))) =
          (-1 : GaloisField p (2 * f)) • (1 : Matrix (Fin 6) (Fin 6) (GaloisField p (2 * f))))
    (hW : (g : Matrix (Fin 6) (Fin 6) (GaloisField p (2 * f))) * suMat (te6Inv p f) =
      suMat (te6Inv p f) * (g : Matrix (Fin 6) (Fin 6) (GaloisField p (2 * f)))) :
    ∀ x ∈ te6Node p f, α x = x := by
  have h2 : (2 : GaloisField p (2 * f)) ≠ 0 := two_ne_zero_te6 hp2
  set σ := unitaryInvolution (GaloisField p (2 * f)) p f with hσdef
  set Gm : Matrix (Fin 6) (Fin 6) (GaloisField p (2 * f)) :=
    ((g : GL (Fin 6) (GaloisField p (2 * f))) : Matrix (Fin 6) (Fin 6) (GaloisField p (2 * f)))
    with hGm
  set Gi : Matrix (Fin 6) (Fin 6) (GaloisField p (2 * f)) :=
    ((g⁻¹ : GL (Fin 6) (GaloisField p (2 * f))) :
      Matrix (Fin 6) (Fin 6) (GaloisField p (2 * f))) with hGi
  have hGGi : Gm * Gi = 1 := by rw [hGi, hGm, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hGb : ∀ i j : Fin 6, (i.val < 2 ↔ ¬ j.val < 2) → Gm i j = 0 := by
    intro i j hij
    have e := congrFun (congrFun hW i) j
    rw [suMat_te6Inv_eq, Matrix.mul_diagonal, Matrix.diagonal_mul] at e
    have hne : (if j.val < 2 then (-1 : GaloisField p (2 * f)) else 1) -
        (if i.val < 2 then (-1 : GaloisField p (2 * f)) else 1) ≠ 0 := by
      by_cases hi : i.val < 2
      · have hj : ¬ j.val < 2 := hij.mp hi
        simp only [hi, hj, ite_true, ite_false]
        intro h
        apply h2
        linear_combination h
      · have hj : j.val < 2 := by
          by_contra hj
          exact hi (hij.mpr hj)
        simp only [hi, hj, ite_true, ite_false]
        intro h
        apply h2
        linear_combination -h
    have : Gm i j * ((if j.val < 2 then (-1 : GaloisField p (2 * f)) else 1) -
        (if i.val < 2 then (-1 : GaloisField p (2 * f)) else 1)) = 0 := by
      linear_combination e
    exact (mul_eq_zero.mp this).resolve_right hne
  have hskew : ∀ i j : Fin 6, Gm i j = -Gm j i := by
    set S : Matrix (Fin 6) (Fin 6) (GaloisField p (2 * f)) := σ.mapMatrix Gm with hS
    have hiso' : Sᵀ * Gm = 1 := hiso
    have hS' : S = -Sᵀ := by
      calc S = (Sᵀ * Gm) * S := by rw [hiso', Matrix.one_mul]
        _ = Sᵀ * (Gm * S) := by rw [Matrix.mul_assoc]
        _ = -Sᵀ := by rw [hμ, Matrix.mul_smul, Matrix.mul_one, neg_one_smul]
    intro i j
    have e := congrFun (congrFun hS' i) j
    simp only [hS, RingEquiv.mapMatrix_apply, Matrix.map_apply, Matrix.neg_apply,
      Matrix.transpose_apply] at e
    exact σ.injective (by rw [e, map_neg] : σ (Gm i j) = σ (-Gm j i))
  have h00 : Gm 0 0 = 0 := by
    have := hskew 0 0
    have h3 : (2 : GaloisField p (2 * f)) * Gm 0 0 = 0 := by linear_combination this
    exact (mul_eq_zero.mp h3).resolve_left h2
  have h11 : Gm 1 1 = 0 := by
    have := hskew 1 1
    have h3 : (2 : GaloisField p (2 * f)) * Gm 1 1 = 0 := by linear_combination this
    exact (mul_eq_zero.mp h3).resolve_left h2
  intro x hx
  rw [te6Node_eq_rootSU2 hp2] at hx
  obtain ⟨A, rfl⟩ := hx
  set X : Matrix (Fin 2) (Fin 2) (GaloisField p (2 * f)) := suMat A with hX
  obtain ⟨h00', h01', h10', h11'⟩ := su2_entries σ X A.2.2
    (by rw [hX]; exact det_suMat A)
  have hcomm := skew_block_comm σ Gm hGb (Gm 0 1) h00 rfl (by rw [hskew 1 0]) h11 X h00' h01'
    h10' h11'
  refine Subtype.ext (Units.ext ?_)
  rw [hmat]
  have hs : ((blockEmb (GaloisField p (2 * f)) p f 6 2 0 (by omega) A : Su _ p f 6) :
      GL (Fin 6) (GaloisField p (2 * f))) = blockMat 6 0 X := rfl
  rw [hs]
  calc Gm * (unitaryInvolution (GaloisField p (2 * f)) p f).mapMatrix (blockMat 6 0 X) * Gi
      = (Gm * σ.mapMatrix (blockMat 6 0 X)) * Gi := rfl
    _ = (blockMat 6 0 X * Gm) * Gi := by rw [hcomm]
    _ = blockMat 6 0 X := by rw [Matrix.mul_assoc, hGGi, Matrix.mul_one]

end Skew

end CFSG.ClassicalInvolution.RouteD.NonClassical
