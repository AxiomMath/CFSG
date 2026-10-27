module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KS.E8FiveOneSL5
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KS.E8FiveOneEig
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KS.E8FiveOneInner
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.LieType.SeitzGeneration.SubfieldPairSUPhan
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ

namespace KSE8Five

namespace One

open CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.SeitzExcOpenRest4Griess
open CFSG.HardMathSupport.Timmesfeld.Torality CFSG.RankThree.PartOne.KE
open scoped MatrixGroups Fin.NatCast

section Swap

variable {K : Type} [Field K]

theorem swap_matrix {ω : K} (hω : IsPrimitiveRoot ω 5)
    (d : Fin 5 → Kˣ) (hd : ∏ i, (d i : K) = 1) (c : Kˣ) (s : Fin 5) (du : Fin 5 → Kˣ)
    (hdu : ∀ i, (du i : K) = c * ω ^ ((s : ℕ) * (i : ℕ))) :
    ∃ (g : SL(5, K)) (δ : Fin 5 → Kˣ) (hδ : ∏ i, (δ i : K) = 1) (r : Fin 5 → Kˣ)
      (hr : ∏ i, (r i : K) = 1),
      g⁻¹ * (diagSLn d hd * coxSL5) * g = diagSLn δ hδ ∧
      conjDiagn (fun i => (du i)⁻¹) g⁻¹ * g = rotSL ^ (s : ℕ) * diagSLn r hr := by
  classical
  have hω5 : ω ^ 5 = 1 := hω.pow_eq_one
  have hω0 : ω ≠ 0 := hω.ne_zero (by norm_num)
  set a : Fin 5 → K := fun j => (d (j + 1) : K) * (![-1, -1, -1, -1, 1] : Fin 5 → K) j with ha_def
  have hM : ((diagSLn d hd * coxSL5 : SL(5, K)) : Matrix (Fin 5) (Fin 5) K) = cycMat5 a := by
    rw [Matrix.SpecialLinearGroup.coe_mul, coe_diagSLn, coe_coxSL5, diagonal_mul_cycMat5]
  have hd5 : (d 0 : K) * d 1 * d 2 * d 3 * d 4 = 1 := by
    simpa [Fin.prod_univ_five] using hd
  have ha : a 0 * a 1 * a 2 * a 3 * a 4 = 1 := by
    simp only [ha_def]
    have e0 : ((0 : Fin 5) + 1) = 1 := by decide
    have e1 : ((1 : Fin 5) + 1) = 2 := by decide
    have e2 : ((2 : Fin 5) + 1) = 3 := by decide
    have e3 : ((3 : Fin 5) + 1) = 4 := by decide
    have e4 : ((4 : Fin 5) + 1) = 0 := by decide
    rw [e0, e1, e2, e3, e4]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
    linear_combination hd5
  have ha0 : a 0 ≠ 0 := fun h => by simp [h] at ha
  have ha1 : a 1 ≠ 0 := fun h => by simp [h] at ha
  have ha2 : a 2 ≠ 0 := fun h => by simp [h] at ha
  have ha3 : a 3 ≠ 0 := fun h => by simp [h] at ha
  set Qe := cycEigen5 ω a with hQe
  have hMQ : cycMat5 a * Qe = Qe * Matrix.diagonal fun k : Fin 5 => ω ^ (5 - (k : ℕ)) :=
    cycMat5_mul_cycEigen5 hω5 ha
  have hVdet : (Matrix.vandermonde fun k : Fin 5 => ω ^ (k : ℕ)).det ≠ 0 := by
    refine Matrix.det_vandermonde_ne_zero_iff.2 fun i j hij => ?_
    exact Fin.ext (hω.pow_inj i.2 j.2 hij)
  have hQdet : Qe.det ≠ 0 := by
    rw [hQe, cycEigen5, Matrix.det_mul, Matrix.det_diagonal]
    refine mul_ne_zero ?_ hVdet
    simp [Fin.prod_univ_five, ha0, ha1, ha2, ha3]
  set t : K := (Qe.det)⁻¹ with ht
  have ht0 : t ≠ 0 := inv_ne_zero hQdet
  set tf : Fin 5 → K := fun i => if i = 0 then t else 1 with htf
  have htf0 : ∀ i, tf i ≠ 0 := fun i => by
    simp only [htf]
    split_ifs
    · exact ht0
    · exact one_ne_zero
  have hD0det : (Matrix.diagonal tf).det = t := by
    rw [Matrix.det_diagonal, Fin.prod_univ_five]
    simp [htf]
  have hgdet : (Qe * Matrix.diagonal tf).det = 1 := by
    rw [Matrix.det_mul, hD0det, ht, mul_inv_cancel₀ hQdet]
  obtain ⟨g, hg⟩ : ∃ g : SL(5, K), (g : Matrix (Fin 5) (Fin 5) K) = Qe * Matrix.diagonal tf :=
    ⟨⟨Qe * Matrix.diagonal tf, hgdet⟩, rfl⟩
  have hδ0 : ∀ k : Fin 5, ω ^ (5 - (k : ℕ)) ≠ 0 := fun k => pow_ne_zero _ hω0
  set δ : Fin 5 → Kˣ := fun k => Units.mk0 (ω ^ (5 - (k : ℕ))) (hδ0 k) with hδdef
  have hδ : ∏ i, (δ i : K) = 1 := by
    simp only [hδdef, Units.val_mk0, Fin.prod_univ_five]
    simp only [Fin.val_zero, Fin.val_one, Fin.val_two]
    have h4 : ((3 : Fin 5) : ℕ) = 3 := rfl
    have h5 : ((4 : Fin 5) : ℕ) = 4 := rfl
    rw [h4, h5]
    have : ω ^ (5 - 0) * ω ^ (5 - 1) * ω ^ (5 - 2) * ω ^ (5 - 3) * ω ^ (5 - 4) = (ω ^ 5) ^ 3 := by
      norm_num
      ring
    rw [this, hω5, one_pow]
  have hMg : (diagSLn d hd * coxSL5) * g = g * diagSLn δ hδ := by
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul, hM, Matrix.SpecialLinearGroup.coe_mul, hg,
      coe_diagSLn, ← Matrix.mul_assoc, hMQ, Matrix.mul_assoc, Matrix.mul_assoc,
      Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    congr 2
    funext i
    simp only [hδdef, Units.val_mk0]
    exact mul_comm _ _
  set Dm : Matrix (Fin 5) (Fin 5) K := Matrix.diagonal fun i => (du i : K) with hDm
  set Ps : Matrix (Fin 5) (Fin 5) K := Matrix.of (fun l k : Fin 5 => if l = k + s then 1 else 0)
    with hPs
  set rf : Fin 5 → K := fun k => tf k * (tf (k + s) * ω ^ ((s : ℕ) * ((k + s : Fin 5) : ℕ)))⁻¹
    with hrf
  have hDmQ : Dm * Qe = (c : K) • (Qe * Ps) := by
    have h1 : Dm = (c : K) • Matrix.diagonal (fun i : Fin 5 => ω ^ ((s : ℕ) * (i : ℕ))) := by
      ext i j
      by_cases hij : i = j
      · subst hij
        simp [hDm, hdu]
      · simp [hDm, Matrix.diagonal_apply_ne _ hij]
    rw [h1, Matrix.smul_mul, diagonal_mul_cycEigen5 hω5 a s]
  have hinner := inner_swap_identity (K := K) hω0 s (c : K) t c.ne_zero ht0
  have hdu' : (fun i => tf i * (du i : K)) = fun i => tf i * ((c : K) * ω ^ ((s : ℕ) * (i : ℕ))) :=
    funext fun i => by rw [hdu i]
  have hDmg : Dm * (g : Matrix (Fin 5) (Fin 5) K) =
      (g : Matrix (Fin 5) (Fin 5) K) * (Dm * (Ps * Matrix.diagonal rf)) := by
    have hR : (Matrix.diagonal tf) * (Dm * (Ps * Matrix.diagonal rf)) =
        (c : K) • (Ps * Matrix.diagonal tf) := by
      rw [← Matrix.mul_assoc, hDm, Matrix.diagonal_mul_diagonal, hdu']
      exact hinner.symm
    rw [hg, Matrix.mul_assoc Qe, hR, ← Matrix.mul_assoc, hDmQ, Matrix.smul_mul, Matrix.mul_assoc,
      Matrix.mul_smul]
  have hg1 : (g : Matrix (Fin 5) (Fin 5) K).det = 1 := g.2
  have hDmdet : Dm.det ≠ 0 := by
    rw [hDm, Matrix.det_diagonal]
    exact Finset.prod_ne_zero_iff.2 fun i _ => (du i).ne_zero
  have hdetPs : Ps.det = 1 := by
    have h := (rotSL ^ (s : ℕ) : SL(5, K)).2
    rwa [coe_rotSL_pow s] at h
  have hTdet : (Ps * Matrix.diagonal rf).det = 1 := by
    have h := congrArg Matrix.det hDmg
    rw [Matrix.det_mul, Matrix.det_mul, hg1, mul_one, one_mul] at h
    rw [Matrix.det_mul] at h
    exact mul_left_cancel₀ hDmdet (by rw [← h, mul_one])
  have hprod : ∏ k, rf k = 1 := by
    rw [Matrix.det_mul, hdetPs, one_mul, Matrix.det_diagonal] at hTdet
    exact hTdet
  have hrf0 : ∀ k, rf k ≠ 0 := fun k =>
    mul_ne_zero (htf0 k) (inv_ne_zero (mul_ne_zero (htf0 (k + s)) (pow_ne_zero _ hω0)))
  set r : Fin 5 → Kˣ := fun k => Units.mk0 (rf k) (hrf0 k) with hrdef
  have hr : ∏ i, (r i : K) = 1 := by simpa [hrdef] using hprod
  refine ⟨g, δ, hδ, r, hr, ?_, ?_⟩
  · calc g⁻¹ * (diagSLn d hd * coxSL5) * g = g⁻¹ * ((diagSLn d hd * coxSL5) * g) := mul_assoc _ _ _
      _ = g⁻¹ * (g * diagSLn δ hδ) := by rw [hMg]
      _ = diagSLn δ hδ := inv_mul_cancel_left _ _
  · have hTmat : ((rotSL ^ (s : ℕ) * diagSLn r hr : SL(5, K)) : Matrix (Fin 5) (Fin 5) K) =
        Ps * Matrix.diagonal rf := by
      rw [Matrix.SpecialLinearGroup.coe_mul, coe_rotSL_pow s, coe_diagSLn]
      rfl
    have hconj : conjDiagn du g = g * conjDiagn du (rotSL ^ (s : ℕ) * diagSLn r hr) := by
      apply Subtype.ext
      rw [coe_conjDiagn, Matrix.SpecialLinearGroup.coe_mul, coe_conjDiagn, hTmat]
      show Dm * (g : Matrix (Fin 5) (Fin 5) K) *
          Matrix.diagonal (fun i => (((du i)⁻¹ : Kˣ) : K)) =
        (g : Matrix (Fin 5) (Fin 5) K) * (Dm * (Ps * Matrix.diagonal rf) *
          Matrix.diagonal (fun i => (((du i)⁻¹ : Kˣ) : K)))
      rw [hDmg, Matrix.mul_assoc]
    have h1 : g⁻¹ * conjDiagn du g = conjDiagn du (rotSL ^ (s : ℕ) * diagSLn r hr) := by
      rw [hconj]
      group
    have h2 := congrArg (conjDiagn (fun i => (du i)⁻¹)) h1
    have h3 : ∀ X Y : SL(5, K), conjDiagn (fun i => (du i)⁻¹) (X * Y) =
        conjDiagn (fun i => (du i)⁻¹) X * conjDiagn (fun i => (du i)⁻¹) Y := fun X Y =>
      (conjDiagnHom (fun i => (du i)⁻¹)).map_mul X Y
    have e1 : ∀ X : SL(5, K), conjDiagn (fun i => (du i)⁻¹) (conjDiagn du X) = X := fun X =>
      conjDiagn_inv_conjDiagn du X
    rw [h3, e1, e1] at h2
    exact h2

end Swap

end One

end KSE8Five

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ
