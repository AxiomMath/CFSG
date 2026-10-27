module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeBadPlaneToralHVec
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeBadPlaneToralFrames
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeBadPlaneToralMat

public noncomputable section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

open Matrix CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Seitz
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.RankThree.PartOne.KF4 CFSG.RankThree.PartOne.KE
open scoped MatrixGroups

set_option linter.unusedSectionVars false

section Mat

variable {K : Type*} [Field K]

theorem conj_transvection_cyc1 (d : Fin 3 → K) (h2 : d 2 ≠ 0) (t : K) :
    (diagonal d * signedCycMat : Matrix (Fin 3) (Fin 3) K) * (1 + Matrix.single 0 1 t) =
      (1 + Matrix.single 1 2 (d 1 / d 2 * t)) * (diagonal d * signedCycMat) := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [signedCycMat, Matrix.mul_apply, Fin.sum_univ_three, Matrix.single_apply,
      Matrix.add_apply, Matrix.mul_add, Matrix.add_mul, Matrix.diagonal_apply] <;> field_simp

theorem conj_transvection_cyc2 (d : Fin 3 → K) (h1 : d 1 ≠ 0) (t : K) :
    (diagonal d * signedCycMat ^ 2 : Matrix (Fin 3) (Fin 3) K) * (1 + Matrix.single 1 2 t) =
      (1 + Matrix.single 0 1 (d 0 / d 1 * t)) * (diagonal d * signedCycMat ^ 2) := by
  rw [signedCycMat_sq]
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.single_apply,
      Matrix.add_apply, Matrix.mul_add, Matrix.add_mul, Matrix.diagonal_apply] <;> field_simp

theorem conjSL_transvection_cyc1 {Γ : GL (Fin 3) K} {d : Fin 3 → K} (h2 : d 2 ≠ 0)
    (hΓ : (Γ : Matrix (Fin 3) (Fin 3) K) = diagonal d * signedCycMat) (t : K) :
    conjSL Γ (SpecialLinearGroup.transvection (show (0 : Fin 3) ≠ 1 by decide) t) =
      SpecialLinearGroup.transvection (show (1 : Fin 3) ≠ 2 by decide) (d 1 / d 2 * t) := by
  apply Subtype.ext
  have hΓi : (Γ : Matrix (Fin 3) (Fin 3) K) * ((Γ⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)
      = 1 := Units.mul_inv Γ
  rw [conjSL_apply, CFSG.LieType.SeitzGeneration.conjUnit_coe, SpecialLinearGroup.transvection_coe,
    SpecialLinearGroup.transvection_coe, hΓ, conj_transvection_cyc1 d h2 t, Matrix.mul_assoc,
    ← hΓ, hΓi, Matrix.mul_one]

theorem conjSL_transvection_cyc2 {Γ : GL (Fin 3) K} {d : Fin 3 → K} (h1 : d 1 ≠ 0)
    (hΓ : (Γ : Matrix (Fin 3) (Fin 3) K) = diagonal d * signedCycMat ^ 2) (t : K) :
    conjSL Γ (SpecialLinearGroup.transvection (show (1 : Fin 3) ≠ 2 by decide) t) =
      SpecialLinearGroup.transvection (show (0 : Fin 3) ≠ 1 by decide) (d 0 / d 1 * t) := by
  apply Subtype.ext
  have hΓi : (Γ : Matrix (Fin 3) (Fin 3) K) * ((Γ⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)
      = 1 := Units.mul_inv Γ
  rw [conjSL_apply, CFSG.LieType.SeitzGeneration.conjUnit_coe, SpecialLinearGroup.transvection_coe,
    SpecialLinearGroup.transvection_coe, hΓ, conj_transvection_cyc2 d h1 t, Matrix.mul_assoc,
    ← hΓ, hΓi, Matrix.mul_one]

private theorem toralBH_three_ne_zero {ω : Kˣ} (hw3 : ω ^ 3 = 1) (hw1 : ω ≠ 1) : (3 : K) ≠ 0 := by
  intro h3
  apply hw1
  have h : ((ω : Kˣ) : K) ^ 3 = 1 := by rw [← Units.val_pow_eq_pow_val, hw3, Units.val_one]
  have h0 : (((ω : Kˣ) : K) - 1) ^ 3 = 0 := by
    linear_combination h - (((ω : Kˣ) : K) ^ 2 - ((ω : Kˣ) : K)) * h3
  exact Units.ext (sub_eq_zero.1 ((pow_eq_zero_iff (by norm_num)).1 h0))

theorem exists_minor_ne_zero (h3 : (3 : K) ≠ 0) (i : Fin 3) :
    ∃ k₁ k₂ : Fin Tag.E6.rank,
      ((cartanPair Tag.E6 (e6LinePair i).1 k₁ * cartanPair Tag.E6 (e6LinePair i).2 k₂ -
        cartanPair Tag.E6 (e6LinePair i).1 k₂ * cartanPair Tag.E6 (e6LinePair i).2 k₁ : ℤ) : K)
          ≠ 0 ∧
      ((cartanPair Tag.E6 (e6LinePair i).2 k₁ * cartanPair Tag.E6 (e6LinePair i).1 k₂ -
        cartanPair Tag.E6 (e6LinePair i).2 k₂ * cartanPair Tag.E6 (e6LinePair i).1 k₁ : ℤ) : K)
          ≠ 0 := by
  have key : ∀ i : Fin 3, ∃ k₁ k₂ : Fin Tag.E6.rank,
      (cartanPair Tag.E6 (e6LinePair i).1 k₁ * cartanPair Tag.E6 (e6LinePair i).2 k₂ -
        cartanPair Tag.E6 (e6LinePair i).1 k₂ * cartanPair Tag.E6 (e6LinePair i).2 k₁ = 3 ∨
       cartanPair Tag.E6 (e6LinePair i).1 k₁ * cartanPair Tag.E6 (e6LinePair i).2 k₂ -
        cartanPair Tag.E6 (e6LinePair i).1 k₂ * cartanPair Tag.E6 (e6LinePair i).2 k₁ = 1) ∧
      (cartanPair Tag.E6 (e6LinePair i).2 k₁ * cartanPair Tag.E6 (e6LinePair i).1 k₂ -
        cartanPair Tag.E6 (e6LinePair i).2 k₂ * cartanPair Tag.E6 (e6LinePair i).1 k₁ = -3 ∨
       cartanPair Tag.E6 (e6LinePair i).2 k₁ * cartanPair Tag.E6 (e6LinePair i).1 k₂ -
        cartanPair Tag.E6 (e6LinePair i).2 k₂ * cartanPair Tag.E6 (e6LinePair i).1 k₁ = -1) := by
    decide +kernel
  obtain ⟨k₁, k₂, h1, h2⟩ := key i
  refine ⟨k₁, k₂, ?_, ?_⟩
  · rcases h1 with h | h <;> rw [h] <;> simp [h3]
  · rcases h2 with h | h <;> rw [h] <;> simp [h3]

end Mat

section Cyc

variable {K : Type} [Field K]

theorem cyc_not_fix {ρ : SpecialLinearGroup (Fin 3) K →* ModGL Tag.E6 K}
    {σ : Fin 3 → Fin 3 → Fin Tag.E6.rank → ℤ} (hfr : IsA2Frame ρ σ) {i : Fin 3}
    (h01 : σ 0 1 = (e6LinePair i).1) (h12 : σ 1 2 = (e6LinePair i).2) (h3 : (3 : K) ≠ 0)
    {g : ModGL Tag.E6 K}
    (hfix : ∀ k, (g : Module.End K (RootModule Tag.E6 K)) (hVec Tag.E6 K k) = hVec Tag.E6 K k)
    {Γ : GL (Fin 3) K} {d : Fin 3 → K} {n : ℕ} (hn : ¬ 3 ∣ n)
    (hΓ : (Γ : Matrix (Fin 3) (Fin 3) K) = diagonal d * signedCycMat ^ n)
    (hconj : ∀ s, g * ρ s * g⁻¹ = ρ (conjSL Γ s)) : False := by
  obtain ⟨k₁, k₂, hD1, hD2⟩ := exists_minor_ne_zero h3 i
  have hdet : d 0 * d 1 * d 2 ≠ 0 := by
    have h := ((Matrix.isUnit_iff_isUnit_det (Γ : Matrix (Fin 3) (Fin 3) K)).1 Γ.isUnit).ne_zero
    rwa [hΓ, Matrix.det_mul, Matrix.det_diagonal, Fin.prod_univ_three, det_pow, det_signedCycMat,
      one_pow, mul_one] at h
  have hd1 : d 1 ≠ 0 := right_ne_zero_of_mul (left_ne_zero_of_mul hdet)
  have hd2 : d 2 ≠ 0 := right_ne_zero_of_mul hdet
  obtain ⟨e, he⟩ := hfr.transv 0 1 (by decide)
  obtain ⟨e', he'⟩ := hfr.transv 1 2 (by decide)
  have hm : n % 3 = 1 ∨ n % 3 = 2 := by omega
  rw [pow_eq_pow_mod n (signedCycMat_pow_three (K := K))] at hΓ
  rcases hm with hm | hm
  · rw [hm, pow_one] at hΓ
    have hc := hconj (SpecialLinearGroup.transvection (show (0 : Fin 3) ≠ 1 by decide)
      ((e⁻¹ : Kˣ) : K))
    rw [conjSL_transvection_cyc1 hd2 hΓ, he, he', Units.mul_inv] at hc
    refine not_fix_hVec_of_conj hfix (hfr.isRoot 0 1 (by decide)) (hfr.isRoot 1 2 (by decide))
      ((e' : K) * (d 1 / d 2 * ((e⁻¹ : Kˣ) : K))) hc k₁ k₂ ?_
    rw [h01, h12]
    exact hD1
  · rw [hm] at hΓ
    have hc := hconj (SpecialLinearGroup.transvection (show (1 : Fin 3) ≠ 2 by decide)
      ((e'⁻¹ : Kˣ) : K))
    have hd0 : d 0 ≠ 0 := left_ne_zero_of_mul (left_ne_zero_of_mul hdet)
    rw [conjSL_transvection_cyc2 hd1 hΓ, he, he', Units.mul_inv] at hc
    refine not_fix_hVec_of_conj hfix (hfr.isRoot 1 2 (by decide)) (hfr.isRoot 0 1 (by decide))
      ((e : K) * (d 0 / d 1 * ((e'⁻¹ : Kˣ) : K))) hc k₁ k₂ ?_
    rw [h01, h12]
    exact hD2

end Cyc

section Cartan

variable
  {K : Type} [Field K]

theorem exists_toralFrames_of_frames {ω : Kˣ} (hw3 : ω ^ 3 = 1) (hw1 : ω ≠ 1)
    {ρ : Fin 3 → SpecialLinearGroup (Fin 3) K →* ModGL Tag.E6 K}
    {σ : Fin 3 → Fin 3 → Fin 3 → Fin Tag.E6.rank → ℤ}
    (hfr : ∀ i, IsA2Frame (ρ i) (σ i)) (hrange : ∀ i, (ρ i).range = e6LineFactor K i)
    (h01 : ∀ i, σ i 0 1 = (e6LinePair i).1) (h12 : ∀ i, σ i 1 2 = (e6LinePair i).2)
    (hmono : ∀ i, ρ i signedCycSL ∈ monomialSubgroup Tag.E6 K) :
    ∃ T : ToralFrames K ω, T.ρ = ρ ∧ T.σ = σ := by
  have htor : ∀ i b s, rootDiagUnit Tag.E6 b * ρ i s * (rootDiagUnit Tag.E6 b)⁻¹ =
      ρ i (conjSL (diagGL3 fun j => rootChar b (σ i j 0)) s) := fun i b s => by
    rw [conjSL_diagGL3]
    exact (hfr i).torus b s
  obtain ⟨π, hπ, hπL, -, hconjd, -, hπconj, hMdec⟩ := exists_commProd_of_frames
    (D := fun i b => diagGL3 fun j => rootChar b (σ i j 0)) hw3 hw1 hrange htor
  have hπM : ∀ x, π x ∈ toralRootGroup Tag.E6 K (e6LineChar ω) := fun x => by
    have hle : rootSpan Tag.E6 K (⋃ i, (e6LineRoots i : Set (Fin Tag.E6.rank → ℤ))) ≤
        toralRootGroup Tag.E6 K (e6LineChar ω) := by
      show _ ≤ torusGroup Tag.E6 K ⊔ rootSpan Tag.E6 K (rootCharKernel (e6LineChar ω))
      rw [e6Line_kernel hw3 hw1]
      exact le_sup_right
    exact hle (hπL x)
  exact ⟨⟨ρ, σ, π, hfr, hrange, h01, h12, hmono, hπ, hπM, fun b i s => htor i b s, hπconj,
    hconjd, hMdec⟩, rfl, rfl⟩

theorem e6Toral_caseB_cartan {ω : Kˣ} (hw3 : ω ^ 3 = 1) (hw1 : ω ≠ 1)
    {ρ : Fin 3 → SpecialLinearGroup (Fin 3) K →* ModGL Tag.E6 K}
    {σ : Fin 3 → Fin 3 → Fin 3 → Fin Tag.E6.rank → ℤ}
    (hfr : ∀ i, IsA2Frame (ρ i) (σ i)) (hrange : ∀ i, (ρ i).range = e6LineFactor K i)
    (h01 : ∀ i, σ i 0 1 = (e6LinePair i).1) (h12 : ∀ i, σ i 1 2 = (e6LinePair i).2)
    (hmono : ∀ i, ρ i signedCycSL ∈ monomialSubgroup Tag.E6 K)
    (c : Fin Tag.E6.rank → Kˣ) (w : Fin 3 → SpecialLinearGroup (Fin 3) K)
    (d : Fin 3 → Fin 3 → K) (n : Fin 3 → ℕ)
    (hw : ∀ i, ((diagGL3 fun j => rootChar c (σ i j 0) : GL (Fin 3) K) :
        Matrix (Fin 3) (Fin 3) K) * (w i : Matrix (Fin 3) (Fin 3) K) =
        diagonal (d i) * signedCycMat ^ n i)
    (hcyc : ∃ i, ¬ 3 ∣ n i) :
    ∃ k : Fin Tag.E6.rank,
      ((rootDiagUnit Tag.E6 c * (ρ 0 (w 0) * ρ 1 (w 1) * ρ 2 (w 2)) : ModGL Tag.E6 K) :
        Module.End K (RootModule Tag.E6 K)) (hVec Tag.E6 K k) ≠ hVec Tag.E6 K k := by
  obtain ⟨T, rfl, rfl⟩ := exists_toralFrames_of_frames hw3 hw1 hfr hrange h01 h12 hmono
  by_contra hcon
  obtain ⟨i, hi⟩ := hcyc
  have hfix : ∀ k, ((rootDiagUnit Tag.E6 c * T.π w : ModGL Tag.E6 K) :
      Module.End K (RootModule Tag.E6 K)) (hVec Tag.E6 K k) = hVec Tag.E6 K k := fun k => by
    rw [T.π_apply]
    exact not_not.1 ((not_exists.1 hcon) k)
  exact cyc_not_fix (hfr i) (h01 i) (h12 i) (toralBH_three_ne_zero hw3 hw1) hfix
    (Γ := T.D i c * SpecialLinearGroup.toGL (w i)) (d := d i) hi (hw i) (fun s => T.act c w i s)

end Cartan

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

end
