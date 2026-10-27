module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneOKronCore
public import CFSG.Certificates.Kernel.ThDemp.OrbCent
public import CFSG.CharacterTheory.Semidihedral.DihedralQuaternion
public import CFSG.ClassicalGroups.Orthogonal.Matrix
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneOEAlg
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneOGenFix
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneOThreeTools
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixStructure

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.O

open Matrix CFSG Subgroup CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.Burgoyne.PSL (signMat reflGL rotGL)
open scoped commutatorElement

variable {K : Type} [Field K] {n : ℕ}

theorem blkDiag_add (n : ℕ) (W W' : Matrix (Fin 2) (Fin 2) K) :
    blkDiag n (W + W') = blkDiag n W + blkDiag n W' := by
  ext p q
  obtain ⟨⟨i, j⟩, rfl⟩ := (pairEquiv n).surjective p
  obtain ⟨⟨k, l⟩, rfl⟩ := (pairEquiv n).surjective q
  rw [Matrix.add_apply, blkDiag_apply, blkDiag_apply, blkDiag_apply]
  split_ifs <;> simp

theorem blkDiag_smul (n : ℕ) (a : K) (W : Matrix (Fin 2) (Fin 2) K) :
    blkDiag n (a • W) = a • blkDiag n W := by
  ext p q
  obtain ⟨⟨i, j⟩, rfl⟩ := (pairEquiv n).surjective p
  obtain ⟨⟨k, l⟩, rfl⟩ := (pairEquiv n).surjective q
  rw [Matrix.smul_apply, blkDiag_apply, blkDiag_apply]
  split_ifs <;> simp

theorem blkDiag_one' (n : ℕ) : blkDiag n (1 : Matrix (Fin 2) (Fin 2) K) = 1 := by
  rw [blkDiag, diagonal_one, map_one]

theorem eq_of_blkDiag_eq {n : ℕ} (hn : 0 < n) {W W' : Matrix (Fin 2) (Fin 2) K}
    (h : blkDiag n W = blkDiag n W') : W = W' := by
  ext a b
  have e := congrFun (congrFun h (pairEquiv n (⟨0, hn⟩, a))) (pairEquiv n (⟨0, hn⟩, b))
  simpa only [blkDiag_apply, eq_self_iff_true, ↓reduceIte] using e

theorem blkDiag_transpose' (n : ℕ) (W : Matrix (Fin 2) (Fin 2) K) :
    (blkDiag n W)ᵀ = blkDiag n Wᵀ := blkDiag_transpose n W

theorem wMat_transpose (a b : K) : (wMat a b)ᵀ = wMat a b := diagonal_transpose _

theorem kappa_pow_eq_one_of_pow {d : ℕ} {Q : QuadraticForm K (Fin d → K)}
    {g : similarityPairs Q} (hg : g.val.right = 1) {m : ℕ} {μ : Kˣ}
    (hpow : (g.val.left : Matrix (Fin d) (Fin d) K) ^ m = (μ : K) • 1) : oκ Q g ^ m = 1 := by
  obtain ⟨hlm, hrm⟩ := pow_left_of_right_eq_one hg m
  rw [← map_pow]
  have e : oκ Q (g ^ m) = oκ Q (1 : similarityPairs Q) := by
    refine oκ_eq_of_left_eq (c := μ) (by rw [hrm]; rfl) ?_
    rw [hlm]
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_mul, GeneralLinearGroup.coe_scalar, hpow]
    change _ = Matrix.scalar (Fin d) (μ : K) * 1
    rw [Matrix.mul_one, Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]
  rw [e, map_one]

variable [Finite K]

theorem pc_core (hK : ringChar K ≠ 2) (hn : 3 ≤ n) {c : K} (hc : c ≠ 0)
    {R : GL (Fin (2 * n)) K} (hR : (R : Matrix (Fin (2 * n)) (Fin (2 * n)) K) =
      blkDiag n (wMat 1 (-c))) (hker : OKer (oQ R))
    (hinj : Function.Injective (MulAut.conj : StatedProj (matrixDerived (oQ R)) →*
      MulAut (StatedProj (matrixDerived (oQ R)))))
    {B : Subgroup (MulAut (StatedProj (matrixDerived (oQ R))))}
    (hB : (MulAut.conj : StatedProj (matrixDerived (oQ R)) →*
      MulAut (StatedProj (matrixDerived (oQ R)))).range ≤ B)
    {g : similarityPairs (oQ R)} (hg1 : g.val.right = 1)
    (hgA : (g.val.left : Matrix (Fin (2 * n)) (Fin (2 * n)) K) = blkDiag n (jMat c))
    (hcd : CompData ⁅isoCent R g.val.left, isoCent R g.val.left⁆)
    {g' : similarityPairs (oQ R)} (hy : oκ _ g' ∈ oddCoreIn B (oκ _ g)) :
    g'.val.right = 1 ∧ ∃ x z : K,
      (g'.val.left : Matrix (Fin (2 * n)) (Fin (2 * n)) K) = x • 1 + z • blkDiag n (jMat c) := by
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
  have hRs : (R : Matrix (Fin (2 * n)) (Fin (2 * n)) K)ᵀ = R := by
    rw [hR, blkDiag_transpose, wMat_transpose]
  have hA2 : (g.val.left : Matrix (Fin (2 * n)) (Fin (2 * n)) K) * g.val.left = c • 1 := by
    rw [hgA, blkDiag_mul, jMat_mul_self, blkDiag_smul, blkDiag_one']
  have hmem : ∀ X : GL (Fin n) K, (X : Matrix (Fin n) (Fin n) K)ᵀ * X = 1 →
      kronGL K n X ∈ isoCent R g.val.left := fun X hX =>
    kronGL_mem_isoCent_blkDiag hR hgA hX
  have hI : 3 ≤ (Finset.univ : Finset (Fin n)).card := by
    rw [Finset.card_univ, Fintype.card_fin]
    exact hn
  obtain ⟨hτ1, hDA, hfix, hS⟩ := kron_core hK hRs hker hinj hB hg1 hc hA2 hcd hI
    (fun i _ => hmem _ (reflGL_orth i)) (fun i _ j _ hij a b hab => hmem _ (rotGL_orth hij hab))
    hy
  set D := (g'.val.left : Matrix (Fin (2 * n)) (Fin (2 * n)) K) with hD
  have hP : ∀ i j k : Fin n, i ≠ j → j ≠ k → i ≠ k →
      D * kronI K n ((⁅Equiv.swap i j, Equiv.swap j k⁆)⁻¹.permMatrix K) =
        kronI K n ((⁅Equiv.swap i j, Equiv.swap j k⁆)⁻¹.permMatrix K) * D := by
    intro i j k _ _ _
    have hm : kronGL K n ⁅permGL K n (Equiv.swap i j), permGL K n (Equiv.swap j k)⁆ ∈
        ⁅isoCent R g.val.left, isoCent R g.val.left⁆ := by
      rw [map_commutatorElement]
      exact commutator_mem_commutator (hmem _ (permGL_orth _)) (hmem _ (permGL_orth _))
    have e := hfix _ hm
    rwa [coe_kronGL, coe_commutator_permGL] at e
  have hblk := eq_blkDiag_of_kron h2 hn (fun i j hij => hS i (Finset.mem_univ _) j
    (Finset.mem_univ _) hij) hP
  set D₀ : Matrix (Fin 2) (Fin 2) K := Matrix.of fun a b =>
    D (pairEquiv n (⟨0, by omega⟩, a)) (pairEquiv n (⟨0, by omega⟩, b)) with hD₀
  have hD₀j : D₀ * jMat c = jMat c * D₀ := by
    apply eq_of_blkDiag_eq (by omega : 0 < n)
    rw [← blkDiag_mul, ← blkDiag_mul, ← hblk, ← hgA]
    exact hDA
  refine ⟨hτ1, D₀ 0 0, D₀ 1 0, ?_⟩
  rw [hblk, eq_of_commute_jMat hc hD₀j, blkDiag_add, blkDiag_smul, blkDiag_smul, blkDiag_one']
  congr 2 <;> rw [← eq_of_commute_jMat hc hD₀j]

theorem pc_oddCoreIn_eq_bot_three (hK : ringChar K ≠ 2) (hK3 : Nat.card K = 3) (hn : 3 ≤ n)
    {c : K} (hc : c ≠ 0) {R : GL (Fin (2 * n)) K}
    (hR : (R : Matrix (Fin (2 * n)) (Fin (2 * n)) K) = blkDiag n (wMat 1 (-c)))
    (hker : OKer (oQ R))
    (hinj : Function.Injective (MulAut.conj : StatedProj (matrixDerived (oQ R)) →*
      MulAut (StatedProj (matrixDerived (oQ R)))))
    {B : Subgroup (MulAut (StatedProj (matrixDerived (oQ R))))}
    (hB : (MulAut.conj : StatedProj (matrixDerived (oQ R)) →*
      MulAut (StatedProj (matrixDerived (oQ R)))).range ≤ B)
    {g : similarityPairs (oQ R)} (hg1 : g.val.right = 1)
    (hgA : (g.val.left : Matrix (Fin (2 * n)) (Fin (2 * n)) K) = blkDiag n (jMat c))
    (hcd : CompData ⁅isoCent R g.val.left, isoCent R g.val.left⁆)
    (hsurj : OSurjCore B (oκ _ g)) :
    oddCoreIn B (oκ _ g) = ⊥ := by
  have : Fintype K := Fintype.ofFinite K
  have hcube : ∀ a : K, a ^ 3 = a := fun a => by
    rw [← hK3, Nat.card_eq_fintype_card, FiniteField.pow_card]
  have hsq1 : ∀ a : K, a ≠ 0 → a ^ 2 = 1 := by
    intro a ha
    have e := hcube a
    have : a * (a ^ 2 - 1) = 0 := by linear_combination e
    exact sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_left ha)
  rw [eq_bot_iff]
  intro y hy
  obtain ⟨g', rfl⟩ := hsurj y hy
  obtain ⟨hτ1, x, z, hxz⟩ := pc_core hK hn hc hR hker hinj hB hg1 hgA hcd hy
  set A := blkDiag n (jMat c) with hA
  have hA2 : A * A = c • 1 := by rw [hA, blkDiag_mul, jMat_mul_self, blkDiag_smul, blkDiag_one']
  set D := (g'.val.left : Matrix (Fin (2 * n)) (Fin (2 * n)) K) with hD
  have hD2 : D * D = (x ^ 2 + c * z ^ 2) • 1 + (2 * x * z) • A := by
    rw [hxz]
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
      Matrix.mul_one, hA2, smul_smul, add_smul]
    module
  have hDinv : D * ((g'.val.left⁻¹ : GL (Fin (2 * n)) K) : Matrix (Fin (2 * n)) (Fin (2 * n)) K) =
      1 := by rw [hD, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hDinv' : ((g'.val.left⁻¹ : GL (Fin (2 * n)) K) : Matrix (Fin (2 * n)) (Fin (2 * n)) K) *
      D = 1 := by rw [hD, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hA00 : A (pairEquiv n (⟨0, by omega⟩, 0)) (pairEquiv n (⟨0, by omega⟩, 0)) = 0 := by
    simp only [hA, blkDiag_apply, ↓reduceIte]
    rfl
  have hkey : x * z * (x ^ 2 + c * z ^ 2) = 0 := by
    by_cases hx : x = 0
    · rw [hx]; ring
    by_cases hz : z = 0
    · rw [hz]; ring
    have hx2 := hsq1 x hx
    have hz2 := hsq1 z hz
    have hc2 := hsq1 c hc
    have hcc : (c - 1) * (c + 1) = 0 := by linear_combination hc2
    rcases mul_eq_zero.1 hcc with h1 | h1
    ·
      exfalso
      have hc1 : c = 1 := sub_eq_zero.1 h1
      have hprod : D * (x • 1 - z • A) = (x ^ 2 - c * z ^ 2) • (1 : Matrix _ _ K) := by
        rw [hxz]
        simp only [Matrix.add_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul,
          Matrix.one_mul, Matrix.mul_one, hA2]
        module
      have hzero : D * (x • 1 - z • A) = 0 := by
        rw [hprod, hc1, hx2, hz2]
        simp
      have h0 : x • (1 : Matrix (Fin (2 * n)) (Fin (2 * n)) K) - z • A = 0 := by
        have := congrArg (fun M => ((g'.val.left⁻¹ : GL (Fin (2 * n)) K) :
          Matrix (Fin (2 * n)) (Fin (2 * n)) K) * M) hzero
        simpa only [← Matrix.mul_assoc, hDinv', Matrix.one_mul, Matrix.mul_zero] using this
      have e := congrFun (congrFun h0 (pairEquiv n (⟨0, by omega⟩, 0)))
        (pairEquiv n (⟨0, by omega⟩, 0))
      rw [Matrix.sub_apply, Matrix.smul_apply, Matrix.smul_apply, hA00, one_apply_eq] at e
      simp only [smul_eq_mul, mul_one, mul_zero, sub_zero, Matrix.zero_apply] at e
      exact hx e
    · have hc1 : c = -1 := eq_neg_of_add_eq_zero_left h1
      rw [hc1, hx2, hz2]
      ring
  set μ : K := (x ^ 2 + c * z ^ 2) ^ 2 + c * (2 * x * z) ^ 2 with hμ
  have hD4 : D ^ 4 = μ • 1 := by
    have e : D ^ 4 = (D * D) * (D * D) := by noncomm_ring
    have hD4' : D ^ 4 = μ • 1 + (2 * ((x ^ 2 + c * z ^ 2) * (2 * x * z))) • A := by
      rw [e, hD2]
      simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul,
        Matrix.one_mul, Matrix.mul_one, hA2]
      rw [hμ]
      module
    have hcoef : 2 * ((x ^ 2 + c * z ^ 2) * (2 * x * z)) = 0 := by
      linear_combination (4 : K) * hkey
    rw [hcoef, zero_smul, add_zero] at hD4'
    exact hD4'
  have hμ0 : μ ≠ 0 := by
    intro h0
    rw [h0, zero_smul] at hD4
    have : Nonempty (Fin (2 * n)) := ⟨⟨0, by omega⟩⟩
    have e := congrArg Matrix.det hD4
    rw [det_pow, det_zero] at e
    exact (Matrix.isUnits_det_units g'.val.left).ne_zero (pow_eq_zero_iff (by norm_num) |>.1 e)
  have h4 := kappa_pow_eq_one_of_pow hτ1 (μ := Units.mk0 μ hμ0) hD4
  have hodd := odd_orderOf_of_mem_oddCoreIn hy
  have hdvd : orderOf (oκ _ g') ∣ 2 ^ 2 := orderOf_dvd_of_pow_eq_one h4
  obtain ⟨i, hi, hi'⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
  rw [hi'] at hodd
  have hi0 : i = 0 := by
    by_contra h
    obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
    rw [pow_succ] at hodd
    exact (Nat.not_even_iff_odd.2 hodd) (by simp)
  rw [hi0, pow_zero] at hi'
  exact orderOf_eq_one_iff.1 hi'

end CFSG.ComponentClassification.Burgoyne.O
