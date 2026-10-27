module

public import CFSG.LocalAnalysis.ComponentClassification.Foote5OddLieClOCentFix
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneOOrth2

public section

namespace CFSG.ComponentClassification.Foote5.OddLieCore

open Matrix CFSG Subgroup CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.Burgoyne.Proj CFSG.ComponentClassification.Burgoyne.O
open CFSG.ComponentClassification.Burgoyne.PSL (signMat reflGL rotGL rotMat_apply_ne_zero)

variable {K : Type} [Field K] [Finite K]

theorem ClO.orth2_eq_one (hK : ringChar K ≠ 2) {c : K} (hc : ¬ IsSquare c) {n : ℕ}
    (hn : 4 ≤ n) [Fact (Irreducible (sqPoly c))] {w : Fin n → EAlg c} (hw : ∀ i, w i ≠ 0)
    (hw1 : ∀ i : Fin n, (i : ℕ) + 1 < n → w i = 1) {R : GL (Fin (2 * n)) K}
    (hRs : (R : Matrix (Fin (2 * n)) (Fin (2 * n)) K)ᵀ = R)
    (hR : (R : Matrix (Fin (2 * n)) (Fin (2 * n)) K) =
      blkDiag n (wMat 1 c) * resMat (phiE c).toRingHom n (diagonal w))
    (hker : OKer (oQ R))
    (hinj : Function.Injective (MulAut.conj : StatedProj (matrixDerived (oQ R)) →*
      MulAut (StatedProj (matrixDerived (oQ R)))))
    {g : similarityPairs (oQ R)} (hg1 : g.val.right = 1)
    (hgA : (g.val.left : Matrix (Fin (2 * n)) (Fin (2 * n)) K) = blkDiag n (jMat c))
    {Ro : Subgroup (MulAut (StatedProj (matrixDerived (oQ R))))} (hRodd : Odd (Nat.card Ro))
    (hRi : ∀ y ∈ Ro, y * oκ _ g = oκ _ g * y)
    (hRc : ∀ s, oκ _ g s = s → Odd (orderOf s) → ∀ y ∈ Ro,
      MulAut.conj s * y * (MulAut.conj s)⁻¹ ∈ Ro)
    (hsurj : ∀ y ∈ Ro, ∃ g' : similarityPairs (oQ R), y = oκ _ g') :
    ∀ y ∈ Ro, y = 1 := by
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
  have hc0 : c ≠ 0 := fun h => hc ⟨0, by rw [h, mul_zero]⟩
  have hcd := compData_orth2 hK hc0 (by omega) hw hR hgA
  set I₀ : Finset (Fin n) := Finset.univ.filter fun i => (i : ℕ) + 1 < n with hI₀
  have hmemI₀ : ∀ i : Fin n, i ∈ I₀ ↔ (i : ℕ) + 1 < n := fun i => by simp [hI₀]
  have hI₀c : 3 ≤ I₀.card := by
    have hsub : (Finset.univ.filter fun i : Fin n => (i : ℕ) < 3) ⊆ I₀ := by
      intro i hi
      rw [hmemI₀]
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
      omega
    refine le_trans ?_ (Finset.card_le_card hsub)
    have : (Finset.univ.filter fun i : Fin n => (i : ℕ) < 3) =
        Finset.image (fun k : Fin 3 => (⟨k, by omega⟩ : Fin n)) Finset.univ := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
      constructor
      · intro hi
        exact ⟨⟨i, hi⟩, Fin.ext rfl⟩
      · rintro ⟨k, -, rfl⟩
        exact k.2
    rw [this, Finset.card_image_of_injective _ (fun a b h => Fin.ext (by
      simpa using congrArg Fin.val h)), Finset.card_univ, Fintype.card_fin]
  have hA2 : (g.val.left : Matrix (Fin (2 * n)) (Fin (2 * n)) K) * g.val.left = c • 1 := by
    rw [hgA, blkDiag_mul, jMat_mul_self, blkDiag_smul_one]
  have hφa : ∀ a : K, (phiE c).toRingHom (algebraMap K (EAlg c) a) =
      algebraMap K (Matrix (Fin 2) (Fin 2) K) a := phiE_algebraMap c
  have hkron : ∀ X : GL (Fin n) K, (X : Matrix (Fin n) (Fin n) K)ᵀ * X = 1 →
      (∀ x y, (X : Matrix (Fin n) (Fin n) K) x y ≠ 0 → w x = w y) →
      kronGL K n X ∈ isoCent R g.val.left := fun X hX hXw =>
    kronGL_mem_iso_inf (σ := RingHom.id (EAlg c)) hφa (fun _ => rfl)
      (fun x => transpose_phiE_mul_wOne hc0 x) (phiE_root c) hR hgA hX (map_mul_diagonal_comm hXw)
  have hrefl : ∀ i ∈ I₀, kronGL K n (reflGL i) ∈ isoCent R g.val.left := fun i _ =>
    hkron _ (reflGL_orth i) fun x y h => by rw [reflGL_support i h]
  have hrot : ∀ i ∈ I₀, ∀ j ∈ I₀, ∀ (hij : i ≠ j) (a b : K) (hab : a ^ 2 + b ^ 2 = 1),
      kronGL K n (rotGL i j hij hab) ∈ isoCent R g.val.left := by
    intro i hi j hj hij a b hab
    refine hkron _ (rotGL_orth hij hab) fun x y h => ?_
    by_cases hxy : x = y
    · rw [hxy]
    rcases rotMat_apply_ne_zero hxy h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rw [hw1 _ ((hmemI₀ _).1 hi), hw1 _ ((hmemI₀ _).1 hj)]
    · rw [hw1 _ ((hmemI₀ _).1 hi), hw1 _ ((hmemI₀ _).1 hj)]
  intro y hy
  obtain ⟨g', rfl⟩ := hsurj y hy
  obtain ⟨hτ1, hDA, -, hS⟩ := ClO.kron_core hK hRs hker hinj hg1 hc0 hA2 hcd hI₀c hrefl hrot
    hRodd hRi hRc hy
  set D := (g'.val.left : Matrix (Fin (2 * n)) (Fin (2 * n)) K) with hD
  have hDj : D * blkDiag n (jMat c) = blkDiag n (jMat c) * D := by rw [← hgA]; exact hDA
  obtain ⟨Y, hY⟩ := exists_resMat_of_commute (phiE c).toRingHom
    (fun M hM => phiE_mem_range hc0 hM) hDj
  have hYd : ∀ x z, x ≠ z → Y x z = 0 := by
    intro x z hxz
    have hblk : ∀ a b : Fin 2, D (pairEquiv n (x, a)) (pairEquiv n (z, b)) = 0 := by
      intro a b
      by_cases hx : x ∈ I₀
      · exact (kron_iso_of_sign h2 hI₀c hS hx (Ne.symm hxz) a b).1
      · have hz : z ∈ I₀ := by
          rw [hmemI₀] at hx ⊢
          have := x.2
          have := z.2
          have : (x : ℕ) ≠ z := fun h => hxz (Fin.ext h)
          omega
        exact (kron_iso_of_sign h2 hI₀c hS hz hxz b a).2
    apply phiE_injective c
    ext a b
    have e := hblk a b
    rw [← hY, resMat_apply] at e
    rw [map_zero]
    exact e
  have hYdiag : Y = diagonal fun x => Y x x := by
    ext x z
    by_cases hxz : x = z
    · rw [hxz, diagonal_apply_eq]
    · rw [diagonal_apply_ne _ hxz, hYd x z hxz]
  obtain ⟨μ, hμ⟩ := (mem_similarityPairs_oQ h2 R hRs g'.val).1 g'.2
  rw [hτ1, show (R : Matrix (Fin (2 * n)) (Fin (2 * n)) K).map ⇑(1 : K ≃+* K) = R from by
    ext; rfl] at hμ
  have hW : ∀ x, ((phiE c).toRingHom x)ᵀ * wMat 1 c = wMat 1 c * (phiE c).toRingHom
      (RingHom.id _ x) := fun x => transpose_phiE_mul_wOne hc0 x
  have hμ' : blkDiag n (wMat 1 c) * resMat (phiE c).toRingHom n
      ((Y.map (RingHom.id _))ᵀ * diagonal w * Y) =
      blkDiag n (wMat 1 c) * resMat (phiE c).toRingHom n
        (algebraMap K (EAlg c) (μ : K) • diagonal w) := by
    rw [← resMat_transpose_mul_mul hW, resMat_algebraMap_smul hφa, hY, ← hR, Matrix.mul_smul,
      ← hR]
    exact hμ
  have hW₀ := wOne_inv_mul hc0
  have hμ'' := congrArg (fun M => blkDiag n (wMat 1 c⁻¹) * M) hμ'
  simp only [← Matrix.mul_assoc, blkDiag_mul, hW₀, blkDiag_one, Matrix.one_mul] at hμ''
  have hG := resMat_injective (phiE_injective c) n hμ''
  have hsq : ∀ x, Y x x * Y x x = algebraMap K (EAlg c) (μ : K) := by
    intro x
    have e := congrFun (congrFun hG x) x
    rw [hYdiag] at e
    simp only [diagonal_map (map_zero _), RingHom.id_apply, diagonal_transpose,
      diagonal_mul_diagonal, diagonal_apply_eq, Matrix.smul_apply, smul_eq_mul] at e
    have : w x * (Y x x * Y x x - algebraMap K (EAlg c) (μ : K)) = 0 := by
      linear_combination e
    exact sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_left (hw x))
  have hDD : D * D = (μ : K) • 1 := by
    rw [← hY, ← map_mul, hYdiag, diagonal_mul_diagonal]
    have : (fun x => Y x x * Y x x) = fun _ => algebraMap K (EAlg c) (μ : K) := funext hsq
    rw [this, resMat_diagonal, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, phiE_algebraMap,
      Algebra.algebraMap_eq_smul_one, blkDiag_smul_one]
  exact eq_one_of_odd_of_sq (ClSp.odd_orderOf_of_mem hRodd hy) (kappa_sq_eq_one_of_sq hτ1 hDD)

end CFSG.ComponentClassification.Foote5.OddLieCore
