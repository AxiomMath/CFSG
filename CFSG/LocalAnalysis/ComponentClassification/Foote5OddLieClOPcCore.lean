module

public import CFSG.LocalAnalysis.ComponentClassification.Foote5OddLieClOCentFix
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneOPcCore

public section

namespace CFSG.ComponentClassification.Foote5.OddLieCore

open Matrix CFSG Subgroup CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.Burgoyne.Proj CFSG.ComponentClassification.Burgoyne.O
open CFSG.ComponentClassification.Burgoyne.PSL (signMat reflGL rotGL)
open scoped commutatorElement

variable {K : Type} [Field K] {n : ℕ}

theorem ClO.commute_lin {d : ℕ} {Q : QuadraticForm K (Fin d → K)} {A : Matrix (Fin d) (Fin d) K}
    {a b : similarityPairs Q} (ha : a.val.right = 1) (hb : b.val.right = 1) {x₁ z₁ x₂ z₂ : K}
    (hal : (a.val.left : Matrix (Fin d) (Fin d) K) = x₁ • 1 + z₁ • A)
    (hbl : (b.val.left : Matrix (Fin d) (Fin d) K) = x₂ • 1 + z₂ • A) :
    oκ Q a * oκ Q b = oκ Q b * oκ Q a := by
  rw [← map_mul, ← map_mul]
  congr 1
  apply Subtype.ext
  apply SemidirectProduct.ext
  · apply Units.ext
    change ((a.val * b.val).left : Matrix (Fin d) (Fin d) K) = ((b.val * a.val).left : Matrix _ _ K)
    rw [SemidirectProduct.mul_left, SemidirectProduct.mul_left, ha, hb, map_one, MulAut.one_apply,
      MulAut.one_apply, Units.val_mul, Units.val_mul, hal, hbl]
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
      Matrix.mul_one]
    module
  · change (a.val * b.val).right = (b.val * a.val).right
    rw [SemidirectProduct.mul_right, SemidirectProduct.mul_right, ha, hb]

variable [Finite K]

theorem ClO.pc_core (hK : ringChar K ≠ 2) (hn : 3 ≤ n) {c : K} (hc : c ≠ 0)
    {R : GL (Fin (2 * n)) K} (hR : (R : Matrix (Fin (2 * n)) (Fin (2 * n)) K) =
      blkDiag n (wMat 1 (-c))) (hker : OKer (oQ R))
    (hinj : Function.Injective (MulAut.conj : StatedProj (matrixDerived (oQ R)) →*
      MulAut (StatedProj (matrixDerived (oQ R)))))
    {g : similarityPairs (oQ R)} (hg1 : g.val.right = 1)
    (hgA : (g.val.left : Matrix (Fin (2 * n)) (Fin (2 * n)) K) = blkDiag n (jMat c))
    (hcd : CompData ⁅isoCent R g.val.left, isoCent R g.val.left⁆)
    {Ro : Subgroup (MulAut (StatedProj (matrixDerived (oQ R))))} (hRodd : Odd (Nat.card Ro))
    (hRi : ∀ y ∈ Ro, y * oκ _ g = oκ _ g * y)
    (hRc : ∀ s, oκ _ g s = s → Odd (orderOf s) → ∀ y ∈ Ro,
      MulAut.conj s * y * (MulAut.conj s)⁻¹ ∈ Ro)
    {g' : similarityPairs (oQ R)} (hy : oκ _ g' ∈ Ro) :
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
  obtain ⟨hτ1, hDA, hfix, hS⟩ := ClO.kron_core hK hRs hker hinj hg1 hc hA2 hcd hI
    (fun i _ => hmem _ (reflGL_orth i)) (fun i _ j _ hij a b hab => hmem _ (rotGL_orth hij hab))
    hRodd hRi hRc hy
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

end CFSG.ComponentClassification.Foote5.OddLieCore
