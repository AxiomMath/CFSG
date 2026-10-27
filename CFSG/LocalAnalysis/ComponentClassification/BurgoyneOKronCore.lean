module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneOKronElts
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneOSplitCore

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.O

open Matrix CFSG Subgroup CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.Burgoyne.PSL (signMat reflGL rotGL mem_of_mem_oddCoreIn)
open scoped commutatorElement

variable {K : Type} [Field K] {n : ℕ}

theorem kappa_sq_eq_one_of_sq {d : ℕ} {Q : QuadraticForm K (Fin d → K)}
    {g : similarityPairs Q} (hg : g.val.right = 1) {μ : Kˣ}
    (hsq : (g.val.left : Matrix (Fin d) (Fin d) K) * g.val.left = (μ : K) • 1) :
    oκ Q g ^ 2 = 1 := by
  obtain ⟨hl2, hr2⟩ := pow_left_of_right_eq_one hg 2
  rw [← map_pow]
  have e : oκ Q (g ^ 2) = oκ Q (1 : similarityPairs Q) := by
    refine oκ_eq_of_left_eq (c := μ) (by rw [hr2]; rfl) ?_
    rw [hl2]
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_mul, GeneralLinearGroup.coe_scalar, pow_two, hsq]
    change _ = Matrix.scalar (Fin d) (μ : K) * 1
    rw [Matrix.mul_one, Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]
  rw [e, map_one]

variable [Finite K]

theorem kron_core (hK : ringChar K ≠ 2) {R : GL (Fin (2 * n)) K}
    (hR : (R : Matrix (Fin (2 * n)) (Fin (2 * n)) K)ᵀ = R) (hker : OKer (oQ R))
    (hinj : Function.Injective (MulAut.conj : StatedProj (matrixDerived (oQ R)) →*
      MulAut (StatedProj (matrixDerived (oQ R)))))
    {B : Subgroup (MulAut (StatedProj (matrixDerived (oQ R))))}
    (hB : (MulAut.conj : StatedProj (matrixDerived (oQ R)) →*
      MulAut (StatedProj (matrixDerived (oQ R)))).range ≤ B)
    {g : similarityPairs (oQ R)} (hg1 : g.val.right = 1) {c : K} (hc : c ≠ 0)
    (hA2 : (g.val.left : Matrix (Fin (2 * n)) (Fin (2 * n)) K) * g.val.left = c • 1)
    (hcd : CompData ⁅isoCent R g.val.left, isoCent R g.val.left⁆)
    {I₀ : Finset (Fin n)} (hI₀ : 3 ≤ I₀.card)
    (hrefl : ∀ i ∈ I₀, kronGL K n (reflGL i) ∈ isoCent R g.val.left)
    (hrot : ∀ i ∈ I₀, ∀ j ∈ I₀, ∀ (hij : i ≠ j) (a b : K) (hab : a ^ 2 + b ^ 2 = 1),
      kronGL K n (rotGL i j hij hab) ∈ isoCent R g.val.left)
    {g' : similarityPairs (oQ R)} (hy : oκ _ g' ∈ oddCoreIn B (oκ _ g)) :
    g'.val.right = 1 ∧
      (g'.val.left : Matrix (Fin (2 * n)) (Fin (2 * n)) K) * g.val.left =
        (g.val.left : Matrix (Fin (2 * n)) (Fin (2 * n)) K) * g'.val.left ∧
      (∀ X ∈ ⁅isoCent R g.val.left, isoCent R g.val.left⁆,
        (g'.val.left : Matrix (Fin (2 * n)) (Fin (2 * n)) K) *
            (X : Matrix (Fin (2 * n)) (Fin (2 * n)) K) =
          (X : Matrix (Fin (2 * n)) (Fin (2 * n)) K) * g'.val.left) ∧
      ∀ i ∈ I₀, ∀ j ∈ I₀, i ≠ j →
        (g'.val.left : Matrix (Fin (2 * n)) (Fin (2 * n)) K) * kronI K n (signMat K {i, j}) =
          kronI K n (signMat K {i, j}) * g'.val.left := by
  have hodd := odd_orderOf_of_mem_oddCoreIn hy
  have hτm : g'.val.right ^ orderOf (oκ _ g') = 1 := hker.right_pow_eq_one (pow_orderOf_eq_one _)
  have hfix := fun X (hX : X ∈ ⁅isoCent R g.val.left, isoCent R g.val.left⁆) =>
    cent_fix hK hR hinj hB hg1 hcd hy hX
  have hcomm2 : ∀ X Y : GL (Fin n) K, kronGL K n X ∈ isoCent R g.val.left →
      kronGL K n Y ∈ isoCent R g.val.left →
      kronGL K n ⁅X, Y⁆ ∈ ⁅isoCent R g.val.left, isoCent R g.val.left⁆ := by
    intro X Y hX hY
    rw [map_commutatorElement]
    exact commutator_mem_commutator hX hY
  obtain ⟨i, hi, j, hj, hij⟩ : ∃ i ∈ I₀, ∃ j ∈ I₀, i ≠ j := by
    obtain ⟨i, hi⟩ := Finset.card_pos.1 (by omega : 0 < I₀.card)
    obtain ⟨j, hj⟩ := Finset.card_pos.1 (by
      have := Finset.pred_card_le_card_erase (s := I₀) (a := i); omega : 0 < (I₀.erase i).card)
    exact ⟨i, hi, j, (Finset.mem_erase.1 hj).2, Ne.symm (Finset.mem_erase.1 hj).1⟩
  have hτ1 : g'.val.right = 1 := by
    refine tau_eq_one_of_kron (D := g'.val.left) hK hij hodd hτm fun a b hab => ?_
    have e := hfix _ (hcomm2 _ _ (hrefl i hi) (hrot i hi j hj hij a b hab))
    rw [coe_kronGL] at e
    exact e
  have hfix1 : ∀ X ∈ ⁅isoCent R g.val.left, isoCent R g.val.left⁆,
      (g'.val.left : Matrix (Fin (2 * n)) (Fin (2 * n)) K) *
          (X : Matrix (Fin (2 * n)) (Fin (2 * n)) K) =
        (X : Matrix (Fin (2 * n)) (Fin (2 * n)) K) * g'.val.left := by
    intro X hX
    have e := hfix X hX
    rw [hτ1, show (X : Matrix (Fin (2 * n)) (Fin (2 * n)) K).map ⇑(1 : K ≃+* K) = X from by
      ext; rfl] at e
    calc (g'.val.left : Matrix (Fin (2 * n)) (Fin (2 * n)) K) *
          (X : Matrix (Fin (2 * n)) (Fin (2 * n)) K) =
        (g'.val.left : Matrix (Fin (2 * n)) (Fin (2 * n)) K) *
          (X : Matrix (Fin (2 * n)) (Fin (2 * n)) K) *
          (((g'.val.left⁻¹ : GL (Fin (2 * n)) K) : Matrix (Fin (2 * n)) (Fin (2 * n)) K) *
            (g'.val.left : Matrix (Fin (2 * n)) (Fin (2 * n)) K)) := by
          rw [← Units.val_mul (g'.val.left⁻¹), inv_mul_cancel, Units.val_one, Matrix.mul_one]
      _ = (X : Matrix (Fin (2 * n)) (Fin (2 * n)) K) * g'.val.left := by
          rw [← Matrix.mul_assoc, e]
  have hd : 0 < 2 * n := by
    have := I₀.card_le_univ
    rw [Fintype.card_fin] at this
    omega
  refine ⟨hτ1, commute_of_odd_gen hd hker hg1 hτ1 hA2 hc hodd (commute_of_mem_oddCoreIn hy),
    hfix1, fun i' hi' j' hj' hij' => ?_⟩
  have h01 : (0 : K) ^ 2 + (1 : K) ^ 2 = 1 := by ring
  have hm := hcomm2 _ _ (hrefl i' hi') (hrot i' hi' j' hj' hij' 0 1 h01)
  have e := hfix1 _ hm
  rwa [coe_kronGL, signMat_pair_eq_commutator] at e

end CFSG.ComponentClassification.Burgoyne.O
