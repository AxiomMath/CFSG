module

public import CFSG.LocalAnalysis.ComponentClassification.Foote5OddLieClOEvenSplit
public import CFSG.LocalAnalysis.ComponentClassification.Foote5OddLieClOOrth2T
public import CFSG.LocalAnalysis.ComponentClassification.Foote5OddLieClOPc
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneOEvenInner

public section

namespace CFSG.ComponentClassification.Foote5.OddLieCore

open Matrix CFSG Subgroup CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.TBLit
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.Burgoyne.Proj CFSG.ComponentClassification.Burgoyne.O

variable {K : Type} [Field K] [Finite K]

theorem ClO.commute_inner_even (hK : ringChar K ≠ 2) {ℓ e : ℕ} (hℓ : ℓ.Prime)
    (hKc : Nat.card K = ℓ ^ e) {n : ℕ} (hn : 4 ≤ n) {R : GL (Fin (2 * n)) K}
    (hR : (R : Matrix (Fin (2 * n)) (Fin (2 * n)) K)ᵀ = R)
    (hker : OKer (oQ R)) (hsurj : OSurj (oQ R))
    (hinj : Function.Injective (MulAut.conj : StatedProj (matrixDerived (oQ R)) →*
      MulAut (StatedProj (matrixDerived (oQ R)))))
    {g : similarityPairs (oQ R)} (hg1 : g.val.right = 1) (hi : orderOf (oκ _ g) = 2)
    {Ro : Subgroup (MulAut (StatedProj (matrixDerived (oQ R))))} (hRodd : Odd (Nat.card Ro))
    (hRi : ∀ y ∈ Ro, y * oκ _ g = oκ _ g * y)
    (hRc : ∀ s, oκ _ g s = s → Odd (orderOf s) → ∀ y ∈ Ro,
      MulAut.conj s * y * (MulAut.conj s)⁻¹ ∈ Ro) :
    ∀ r₁ ∈ Ro, ∀ r₂ ∈ Ro, r₁ * r₂ = r₂ * r₁ := by
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
  have hgg : oκ (oQ R) (g * g) = 1 := by
    have hp := pow_orderOf_eq_one (oκ (oQ R) g)
    rw [hi] at hp
    rw [map_mul, ← pow_two]
    exact hp
  obtain ⟨c, hc0, hA2, hε, hμ⟩ := inner_even_data h2 hR (by omega) hker hg1 hgg
  rcases hε with hε | hε
  · by_cases hsq : IsSquare c
    ·
      obtain ⟨s, hs⟩ := hsq
      have hs0 : s ≠ 0 := by
        rintro rfl
        exact hc0 (by rw [hs, mul_zero])
      have hμc : (g.val.left : Matrix (Fin (2 * n)) (Fin (2 * n)) K)ᵀ * R * g.val.left =
          c • (R : Matrix (Fin (2 * n)) (Fin (2 * n)) K) := by
        rcases hμ with h | h
        · exact h
        · exfalso
          have e1 : (g.val.left : Matrix (Fin (2 * n)) (Fin (2 * n)) K)ᵀ * R * g.val.left =
              c • (R : Matrix (Fin (2 * n)) (Fin (2 * n)) K) := by
            rw [hε, one_smul, Matrix.mul_assoc, hA2, Matrix.mul_smul, Matrix.mul_one]
          rw [h] at e1
          have e2 : ((2 : K) * c) • (R : Matrix (Fin (2 * n)) (Fin (2 * n)) K) = 0 := by
            rw [mul_smul, two_smul]
            nth_rewrite 1 [← e1]
            rw [neg_smul, neg_add_cancel]
          rcases smul_eq_zero.1 e2 with h' | h'
          · exact mul_ne_zero h2 hc0 h'
          · have : Nonempty (Fin (2 * n)) := ⟨⟨0, by omega⟩⟩
            have := congrArg Matrix.det h'
            rw [det_zero] at this
            exact (Matrix.isUnits_det_units R).ne_zero this
      obtain ⟨A', hA'def⟩ : ∃ A' : GL (Fin (2 * n)) K,
          A' = GeneralLinearGroup.scalar (Fin (2 * n)) (Units.mk0 s hs0)⁻¹ * g.val.left :=
        ⟨_, rfl⟩
      have hA'c : (A' : Matrix (Fin (2 * n)) (Fin (2 * n)) K) =
          s⁻¹ • (g.val.left : Matrix (Fin (2 * n)) (Fin (2 * n)) K) := by
        rw [hA'def, Units.val_mul, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
          ← Matrix.smul_one_eq_diagonal, Matrix.smul_mul, Matrix.one_mul,
          Units.val_inv_eq_inv_val, Units.val_mk0]
      have hA'R : (A' : Matrix (Fin (2 * n)) (Fin (2 * n)) K)ᵀ * R * A' = R := by
        rw [hA'c, transpose_smul, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, hμc,
          smul_smul, smul_smul, hs]
        rw [show s⁻¹ * s⁻¹ * (s * s) = 1 by field_simp, one_smul]
      have hA'2 : (A' : Matrix (Fin (2 * n)) (Fin (2 * n)) K) * A' = 1 := by
        rw [hA'c, Matrix.smul_mul, Matrix.mul_smul, hA2, smul_smul, smul_smul, hs]
        rw [show s⁻¹ * s⁻¹ * (s * s) = 1 by field_simp, one_smul]
      have hA' : A' ∈ matrixIsometries (oQ R) :=
        (mem_matrixIsometries_oQ h2 R hR A').2
          ((CatalogueBGraphForm.mem_isometryGroup _ _ _ _).2 hA'R)
      have hκ : oκ _ g = oκ _ (linPair A' hA') := by
        refine oκ_eq_of_left_eq (c := Units.mk0 s hs0) (by rw [hg1, linPair_right]) ?_
        rw [linPair_left, hA'def, ← mul_assoc, ← map_mul, mul_inv_cancel, map_one, one_mul]
      exact ClO.commute_split_gen hK (by omega) hR hker hsurj hinj hi hRodd hRi hRc hA' hκ hA'R
        hA'2
    · exact ClO.commute_orth2 hK hn hR hker hsurj hinj hg1 hsq hA2 hε hRodd hRi hRc
  · exact ClO.commute_pc hK hℓ hKc hn hR hker hsurj hinj hg1 hc0 hA2 hε hRodd hRi hRc

end CFSG.ComponentClassification.Foote5.OddLieCore
