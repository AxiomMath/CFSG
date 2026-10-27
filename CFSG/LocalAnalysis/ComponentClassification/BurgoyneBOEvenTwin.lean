module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneBOSplitTwin
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneOEvenInner

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.O

open Matrix CFSG Subgroup CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.TBLit
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.Burgoyne.Proj

variable {K : Type} [Field K] [Finite K]

theorem inner_even_twin (hK : ringChar K ≠ 2) {n : ℕ} (hn : 4 ≤ n) {R : GL (Fin (2 * n)) K}
    (hR : (R : Matrix (Fin (2 * n)) (Fin (2 * n)) K)ᵀ = R)
    (hker : OKer (oQ R)) {X : Type} [Group X] [Finite X]
    (hsimple : IsSimpleGroup (GeneralizedFitting.subgroup X))
    (hnab : ∃ a b : GeneralizedFitting.subgroup X, a * b ≠ b * a)
    (θ : GeneralizedFitting.subgroup X ≃* StatedProj (matrixDerived (oQ R)))
    {t : X} (hsurj : OSurjX θ t) (ht : orderOf t = 2) {g : similarityPairs (oQ R)}
    (hg1 : g.val.right = 1) (htg : socleAction θ t = oκ _ g) :
    oddCentralizerCore t = ⊥ ∨ (5 ≤ Nat.card K ∧ TwinSliceData (Ring.two_ne_zero hK) θ t) ∨
      (g.val.left : Matrix (Fin (2 * n)) (Fin (2 * n)) K)ᵀ * R =
        (-1 : K) • ((R : Matrix (Fin (2 * n)) (Fin (2 * n)) K) * g.val.left) := by
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
  have hgg : oκ (oQ R) (g * g) = 1 := by
    rw [map_mul, ← htg, ← map_mul, ← pow_two,
      show t ^ 2 = 1 from by rw [← ht]; exact pow_orderOf_eq_one t, map_one]
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
      rcases inner_split_twin hK (by omega) hR hker hsimple hnab θ hsurj ht htg hA' hκ hA'R hA'2
        with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
    · exact Or.inl (orth2_oddCentralizerCore_eq_bot hK hn hR hker hsimple hnab θ hsurj hg1 htg
        hsq hA2 hε)
  · exact Or.inr (Or.inr hε)

end CFSG.ComponentClassification.Burgoyne.O
