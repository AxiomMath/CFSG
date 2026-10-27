module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneOEvenPc
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneOSplitMain
public import Certificates.Kernel.ThCent.Leaves
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneOField
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneUGraphCore
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneUGraphDescent
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneUInnerPaired

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.O

open Matrix CFSG Subgroup CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.TBLit
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.Burgoyne.Proj

variable {K : Type} [Field K] {d : ℕ}

theorem inner_even_data (h2 : (2 : K) ≠ 0) {R : GL (Fin d) K}
    (hR : (R : Matrix (Fin d) (Fin d) K)ᵀ = R) (hd : 0 < d) (hker : OKer (oQ R))
    {g : similarityPairs (oQ R)} (hg1 : g.val.right = 1) (hgg : oκ (oQ R) (g * g) = 1) :
    ∃ c : K, c ≠ 0 ∧
      (g.val.left : Matrix (Fin d) (Fin d) K) * g.val.left = c • 1 ∧
      ((g.val.left : Matrix (Fin d) (Fin d) K)ᵀ * R =
          (1 : K) • ((R : Matrix (Fin d) (Fin d) K) * g.val.left) ∨
        (g.val.left : Matrix (Fin d) (Fin d) K)ᵀ * R =
          (-1 : K) • ((R : Matrix (Fin d) (Fin d) K) * g.val.left)) ∧
      ((g.val.left : Matrix (Fin d) (Fin d) K)ᵀ * R * g.val.left = c • R ∨
        (g.val.left : Matrix (Fin d) (Fin d) K)ᵀ * R * g.val.left = (-c) • R) := by
  set A := (g.val.left : Matrix (Fin d) (Fin d) K) with hA
  set Rm := (R : Matrix (Fin d) (Fin d) K) with hRm
  obtain ⟨-, c, hc⟩ := hker _ hgg
  have hAA : A * A = (c : K) • 1 := by
    have hl : (g * g).val.left = g.val.left * g.val.left := by
      change (g.val * g.val).left = _
      rw [SemidirectProduct.mul_left, hg1, map_one, MulAut.one_apply]
    have e := congrArg Units.val hc
    rw [hl, Units.val_mul, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
      ← Matrix.smul_one_eq_diagonal] at e
    exact e.symm
  obtain ⟨μ, hμ⟩ := (mem_similarityPairs_oQ h2 R hR g.val).1 g.2
  rw [hg1, show (R : Matrix (Fin d) (Fin d) K).map ⇑(1 : K ≃+* K) = R from by ext; rfl] at hμ
  have hc0 : (c : K) ≠ 0 := c.ne_zero
  have hAR : Aᵀ * Rm = ((μ : K) / c) • (Rm * A) := by
    have e : Aᵀ * Rm * (A * A) = (μ : K) • (Rm * A) := by
      rw [← Matrix.mul_assoc, hμ, Matrix.smul_mul]
    rw [hAA, Matrix.mul_smul, Matrix.mul_one] at e
    rw [div_eq_mul_inv, mul_comm, ← smul_smul, ← e, smul_smul, inv_mul_cancel₀ hc0, one_smul]
  have hR0 : Rm ≠ 0 := by
    intro h0
    have : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
    have := congrArg Matrix.det h0
    rw [det_zero] at this
    exact (Matrix.isUnits_det_units R).ne_zero this
  have hμc : (μ : K) * μ = c * c := by
    have hμ' : Aᵀ * Rm * A = (μ : K) • Rm := hμ
    have e1 : (A * A)ᵀ * Rm * (A * A) = ((μ : K) * μ) • Rm := by
      have : (A * A)ᵀ * Rm * (A * A) = Aᵀ * (Aᵀ * Rm * A) * A := by
        rw [transpose_mul]
        simp only [Matrix.mul_assoc]
      rw [this, hμ', Matrix.mul_smul, Matrix.smul_mul, hμ', smul_smul]
    rw [hAA, transpose_smul, transpose_one, Matrix.smul_mul, Matrix.one_mul, Matrix.smul_mul,
      Matrix.mul_smul, Matrix.mul_one, smul_smul] at e1
    have e2 : ((c : K) * c - μ * μ) • Rm = 0 := by rw [sub_smul, e1, sub_self]
    rcases smul_eq_zero.1 e2 with h | h
    · exact (sub_eq_zero.1 h).symm
    · exact absurd h hR0
  have hcases : (μ : K) = c ∨ (μ : K) = -c := by
    have : ((μ : K) - c) * (μ + c) = 0 := by linear_combination hμc
    rcases mul_eq_zero.1 this with h | h
    · exact Or.inl (sub_eq_zero.1 h)
    · exact Or.inr (eq_neg_of_add_eq_zero_left h)
  refine ⟨c, hc0, hAA, ?_, ?_⟩
  · rcases hcases with h | h
    · left
      rw [hAR, h, div_self hc0]
    · right
      rw [hAR, h, neg_div, div_self hc0]
  · rcases hcases with h | h
    · left
      rw [hμ, h]
    · right
      rw [hμ, h]

variable [Finite K]

theorem inner_even_propAConclusion (hK : ringChar K ≠ 2) {ℓ e : ℕ} (hℓ : ℓ.Prime)
    (hKc : Nat.card K = ℓ ^ e) {n : ℕ} (hn : 4 ≤ n) {R : GL (Fin (2 * n)) K}
    (hR : (R : Matrix (Fin (2 * n)) (Fin (2 * n)) K)ᵀ = R)
    (hker : OKer (oQ R)) {X : Type} [Group X] [Finite X]
    (hsimple : IsSimpleGroup (GeneralizedFitting.subgroup X))
    (hnab : ∃ a b : GeneralizedFitting.subgroup X, a * b ≠ b * a)
    (θ : GeneralizedFitting.subgroup X ≃* StatedProj (matrixDerived (oQ R)))
    {t : X} (hsurj : OSurjX θ t) (ht : orderOf t = 2) {g : similarityPairs (oQ R)}
    (hg1 : g.val.right = 1)
    (htg : socleAction θ t = oκ _ g) {Y : Subgroup X} (hY : Y ≠ ⊥)
    (hYO : Y ≤ oddCentralizerCore t) : PropAConclusion X t Y := by
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
      exact inner_split_propAConclusion hK (by omega) hR hker hsimple hnab θ hsurj ht htg hA' hκ
        hA'R hA'2 hY hYO
    · exact orth2_propAConclusion hK hn hR hker hsimple hnab θ hsurj hg1 htg hsq hA2 hε hY hYO
  · exact pc_propAConclusion hK hℓ hKc hn hR hker hsimple hnab θ hsurj hg1 htg hc0 hA2 hε hY hYO

end CFSG.ComponentClassification.Burgoyne.O
