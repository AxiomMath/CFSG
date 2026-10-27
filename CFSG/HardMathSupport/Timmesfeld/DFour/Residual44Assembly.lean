module

public import CFSG.HardMathSupport.Timmesfeld.DFour.Residual44

public section

namespace CFSG.HardMathSupport.Timmesfeld.DFour

open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open CFSG.HardMathSupport.Timmesfeld.DefChar CFSG.HardMathSupport.Timmesfeld.DefChar.Orth

theorem exists_lift_pow_eq_one {K : Type} [Field K] {d : ℕ} {Q : QuadraticForm K (Fin d → K)}
    (hQ : ∃ v, Q v ≠ 0) {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {g : matrixProjectiveDerived Q}
    (hg : orderOf g = p) :
    ∃ gh : matrixDerived Q, matrixProjectiveProjection Q gh = g ∧ gh ^ p = 1 := by
  obtain ⟨s0, c, hcc, rfl, hG, -⟩ := exists_lift hQ hp2 g hg
  have hodd : Odd p := (Fact.out : p.Prime).odd_of_ne_two hp2
  refine ⟨s0 ^ (p + 1), ?_, ?_⟩
  · rw [map_pow, pow_succ, ← hg, pow_orderOf_eq_one, one_mul]
  · have hcp : c ^ p = c := by
      obtain ⟨k, hk⟩ := hodd
      rw [hk, pow_succ, pow_mul, sq, hcc, one_pow, one_mul]
    have h1 : toE s0.val ^ p = c • 1 := by
      rw [smul_pow, hcp] at hG
      calc toE s0.val ^ p = c • (c • toE s0.val ^ p) := by rw [smul_smul, hcc, one_smul]
        _ = c • 1 := by rw [hG]
    have hcp1 : c ^ (p + 1) = 1 := by rw [pow_succ, hcp, hcc]
    apply Subtype.ext
    apply toE_injective
    rw [Subgroup.coe_pow, Subgroup.coe_pow, ← pow_mul, toE_pow, Subgroup.coe_one, toE_one,
      mul_comm, pow_mul, h1, smul_pow, one_pow, hcp1, one_smul]

theorem dFourPrimeCentralizerInImage_of_nonResidual44
    (h : ∀ (K : Type) [Field K] [Finite K] (p : ℕ) [Fact p.Prime] [CharP K p], p ≠ 2 →
      ∀ (g : matrixProjectiveDerived (coordinateQuadPlus 4 K))
        (gh : matrixDerived (coordinateQuadPlus 4 K)),
        matrixProjectiveProjection (coordinateQuadPlus 4 K) gh = g → gh ^ p = 1 →
        orderOf g = p → ¬ Residual44 gh →
        ∀ α : MulAut (matrixProjectiveDerived (coordinateQuadPlus 4 K)),
          (orderOf α).Coprime p → (∀ s, s * g = g * s → α s = s) →
            α ∈ matrixProjectiveImage (coordinateQuadPlus 4 K)) :
    DFourPrimeCentralizerInImage := by
  intro K _ _ p _ _ hp2 g hg α hcop hfix
  obtain ⟨-, hQ, -, -⟩ := coordinatePlusFour_facts (K := K) p
  obtain ⟨gh, hgh, hghp⟩ := exists_lift_pow_eq_one hQ hp2 hg
  by_cases hres : Residual44 gh
  · exact dFourResidual44_holds K p hp2 g gh hgh hghp hg hres α hcop hfix
  · exact h K p hp2 g gh hgh hghp hg hres α hcop hfix

end CFSG.HardMathSupport.Timmesfeld.DFour
