module

public import CFSG.RankThree.Classical2.OrthogonalIsotropicUnipotent
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalThreeSimilarityGroups

public section

namespace CFSG.LinearAlgebra

open Module QuadraticMap

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

private theorem orthDerived_smul_eq (Q : QuadraticForm K V) {d : K} (hd : d ≠ 0) :
    CFSG.RankThree.Classical2.orthDerived (d • Q) = CFSG.RankThree.Classical2.orthDerived Q := by
  have hO : TauCeti.QuadraticMap.orthogonalGroup (d • Q) =
      TauCeti.QuadraticMap.orthogonalGroup Q :=
    CFSG.ComponentClassification.CatalogueBOrthogonalThreeSimilarity.orthogonalGroup_unit_smul
      Q (Units.mk0 d hd)
  rw [show CFSG.RankThree.Classical2.orthDerived (d • Q) =
      ⁅TauCeti.QuadraticMap.orthogonalGroup (d • Q),
        TauCeti.QuadraticMap.orthogonalGroup (d • Q)⁆ from rfl,
    show CFSG.RankThree.Classical2.orthDerived Q =
      ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ from rfl,
    hO]

theorem exists_mem_orthDerived_double_sign_of_norm_eq (h2 : (2 : K) ≠ 0) {u v : V} {c : K}
    (hu : Q u = c) (hv : Q v = c) (hc : c ≠ 0) (huv : polar Q u v = 0) :
    ∃ g ∈ CFSG.RankThree.Classical2.orthDerived Q, g u = -u ∧ g v = -v ∧
      ∀ x, polar Q u x = 0 → polar Q v x = 0 → g x = x := by
  have hu' : (c⁻¹ • Q) u = 1 := by
    rw [smul_apply, hu, smul_eq_mul, inv_mul_cancel₀ hc]
  have hv' : (c⁻¹ • Q) v = 1 := by
    rw [smul_apply, hv, smul_eq_mul, inv_mul_cancel₀ hc]
  have hpol : ∀ x y : V, polar (c⁻¹ • Q) x y = c⁻¹ * polar Q x y := by
    intro x y
    rw [QuadraticMap.polar, QuadraticMap.polar, smul_apply, smul_apply, smul_apply,
      smul_eq_mul, smul_eq_mul, smul_eq_mul]
    ring
  have huv' : polar (c⁻¹ • Q) u v = 0 := by rw [hpol, huv, mul_zero]
  obtain ⟨g, hg, hgu, hgv, hgx⟩ :=
    CFSG.RankThree.Classical2.exists_mem_orthDerived_double_sign (Q := c⁻¹ • Q) h2 hu' hv' huv'
  refine ⟨g, ?_, hgu, hgv, fun x hx hx' => hgx x ?_ ?_⟩
  · rwa [orthDerived_smul_eq Q (inv_ne_zero hc)] at hg
  · rw [hpol, hx, mul_zero]
  · rw [hpol, hx', mul_zero]

theorem exists_mem_orthDerived_double_sign_of_sq_mul (h2 : (2 : K) ≠ 0) {u v : V} {b c t : K}
    (hu : Q u = b) (hv : Q v = c) (hb : b ≠ 0) (ht : t ≠ 0) (hbc : b = t ^ 2 * c)
    (huv : polar Q u v = 0) :
    ∃ g ∈ CFSG.RankThree.Classical2.orthDerived Q, g u = -u ∧ g v = -v ∧
      ∀ x, polar Q u x = 0 → polar Q v x = 0 → g x = x := by
  have hw : Q (t • v) = b := by
    rw [QuadraticMap.map_smul, hv, hbc, smul_eq_mul]
    ring
  have hpw : polar Q u (t • v) = 0 := by
    rw [polar_smul_right, huv, smul_zero]
  obtain ⟨g, hg, hgu, hgw, hgx⟩ :=
    exists_mem_orthDerived_double_sign_of_norm_eq (Q := Q) h2 hu hw hb hpw
  have hgv : g v = -v := by
    have h1 : g (t • v) = t • (-v) := by rw [hgw, smul_neg]
    rw [map_smul] at h1
    have h2 := congrArg (fun z => t⁻¹ • z) h1
    simpa [smul_smul, inv_mul_cancel₀ ht] using h2
  refine ⟨g, hg, hgu, hgv, fun x hx hx' => hgx x hx ?_⟩
  rw [polar_smul_left, hx', smul_zero]

end CFSG.LinearAlgebra

end
