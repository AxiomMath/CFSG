module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierLinearTwo
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGL2DeterminantSquare
public import CFSG.LocalAnalysis.ComponentInitial.DiagonalSemilinear

public noncomputable section

namespace CFSG.LocalAnalysis.ComponentInitial

open CFSG.ComponentClassification.CatalogueSchreierLinearTwo CFSG.GorensteinWalter
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)

@[expose] def diagonalGLHom (K : Type) [Field K] : Kˣ →* Matrix.GeneralLinearGroup (Fin 2) K where
  toFun := diagonalGL K
  map_one' := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [diagonalGL]
  map_mul' s t := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [diagonalGL, Matrix.mul_apply, Fin.sum_univ_two]

theorem card_pgl_quotient_psl_dvd (K : Type) [Field K] [Finite K] :
    Nat.card (PGL2 K ⧸ (Matrix.ProjectiveSpecialLinearGroup.toPGL
      (n := Fin 2) (R := K)).range) ∣ Nat.gcd 2 (Nat.card K - 1) := by
  set R := (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := K)).range
  set ψ : Kˣ →* PGL2 K ⧸ R :=
    (QuotientGroup.mk' R).comp (Matrix.ProjGenLinGroup.mk.comp (diagonalGLHom K))
  have hdet : ∀ s : Kˣ, Matrix.GeneralLinearGroup.det (diagonalGLHom K s) = s :=
    diagonalGL_det K
  have hψ : Function.Surjective ψ := by
    intro x
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective R x
    obtain ⟨A, rfl⟩ := Matrix.ProjGenLinGroup.mk_surjective y
    refine ⟨Matrix.GeneralLinearGroup.det A, ?_⟩
    change QuotientGroup.mk' R (Matrix.ProjGenLinGroup.mk
      (diagonalGLHom K (Matrix.GeneralLinearGroup.det A))) = QuotientGroup.mk' R _
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq, ← map_inv, ← map_mul,
      pgl2_mk_mem_psl2_range_iff_det_isSquare, map_mul, map_inv, hdet, inv_mul_cancel,
      Units.val_one]
    exact ⟨1, (mul_one 1).symm⟩
  have hsq : ∀ x : PGL2 K ⧸ R, x ^ 2 = 1 := by
    intro x
    obtain ⟨s, rfl⟩ := hψ x
    rw [← map_pow]
    change QuotientGroup.mk' R (Matrix.ProjGenLinGroup.mk (diagonalGLHom K (s ^ 2))) = 1
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
      pgl2_mk_mem_psl2_range_iff_det_isSquare, hdet, Units.val_pow_eq_pow_val]
    exact ⟨s, sq (s : K)⟩
  have : IsCyclic (PGL2 K ⧸ R) := isCyclic_of_surjective ψ hψ
  have h2 : Nat.card (PGL2 K ⧸ R) ∣ 2 := by
    rw [← IsCyclic.exponent_eq_card]
    exact Monoid.exponent_dvd_of_forall_pow_eq_one hsq
  have hq : Nat.card (PGL2 K ⧸ R) ∣ Nat.card K - 1 := by
    rw [Nat.card_eq_card_units_add_one K, Nat.add_sub_cancel]
    exact Subgroup.card_dvd_of_surjective (f := ψ) hψ
  exact Nat.dvd_gcd h2 hq

theorem linear_two_outer_order_divisor {p f : ℕ} (hp : p.Prime) (K : Type) [Field K]
    (hK : Nat.card K = p ^ f) :
    Nat.card (Outer (Matrix.ProjectiveSpecialLinearGroup (Fin 2) K)) ∣
        f * Nat.gcd 2 (p ^ f - 1) ∧
      ∀ (G : Type) [Group G], Nonempty (G ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) K) →
        Nat.card (Outer G) ∣ f * Nat.gcd 2 (p ^ f - 1) := by
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; exact (pow_pos hp.pos f).ne')
  have hGD := coordinateG_le_D K
  have hDE := coordinateD_le_E K
  have hEG : Nat.card (CoordinateQuotientEG K) =
      Nat.card (CoordinateQuotientDG K) * Nat.card (CoordinateQuotientED K) :=
    (Subgroup.relIndex_mul_relIndex _ _ _ hGD hDE).symm
  have hED : Nat.card (CoordinateQuotientED K) = f := by
    rw [Nat.card_congr (coordinateEDQuotientEquivField K).toEquiv]
    exact (card_ringAut_and_isCyclic hp K hK).1
  have hDG : Nat.card (CoordinateQuotientDG K) ∣ Nat.gcd 2 (p ^ f - 1) := by
    rw [← Nat.card_congr (pglQuotientEquivCoordinateDG K).toEquiv, ← hK]
    exact card_pgl_quotient_psl_dvd K
  have hout : Nat.card (Outer (Matrix.ProjectiveSpecialLinearGroup (Fin 2) K)) ∣
      f * Nat.gcd 2 (p ^ f - 1) := by
    rw [← Nat.card_congr (coordinateOuterEquivPSL K).toEquiv,
      ← Nat.card_congr (coordinateOuterQuotientEquiv K).toEquiv, hEG, hED, mul_comm]
    exact Nat.mul_dvd_mul_left f hDG
  refine ⟨hout, fun G _ ⟨e⟩ => ?_⟩
  rw [Nat.card_congr
    (CFSG.ComponentClassification.OuterAutomorphisms.equivalence e).toEquiv]
  exact hout

end CFSG.LocalAnalysis.ComponentInitial
