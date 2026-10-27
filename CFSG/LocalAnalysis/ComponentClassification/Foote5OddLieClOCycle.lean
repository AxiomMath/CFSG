module

public import CFSG.LocalAnalysis.ComponentClassification.Foote5OddLiePSLGrPerm
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneOKronElts
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneOThreeTools
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.ComponentClassification.Foote5.OddLieCore

open Matrix CFSG Subgroup CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.Burgoyne.Proj CFSG.ComponentClassification.Burgoyne.O
open CFSG.ComponentClassification.Burgoyne.PSL (diagGL coe_diagGL signMat signMat_mul_self)
open scoped commutatorElement

variable {K : Type} [Field K] {d : ℕ}

theorem ClO.permGL_signGL_conj (ρ : Equiv.Perm (Fin d)) (M : Finset (Fin d)) :
    ((permGL K d ρ * signGL K M * (permGL K d ρ)⁻¹ : GL (Fin d) K) :
      Matrix (Fin d) (Fin d) K) = diagonal fun x => if ρ⁻¹ x ∈ M then (-1 : K) else 1 := by
  rw [← map_inv, Units.val_mul, Units.val_mul, coe_signGL]
  change Matrix.permMatrixHom (R := K) ρ * signMat K M * Matrix.permMatrixHom (R := K) ρ⁻¹ = _
  rw [← Gr.permMatrixHom_transpose, signMat, Gr.permMatrixHom_diagonal]

theorem ClO.permGL_mem_isometry {w : Fin d → K} (hw : ∀ i, w i ≠ 0) (σ : Equiv.Perm (Fin d))
    (hσ : ∀ x, w (σ x) = w x) :
    permGL K d σ ∈ CatalogueBGraphForm.isometryGroup d K (diagGL hw) := by
  rw [CatalogueBGraphForm.mem_isometryGroup]
  change (Matrix.permMatrixHom (R := K) σ)ᵀ * (diagGL hw : Matrix (Fin d) (Fin d) K) *
    Matrix.permMatrixHom (R := K) σ = (diagGL hw : Matrix (Fin d) (Fin d) K)
  have hP : Matrix.permMatrixHom (R := K) σ = (Matrix.permMatrixHom (R := K) σ⁻¹)ᵀ := by
    rw [Gr.permMatrixHom_transpose, inv_inv]
  rw [Gr.permMatrixHom_transpose, hP, coe_diagGL, Gr.permMatrixHom_diagonal]
  congr 1
  ext x
  rw [inv_inv]
  exact hσ x

theorem ClO.permGL_cycle_mem (h2 : (2 : K) ≠ 0) {w : Fin d → K} (hw : ∀ i, w i ≠ 0)
    {a b c : Fin d} (hwab : w a = w b) (hwac : w a = w c) :
    permGL K d ⁅Equiv.swap a b, Equiv.swap a c⁆ ∈ matrixDerived (oQ (diagGL hw)) := by
  rw [matrixDerived_oQ h2 _ (diagGL_transpose hw), map_commutatorElement]
  have hsw : ∀ x y : Fin d, w x = w y → ∀ z, w (Equiv.swap x y z) = w z := by
    intro x y hxy z
    rw [Equiv.swap_apply_def]
    split_ifs with h1 h2'
    · rw [h1, hxy]
    · rw [h2', hxy]
    · rfl
  exact commutator_mem_commutator (ClO.permGL_mem_isometry hw _ (hsw a b hwab))
    (ClO.permGL_mem_isometry hw _ (hsw a c hwac))

theorem ClO.kappa_fix_of_commute (h2 : (2 : K) ≠ 0) {w : Fin d → K} (hw : ∀ i, w i ≠ 0)
    {J : Finset (Fin d)} (X : matrixDerived (oQ (diagGL hw)))
    (hX : signGL K J * (X : GL (Fin d) K) = (X : GL (Fin d) K) * signGL K J) :
    oκ _ (sgnPair h2 hw J) (projH _ X) = projH _ X := by
  rw [kappa_lift]
  congr 1
  apply Subtype.ext
  change ((matrixDerivedConjugation _ (sgnPair h2 hw J) X : matrixDerived (oQ (diagGL hw))) :
    GL (Fin d) K) = X
  rw [sgnPair, coe_conj_linPair, hX, mul_inv_cancel_right]

theorem ClO.conj_mem_of_three (hK : ringChar K ≠ 2) {w : Fin d → K} (hw : ∀ i, w i ≠ 0)
    {J : Finset (Fin d)}
    {Ro : Subgroup (MulAut (StatedProj (matrixDerived (oQ (diagGL hw)))))}
    (hRc : ∀ s, oκ _ (sgnPair (Ring.two_ne_zero hK) hw J) s = s → Odd (orderOf s) →
      ∀ y ∈ Ro, MulAut.conj s * y * (MulAut.conj s)⁻¹ ∈ Ro)
    (X : matrixDerived (oQ (diagGL hw)))
    (hX : signGL K J * (X : GL (Fin d) K) = (X : GL (Fin d) K) * signGL K J) (hX3 : X ^ 3 = 1)
    {z : MulAut (StatedProj (matrixDerived (oQ (diagGL hw))))} (hz : z ∈ Ro) :
    conjProjH _ X * z * (conjProjH _ X)⁻¹ ∈ Ro := by
  refine hRc _ (ClO.kappa_fix_of_commute (Ring.two_ne_zero hK) hw X hX) ?_ z hz
  exact Odd.of_dvd_nat (by decide : Odd 3)
    (orderOf_dvd_of_pow_eq_one (by rw [← map_pow, hX3, map_one]))

theorem ClO.signGL_comm (J N : Finset (Fin d)) :
    signGL K J * signGL K N = signGL K N * signGL K J := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, coe_signGL, coe_signGL]
  simp only [signMat]
  rw [diagonal_mul_diagonal, diagonal_mul_diagonal]
  congr 1
  ext x
  ring

theorem ClO.permGL_signGL_comm (ρ : Equiv.Perm (Fin d)) {M M' : Finset (Fin d)}
    (hM' : ∀ x, x ∈ M' ↔ ¬ (ρ⁻¹ x ∈ M ↔ x ∈ M)) :
    permGL K d ρ * (signGL K M * (permGL K d ρ)⁻¹ * (signGL K M)⁻¹) = signGL K M' := by
  apply Units.ext
  rw [show permGL K d ρ * (signGL K M * (permGL K d ρ)⁻¹ * (signGL K M)⁻¹) =
    (permGL K d ρ * signGL K M * (permGL K d ρ)⁻¹) * signGL K M by
      rw [signGL_inv]; group, Units.val_mul, ClO.permGL_signGL_conj, coe_signGL]
  simp only [signMat]
  rw [diagonal_mul_diagonal]
  congr 1
  ext x
  by_cases h1 : x ∈ M' <;> by_cases h2 : ρ⁻¹ x ∈ M <;> by_cases h3 : x ∈ M <;> simp_all

theorem ClO.conj_mem_of_cycle [Finite K] (hK : ringChar K ≠ 2) {w : Fin d → K}
    (hw : ∀ i, w i ≠ 0) {J : Finset (Fin d)}
    {Ro : Subgroup (MulAut (StatedProj (matrixDerived (oQ (diagGL hw)))))}
    (hRc : ∀ s, oκ _ (sgnPair (Ring.two_ne_zero hK) hw J) s = s → Odd (orderOf s) →
      ∀ y ∈ Ro, MulAut.conj s * y * (MulAut.conj s)⁻¹ ∈ Ro)
    {ρ : Equiv.Perm (Fin d)} (hρ3 : ρ ^ 3 = 1) (hρJ : ∀ x, ρ⁻¹ x ∈ J ↔ x ∈ J)
    (hρH : permGL K d ρ ∈ matrixDerived (oQ (diagGL hw))) {M M' : Finset (Fin d)}
    (hMH : signGL K M ∈ matrixDerived (oQ (diagGL hw)))
    (hM' : ∀ x, x ∈ M' ↔ ¬ (ρ⁻¹ x ∈ M ↔ x ∈ M)) :
    ∀ y ∈ Ro, oκ _ (sgnPair (Ring.two_ne_zero hK) hw M') * y *
      (oκ _ (sgnPair (Ring.two_ne_zero hK) hw M'))⁻¹ ∈ Ro := by
  intro y hy
  have hPJ : signGL K J * permGL K d ρ = permGL K d ρ * signGL K J := by
    have e : permGL K d ρ * signGL K J * (permGL K d ρ)⁻¹ = signGL K J := by
      apply Units.ext
      rw [ClO.permGL_signGL_conj, coe_signGL, signMat]
      congr 1
      ext x
      simp only [hρJ x]
    calc signGL K J * permGL K d ρ =
        (permGL K d ρ * signGL K J * (permGL K d ρ)⁻¹) * permGL K d ρ := by rw [e]
      _ = permGL K d ρ * signGL K J := by group
  have hPJi : signGL K J * (permGL K d ρ)⁻¹ = (permGL K d ρ)⁻¹ * signGL K J := by
    calc signGL K J * (permGL K d ρ)⁻¹ =
        (permGL K d ρ)⁻¹ * (permGL K d ρ * signGL K J) * (permGL K d ρ)⁻¹ := by group
      _ = (permGL K d ρ)⁻¹ * (signGL K J * permGL K d ρ) * (permGL K d ρ)⁻¹ := by rw [hPJ]
      _ = (permGL K d ρ)⁻¹ * signGL K J := by group
  have hSJi : signGL K J * (signGL K M)⁻¹ = (signGL K M)⁻¹ * signGL K J := by
    rw [signGL_inv, ClO.signGL_comm]
  set P : matrixDerived (oQ (diagGL hw)) := ⟨permGL K d ρ, hρH⟩ with hP
  set S : matrixDerived (oQ (diagGL hw)) := ⟨signGL K M, hMH⟩ with hS
  have hP3 : P ^ 3 = 1 := Subtype.ext (by
    rw [SubgroupClass.coe_pow, hP, ← map_pow, hρ3, map_one]
    rfl)
  have hY3 : (S * P⁻¹ * S⁻¹) ^ 3 = 1 := by
    rw [conj_pow, inv_pow, hP3, inv_one, mul_one, mul_inv_cancel]
  have hYc : signGL K J * ((S * P⁻¹ * S⁻¹ : matrixDerived (oQ (diagGL hw))) : GL (Fin d) K) =
      ((S * P⁻¹ * S⁻¹ : matrixDerived (oQ (diagGL hw))) : GL (Fin d) K) * signGL K J := by
    change signGL K J * (signGL K M * (permGL K d ρ)⁻¹ * (signGL K M)⁻¹) =
      (signGL K M * (permGL K d ρ)⁻¹ * (signGL K M)⁻¹) * signGL K J
    rw [← mul_assoc, ← mul_assoc, ClO.signGL_comm J M, mul_assoc (signGL K M), hPJi,
      ← mul_assoc, mul_assoc _ _ (signGL K M)⁻¹, hSJi, ← mul_assoc]
  have hM'mat : signGL K M' = ((P * (S * P⁻¹ * S⁻¹) : matrixDerived (oQ (diagGL hw))) :
      GL (Fin d) K) := (ClO.permGL_signGL_comm ρ hM').symm
  have hM'H : signGL K M' ∈ matrixDerived (oQ (diagGL hw)) := by
    rw [hM'mat]
    exact (P * (S * P⁻¹ * S⁻¹)).2
  have hκ : oκ _ (sgnPair (Ring.two_ne_zero hK) hw M') =
      conjProjH _ (P * (S * P⁻¹ * S⁻¹)) := by
    rw [sgnPair, oκ_linPair_eq_conj _ hM'H]
    congr 1
    exact Subtype.ext hM'mat
  rw [hκ, map_mul]
  have h1 := ClO.conj_mem_of_three hK hw hRc P hPJ hP3
    (ClO.conj_mem_of_three hK hw hRc _ hYc hY3 hy)
  have e : ∀ a b : MulAut (StatedProj (matrixDerived (oQ (diagGL hw)))),
      a * b * y * (a * b)⁻¹ = a * (b * y * b⁻¹) * a⁻¹ := fun a b => by group
  rw [e]
  exact h1

end CFSG.ComponentClassification.Foote5.OddLieCore
