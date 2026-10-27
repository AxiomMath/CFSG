module

public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.GomiU42OddClPSLGraphAlt
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBLinearHigherBPureGraph
public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.GomiU42OddClPSLGraphBase

public section

namespace CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo

open Subgroup Module Matrix
open CFSG.ComponentClassification
open CFSG.ComponentClassification.CatalogueBGraphForm (isometryGroup)
open CFSG.ComponentClassification.CatalogueBLinearHigherB (matrixForm isometryGroupEquiv
  matrixForm_isAlt matrixForm_nondegenerate)

section AntiIsometry

variable {K : Type} [Field K]

theorem u42_exists_antiIsometry_sl4 (hodd : ringChar K ≠ 2) (R : GL (Fin 4) K)
    (hR : (R : Matrix (Fin 4) (Fin 4) K)ᵀ = -(R : Matrix (Fin 4) (Fin 4) K)) :
    ∃ M : Matrix (Fin 4) (Fin 4) K, M.det = 1 ∧
      Mᵀ * (R : Matrix (Fin 4) (Fin 4) K) * M = -(R : Matrix (Fin 4) (Fin 4) K) := by
  classical
  have hB := matrixForm_isAlt hodd R hR
  have hnd := matrixForm_nondegenerate R
  obtain ⟨m, bs, hm, hll, hrr, hlr⟩ :=
    CatalogueBAlternatingIsometry.exists_blueprint_symplectic_basis (matrixForm R) hB hnd
  have hm2 : m = 2 := by
    rw [Module.finrank_fin_fun] at hm
    omega
  let w : Fin m ⊕ Fin m → Kˣ := Sum.elim (fun _ => 1) (fun _ => -1)
  let bs' := bs.unitsSMul w
  let h : (Fin 4 → K) ≃ₗ[K] (Fin 4 → K) := bs.equiv bs' (Equiv.refl _)
  have hbi : ∀ i, h (bs i) = w i • bs i := fun i => by
    simp [h, bs', Module.Basis.equiv_apply, Module.Basis.unitsSMul_apply]
  have hh : (matrixForm R).comp h.toLinearMap h.toLinearMap = (-1 : K) • matrixForm R := by
    apply LinearMap.BilinForm.ext_basis bs
    intro i j
    show matrixForm R (h (bs i)) (h (bs j)) = (-1 : K) * matrixForm R (bs i) (bs j)
    rw [hbi i, hbi j]
    rcases i with i | i <;> rcases j with j | j
    · simp [w, hll, Units.smul_def]
    · simp [w, Units.smul_def]
    · simp [w, Units.smul_def]
    · simp [w, Units.smul_def, hrr]
  have hmat : LinearMap.toMatrix bs bs h.toLinearMap = Matrix.diagonal (fun i => ((w i : Kˣ) : K)) := by
    ext i j
    rw [LinearMap.toMatrix_apply]
    change bs.repr (h (bs j)) i = _
    rw [hbi j, Units.smul_def, map_smul, Module.Basis.repr_self]
    by_cases hij : i = j
    · subst hij
      simp [Matrix.diagonal_apply]
    · simp [Matrix.diagonal_apply, Finsupp.single_apply, hij, Ne.symm hij]
  have hdet : LinearMap.det h.toLinearMap = 1 := by
    rw [← LinearMap.det_toMatrix bs, hmat, Matrix.det_diagonal, Fintype.prod_sum_type]
    simp [w, hm2]
  refine ⟨LinearMap.toMatrix' h.toLinearMap, ?_, ?_⟩
  · rw [LinearMap.det_toMatrix']
    exact hdet
  · have hcomp := Matrix.toBilin'_comp (R : Matrix (Fin 4) (Fin 4) K)
      (LinearMap.toMatrix' h.toLinearMap) (LinearMap.toMatrix' h.toLinearMap)
    rw [Matrix.toLin'_toMatrix'] at hcomp
    have h1 : Matrix.toBilin' ((LinearMap.toMatrix' h.toLinearMap)ᵀ * (R : Matrix (Fin 4) (Fin 4) K) *
        LinearMap.toMatrix' h.toLinearMap) = Matrix.toBilin' (-(R : Matrix (Fin 4) (Fin 4) K)) := by
      rw [← hcomp]
      change (matrixForm R).comp h.toLinearMap h.toLinearMap = _
      rw [hh, map_neg]
      ext u v
      simp [matrixForm]
    exact Matrix.toBilin'.injective h1

end AntiIsometry

section Displacement

variable {K : Type} [Field K]

open CFSG.ComponentClassification.CatalogueBHigherLinearAction (slConjugation toGL_slConjugation)
open CFSG.ComponentClassification.CatalogueBGraphForm (glGraphAut glTranspose toGL_slGraphAut
  pureGraphAction slGraphAut)

theorem u42_pg_psi_eq {n : ℕ} (A : GL (Fin n) K) (x z : SpecialLinearGroup (Fin n) K) (μ : Kˣ)
    (hx : (x : Matrix (Fin n) (Fin n) K)ᵀ * ((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
      (x : Matrix (Fin n) (Fin n) K) = (μ : K) • ((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))
    (hz : SpecialLinearGroup.toGL z = GeneralLinearGroup.scalar (Fin n) μ⁻¹) :
    (slConjugation n K A * slGraphAut n K) x = x * z := by
  apply SpecialLinearGroup.toGL_injective
  rw [MulAut.mul_apply, toGL_slConjugation, toGL_slGraphAut, map_mul, hz, map_inv]
  set X := SpecialLinearGroup.toGL x with hX
  set y := glTranspose n K X with hy
  set S := GeneralLinearGroup.scalar (Fin n) μ with hS
  have hGL : y * A⁻¹ * X = A⁻¹ * S := by
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, Units.val_mul, hy, CatalogueBGraphForm.glTranspose_matrix,
      hX, SpecialLinearGroup.coe_GL_coe_matrix, hS, GeneralLinearGroup.coe_scalar]
    rw [hx, show Matrix.scalar (Fin n) (μ : K) = (μ : K) • (1 : Matrix (Fin n) (Fin n) K) from
      (Matrix.smul_one_eq_diagonal _).symm, Matrix.mul_smul, Matrix.mul_one]
  have key : y * A⁻¹ * (X * S⁻¹) = A⁻¹ := by
    rw [← mul_assoc (y * A⁻¹) X, hGL, mul_assoc, mul_inv_cancel, mul_one]
  have hg : glGraphAut n K X = y⁻¹ := by
    rw [hy, glTranspose, inv_inv]
  rw [hg]
  calc A * y⁻¹ * A⁻¹ = A * y⁻¹ * (y * A⁻¹ * (X * S⁻¹)) := by rw [key]
    _ = X * S⁻¹ := by group

end Displacement

section Lift

variable {n : ℕ} {K : Type} [Field K] [Finite K]

open CFSG.ComponentClassification.CatalogueBHigherLinearAction (slConjugation toGL_slConjugation)
open CFSG.ComponentClassification.CatalogueBGraphForm (glGraphAut glTranspose toGL_slGraphAut
  pureGraphAction slGraphAut)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.CatalogueBGeneralLinear (specialLinearRange)
open CFSG.ComponentClassification.CatFC (pgFix_iff)

theorem u42_pgLift_inv (A : GL (Fin n) K) :
    (center (SpecialLinearGroup (Fin n) K)).map
      (slConjugation n K A * slGraphAut n K).toMonoidHom =
      center (SpecialLinearGroup (Fin n) K) :=
  Subgroup.map_center_eq
    (slConjugation n K A * slGraphAut n K : MulAut (SpecialLinearGroup (Fin n) K))

theorem u42_pureGraphAction_eq (A : GL (Fin n) K) :
    pureGraphAction n K A = CatalogueBFixedCentralQuotient.onQuotient
      (center (SpecialLinearGroup (Fin n) K)) (slConjugation n K A * slGraphAut n K)
      (u42_pgLift_inv A) := by
  refine MulEquiv.ext fun x => ?_
  induction x using QuotientGroup.induction_on with
  | H g =>
    rw [show ((g : SpecialLinearGroup (Fin n) K ⧸ center (SpecialLinearGroup (Fin n) K)) :
        SpecialLinearGroup (Fin n) K ⧸ center (SpecialLinearGroup (Fin n) K)) =
        QuotientGroup.mk' (center (SpecialLinearGroup (Fin n) K)) g from rfl,
      CatalogueBFixedCentralQuotient.onQuotient_mk]
    exact CatalogueBGraphForm.pureGraphAction_mk n K A g

theorem u42_pgLift_fixed_map (A : GL (Fin n) K) :
    (fixedSubgroup (slConjugation n K A * slGraphAut n K)).map SpecialLinearGroup.toGL =
      CatalogueBGraphForm.isometryGroup n K A⁻¹ ⊓ specialLinearRange n K := by
  ext y
  constructor
  · rintro ⟨g, hg, rfl⟩
    refine Subgroup.mem_inf.mpr ⟨?_, ⟨g, rfl⟩⟩
    have h1 : SpecialLinearGroup.toGL ((slConjugation n K A * slGraphAut n K) g) =
        SpecialLinearGroup.toGL g :=
      congrArg _ (show (slConjugation n K A * slGraphAut n K) g = g from hg)
    rw [MulAut.mul_apply, toGL_slConjugation, toGL_slGraphAut] at h1
    exact (pgFix_iff A _).mp h1
  · intro hy
    obtain ⟨hyI, ⟨g, rfl⟩⟩ := Subgroup.mem_inf.mp hy
    refine ⟨g, ?_, rfl⟩
    change (slConjugation n K A * slGraphAut n K) g = g
    apply SpecialLinearGroup.toGL_injective
    rw [MulAut.mul_apply, toGL_slConjugation, toGL_slGraphAut]
    exact (pgFix_iff A _).mpr hyI

theorem u42_pgLift_card (A : GL (Fin n) K) :
    Nat.card ↥(fixedSubgroup (slConjugation n K A * slGraphAut n K)) =
      Nat.card ↥(CatalogueBGraphForm.isometryGroup n K A⁻¹ ⊓ specialLinearRange n K) := by
  rw [← u42_pgLift_fixed_map A]
  exact Nat.card_congr ((fixedSubgroup (slConjugation n K A * slGraphAut n K)).equivMapOfInjective
    SpecialLinearGroup.toGL SpecialLinearGroup.toGL_injective).toEquiv

end Lift

section Final

variable {K : Type} [Field K] [Finite K]

open CFSG.ComponentClassification.CatalogueBHigherLinearAction (slConjugation)
open CFSG.ComponentClassification.CatalogueBGraphForm (pureGraphAction slGraphAut)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.CatalogueBGeneralLinear (specialLinearRange)

theorem u42_pg_isometry_det_one (hK : Nat.card K = 3) (R : GL (Fin 4) K)
    (hR : (R : Matrix (Fin 4) (Fin 4) K)ᵀ = -(R : Matrix (Fin 4) (Fin 4) K)) {x : GL (Fin 4) K}
    (hx : x ∈ isometryGroup 4 K R) : Matrix.GeneralLinearGroup.det x = 1 := by
  have hodd := u42_ringChar_ne_two (f := 1) le_rfl (by rw [hK]; norm_num)
  have hB := matrixForm_isAlt hodd R hR
  have hnd := matrixForm_nondegenerate R
  obtain ⟨e⟩ := OutcomeLocal.nonempty_altIsometry_mulEquiv_statedSp (matrixForm R) hB hnd
    (r := 2) (by rw [Module.finrank_fin_fun])
  let e' : ↥(isometryGroup 4 K R) ≃* CFSG.Assembly.LowTwoRank.StatedSp 2 K :=
    (isometryGroupEquiv R).symm.trans e
  let φ : CFSG.Assembly.LowTwoRank.StatedSp 2 K →* Kˣ := Matrix.GeneralLinearGroup.det.comp
    ((isometryGroup 4 K R).subtype.comp e'.symm.toMonoidHom)
  have hperf := Group.isPerfect_def.mp
    (LieType.Universal.Symplectic.isQuasisimple 2 K (by norm_num)
      (Or.inr (Or.inl ⟨hK, le_rfl⟩))).1
  have hker : φ.ker = ⊤ := eq_top_iff.mpr (hperf ▸ Abelianization.commutator_subset_ker φ)
  have h1 : e' ⟨x, hx⟩ ∈ φ.ker := by
    rw [hker]
    exact Subgroup.mem_top _
  have h2 : φ (e' ⟨x, hx⟩) = 1 := h1
  simpa [φ] using h2

theorem u42_pg_alt_four_false (hK : Nat.card K = 3) (A : GL (Fin 4) K)
    (halt : (A : Matrix (Fin 4) (Fin 4) K)ᵀ = -(A : Matrix (Fin 4) (Fin 4) K))
    {J : Subgroup ↥(fixedSubgroup (pureGraphAction 4 K A))}
    (hJ : U42Hyp (pureGraphAction 4 K A) J) : False := by
  have hodd := u42_ringChar_ne_two (f := 1) le_rfl (by rw [hK]; norm_num)
  have h2K : (2 : K) ≠ 0 := Ring.two_ne_zero hodd
  have hRalt := CatalogueBLinearHigherB.transpose_inv_of_transpose_eq_neg A halt
  obtain ⟨h1, h2⟩ := u42_pg_constraints (by norm_num) A hJ
  have hI : Nat.card ↥(isometryGroup 4 K A⁻¹) = 51840 := by
    rw [u42_pg_card_alt hodd (m := 2) rfl A⁻¹ hRalt, hK]
    rw [show Finset.Icc 1 2 = {1, 2} by decide, Finset.prod_pair (by norm_num)]
    norm_num
  have hIB : isometryGroup 4 K A⁻¹ ⊓ specialLinearRange 4 K = isometryGroup 4 K A⁻¹ := by
    refine inf_eq_left.mpr fun x hx => ?_
    rw [CatalogueBGeneralLinear.specialLinearRange_eq_detKernel, MonoidHom.mem_ker]
    exact u42_pg_isometry_det_one hK A⁻¹ hRalt hx
  rw [hIB, hI] at h1 h2
  have hz2 : Nat.card (center (SpecialLinearGroup (Fin 4) K)) = 2 := by
    have hd : Nat.card (center (SpecialLinearGroup (Fin 4) K)) ∣ 2 := by
      have := u42_card_center_sl_dvd_card (K := K) (n := 4) (by norm_num)
      rwa [hK] at this
    have hpos : 0 < Nat.card (center (SpecialLinearGroup (Fin 4) K)) := Nat.card_pos
    have hle := Nat.le_of_dvd (by norm_num) hd
    have h12 : Nat.card (center (SpecialLinearGroup (Fin 4) K)) = 1 ∨
        Nat.card (center (SpecialLinearGroup (Fin 4) K)) = 2 := by omega
    rcases h12 with h12 | h12
    · rw [h12] at h2
      omega
    · exact h12
  obtain ⟨M, hdetM, hM⟩ := u42_exists_antiIsometry_sl4 hodd A⁻¹ hRalt
  let x : SpecialLinearGroup (Fin 4) K := ⟨M, hdetM⟩
  let z₀ : SpecialLinearGroup (Fin 4) K := ⟨-1, by
    rw [Matrix.det_neg, Matrix.det_one, Fintype.card_fin]
    norm_num⟩
  have hz₀ : SpecialLinearGroup.toGL z₀ = GeneralLinearGroup.scalar (Fin 4) (-1 : Kˣ)⁻¹ := by
    apply Units.ext
    rw [SpecialLinearGroup.coe_GL_coe_matrix, GeneralLinearGroup.coe_scalar]
    ext i j
    by_cases hij : i = j
    · subst hij
      simp [z₀, Matrix.scalar_apply]
    · simp [z₀, Matrix.scalar_apply, hij]
  have hx : (slConjugation 4 K A * slGraphAut 4 K) x = x * z₀ := by
    refine u42_pg_psi_eq A x z₀ (-1) ?_ hz₀
    rw [Units.val_neg, Units.val_one, neg_smul, one_smul]
    exact hM
  have hz₀mem : z₀ ∈ center (SpecialLinearGroup (Fin 4) K) := by
    rw [Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    change (g : Matrix (Fin 4) (Fin 4) K) * (-1) = (-1) * (g : Matrix (Fin 4) (Fin 4) K)
    simp
  have hz₀ne : z₀ ≠ 1 := by
    intro h
    have h' := congrArg (fun g : SpecialLinearGroup (Fin 4) K =>
      (g : Matrix (Fin 4) (Fin 4) K) 0 0) h
    simp [z₀] at h'
    apply h2K
    linear_combination (-1 : K) * h'
  have hout : pureGraphAction 4 K A ∉
      CFSG.ComponentClassification.OuterAutomorphisms.inner
        (ProjectiveSpecialLinearGroup (Fin 4) K) :=
    CFSG.ComponentClassification.CatFC.PSLSmallGraph3.pureGraph_not_inner (by norm_num) A
  have hC := hJ.card_outer hout
  rw [u42_pureGraphAction_eq A] at hC
  have hdisp := card_fixed_onQuotient_eq_of_displacement
    (center (SpecialLinearGroup (Fin 4) K)) le_rfl (slConjugation 4 K A * slGraphAut 4 K)
    (u42_pgLift_inv A) hz2 hz₀mem hz₀ne hx
  rw [hC, u42_pgLift_card A, hIB, hI] at hdisp
  exact absurd hdisp (by norm_num)

end Final

end CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo
