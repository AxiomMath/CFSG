module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHigherLinearInnerFixed
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHigherLinearFieldDeterminant
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBProjectiveQuadraticQuotient

public noncomputable section

namespace CFSG.ComponentClassification.CatFC.PSLSmall

open Subgroup CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank Matrix
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.CatalogueBHigherLinearAction
open CFSG.ComponentClassification.CatalogueBProjectiveInvolution
open CFSG.ComponentClassification.CatalogueBProjectiveQuadratic
open CFSG.ComponentClassification.CatalogueBProjectiveCoordinates

section Conj

variable {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]

private def TwD (A : GL ι K) (lambda : Kˣ) (_hsq : A ^ 2 = GeneralLinearGroup.scalar ι lambda) :
    Type := ι → K

private instance (A : GL ι K) (lambda : Kˣ) (hsq : A ^ 2 = GeneralLinearGroup.scalar ι lambda) :
    AddCommGroup (TwD A lambda hsq) := inferInstanceAs (AddCommGroup (ι → K))

private instance (A : GL ι K) (lambda : Kˣ) (hsq : A ^ 2 = GeneralLinearGroup.scalar ι lambda) :
    Module K (TwD A lambda hsq) := inferInstanceAs (Module K (ι → K))

private instance (A : GL ι K) (lambda : Kˣ) (hsq : A ^ 2 = GeneralLinearGroup.scalar ι lambda) :
    Module (extension lambda.val) (TwD A lambda hsq) := matrixModule A lambda hsq

private instance (A : GL ι K) (lambda : Kˣ) (hsq : A ^ 2 = GeneralLinearGroup.scalar ι lambda) :
    IsScalarTower K (extension lambda.val) (TwD A lambda hsq) :=
  matrixModule_scalarTower A lambda hsq

private instance (A : GL ι K) (lambda : Kˣ) (hsq : A ^ 2 = GeneralLinearGroup.scalar ι lambda) :
    Module.Finite (extension lambda.val) (TwD A lambda hsq) := matrixModule_finite A lambda hsq

private theorem TwD_root_smul (A : GL ι K) (lambda : Kˣ)
    (hsq : A ^ 2 = GeneralLinearGroup.scalar ι lambda) (v : TwD A lambda hsq) :
    (AdjoinRoot.root (quadraticPolynomial lambda.val) • v : TwD A lambda hsq) =
      A.val.mulVec v :=
  matrixModule_root_smul A lambda hsq v

theorem exists_conj_neg_of_nonsquare [Nonempty ι] (A : GL ι K) (lambda : Kˣ)
    (hns : ¬ IsSquare lambda.val) (hsq : A ^ 2 = GeneralLinearGroup.scalar ι lambda) :
    ∃ w : GL ι K, w * A * w⁻¹ = GeneralLinearGroup.scalar ι (-1) * A := by
  haveI : Fact (¬ IsSquare lambda.val) := ⟨hns⟩
  set s : GL ι K := GeneralLinearGroup.scalar ι (-1) with hs
  set A' : GL ι K := s * A with hA'
  have hcomm : Commute s A := GeneralLinearGroup.scalar_commute _ A
  have hsq' : A' ^ 2 = GeneralLinearGroup.scalar ι lambda := by
    rw [hA', hcomm.mul_pow, hsq, hs, ← map_pow, neg_one_sq, map_one, one_mul]
  have hd1 := matrixDimension_twice A lambda hsq
  have hd2 := matrixDimension_twice A' lambda hsq'
  have hfr : Module.finrank (extension lambda.val) (TwD A lambda hsq) =
      Module.finrank (extension lambda.val) (TwD A' lambda hsq') := by
    have e1 : Module.finrank (extension lambda.val) (TwD A lambda hsq) =
      matrixDimension A lambda hsq := rfl
    have e2 : Module.finrank (extension lambda.val) (TwD A' lambda hsq') =
      matrixDimension A' lambda hsq' := rfl
    omega
  let w : TwD A lambda hsq ≃ₗ[extension lambda.val] TwD A' lambda hsq' :=
    LinearEquiv.ofFinrankEq _ _ hfr
  let W : (ι → K) ≃ₗ[K] (ι → K) :=
    (LinearEquiv.restrictScalars K w : TwD A lambda hsq ≃ₗ[K] TwD A' lambda hsq')
  have hsmul : ∀ x : ι → K, s.val.mulVec x = -x := by
    intro x
    ext i
    rw [hs]
    simp [GeneralLinearGroup.scalar, Matrix.mulVec, dotProduct, Matrix.diagonal_apply,
      Matrix.one_apply]
  have hA'mul : ∀ u : ι → K, A'.val.mulVec u = -(A.val.mulVec u) := by
    intro u
    rw [hA', Units.val_mul, ← Matrix.mulVec_mulVec, hsmul]
  have hkey : ∀ v : ι → K, W (A.val.mulVec v) = -(A.val.mulVec (W v)) := by
    intro v
    let v' : TwD A lambda hsq := v
    have h1 : w (AdjoinRoot.root (quadraticPolynomial lambda.val) • v') =
        AdjoinRoot.root (quadraticPolynomial lambda.val) • w v' :=
      w.map_smul _ _
    rw [TwD_root_smul] at h1
    have h2 := TwD_root_smul A' lambda hsq' (w v')
    exact h1.trans (h2.trans (hA'mul (w v')))
  refine ⟨matrixActionEquiv.symm W, ?_⟩
  have hrel : matrixActionEquiv.symm W * A = (s * A) * matrixActionEquiv.symm W := by
    apply matrixActionEquiv.injective
    apply LinearEquiv.ext
    intro v
    rw [map_mul, map_mul, map_mul, LinearEquiv.mul_apply, LinearEquiv.mul_apply,
      LinearEquiv.mul_apply, matrixActionEquiv_apply_symm_apply, matrixActionEquiv_apply,
      matrixActionEquiv_apply, matrixActionEquiv_apply, hkey, hsmul]
  calc matrixActionEquiv.symm W * A * (matrixActionEquiv.symm W)⁻¹
      = (s * A) * matrixActionEquiv.symm W * (matrixActionEquiv.symm W)⁻¹ := by rw [hrel]
    _ = s * A := mul_inv_cancel_right _ _

end Conj

section Quad4Dvd

variable {K : Type} [Field K] [Finite K]

theorem card_units_eq_two_of_card_three (hK : Nat.card K = 3) : Nat.card Kˣ = 2 := by
  rw [Nat.card_units, hK]

theorem card_range_quad_dvd (hK : Nat.card K = 3) {A : GL (Fin 4) K} {lambda : Kˣ}
    (hns : ¬ IsSquare lambda.val) (hsq : A ^ 2 = GeneralLinearGroup.scalar (Fin 4) lambda) :
    2 ^ 6 ∣ Nat.card (ordinaryCentralizerProjection A).range := by
  haveI : Fact (¬ IsSquare lambda.val) := ⟨hns⟩
  haveI : Finite (extension lambda.val) := Module.finite_of_finite K
  have hdim := matrixDimension_twice A lambda hsq
  simp only [Fintype.card_fin] at hdim
  have hm : matrixDimension A lambda hsq = 2 := by omega
  have hE : Nat.card (extension lambda.val) = 9 := by
    rw [Module.natCard_eq_pow_finrank (K := K), extension_finrank, hK]
    norm_num
  have hGL : Nat.card (GL (Fin (matrixDimension A lambda hsq)) (extension lambda.val)) = 5760 := by
    rw [hm]
    letI : Fintype (extension lambda.val) := Fintype.ofFinite _
    have hE' : Fintype.card (extension lambda.val) = 9 := by
      rw [← Nat.card_eq_fintype_card]
      exact hE
    rw [Matrix.card_GL_field, Fin.prod_univ_two, hE']
    norm_num
  rw [Nat.card_congr (projectiveQuadraticQuotientEquiv A lambda hsq).toEquiv]
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup
    (matrixKScalars lambda.val (matrixDimension A lambda hsq)).range
  rw [hGL] at h1
  have h2 : Nat.card (matrixKScalars lambda.val (matrixDimension A lambda hsq)).range ≤ 2 := by
    rw [← card_units_eq_two_of_card_three hK]
    exact Nat.card_le_card_of_surjective _ (MonoidHom.rangeRestrict_surjective _)
  have h3 : 0 < Nat.card (matrixKScalars lambda.val (matrixDimension A lambda hsq)).range :=
    Nat.card_pos
  generalize Nat.card (matrixKScalars lambda.val (matrixDimension A lambda hsq)).range = y at *
  generalize Nat.card ((GL (Fin (matrixDimension A lambda hsq)) (extension lambda.val)) ⧸
    (matrixKScalars lambda.val (matrixDimension A lambda hsq)).range) = x at *
  interval_cases y <;> omega

theorem card_P_eq_two_mul_range (htwo : (2 : K) ≠ 0) {A : GL (Fin 4) K} {lambda : Kˣ}
    (hns : ¬ IsSquare lambda.val) (hsq : A ^ 2 = GeneralLinearGroup.scalar (Fin 4) lambda) :
    Nat.card (Subgroup.centralizer ({ProjGenLinGroup.mk A} : Set (ProjGenLinGroup (Fin 4) K))) =
      2 * Nat.card (ordinaryCentralizerProjection A).range := by
  have hproj : ProjGenLinGroup.mk A ^ 2 = 1 := by
    rw [← map_pow, hsq, ProjGenLinGroup.mk_scalar]
  have hle : (ordinaryCentralizerProjection A).range.index ≤ 2 :=
    ordinaryCentralizerProjection_range_index_le_two A hproj
  obtain ⟨w, hw⟩ := exists_conj_neg_of_nonsquare A lambda hns hsq
  have hw' : w * A = (GeneralLinearGroup.scalar (Fin 4) (-1) * A) * w :=
    mul_inv_eq_iff_eq_mul.mp hw
  have hP : ProjGenLinGroup.mk w ∈
      Subgroup.centralizer ({ProjGenLinGroup.mk A} : Set (ProjGenLinGroup (Fin 4) K)) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have := congrArg ProjGenLinGroup.mk hw'
    rw [map_mul, map_mul, map_mul, ProjGenLinGroup.mk_scalar, one_mul] at this
    exact this
  have hnot : (⟨ProjGenLinGroup.mk w, hP⟩ :
      Subgroup.centralizer ({ProjGenLinGroup.mk A} : Set (ProjGenLinGroup (Fin 4) K))) ∉
        (ordinaryCentralizerProjection A).range := by
    rintro ⟨B, hB⟩
    have hmk : ProjGenLinGroup.mk B.val = ProjGenLinGroup.mk w := congrArg Subtype.val hB
    obtain ⟨c, hc⟩ := ProjGenLinGroup.mk_eq_mk_iff.mp hmk
    have hBA : B.val * A = A * B.val := Subgroup.mem_centralizer_singleton_iff.mp B.property
    have hwA : w * A = A * w := by
      rw [← hc]
      calc B.val * GeneralLinearGroup.scalar (Fin 4) c * A
          = B.val * (GeneralLinearGroup.scalar (Fin 4) c * A) := mul_assoc _ _ _
        _ = B.val * (A * GeneralLinearGroup.scalar (Fin 4) c) := by
          rw [GeneralLinearGroup.scalar_commute c A]
        _ = (B.val * A) * GeneralLinearGroup.scalar (Fin 4) c := (mul_assoc _ _ _).symm
        _ = (A * B.val) * GeneralLinearGroup.scalar (Fin 4) c := by rw [hBA]
        _ = A * (B.val * GeneralLinearGroup.scalar (Fin 4) c) := mul_assoc _ _ _
    have h1 : A * w = (GeneralLinearGroup.scalar (Fin 4) (-1) * A) * w := hwA.symm.trans hw'
    have h2 : A = GeneralLinearGroup.scalar (Fin 4) (-1) * A := mul_right_cancel h1
    have h3 : (1 : GL (Fin 4) K) = GeneralLinearGroup.scalar (Fin 4) (-1) :=
      mul_right_cancel (by rw [one_mul]; exact h2)
    have h4 : (1 : Kˣ) = -1 := by
      apply scalarGL_injective (ι := Fin 4) (K := K)
      rw [map_one]
      exact h3
    have h5 : ((1 : Kˣ) : K) = ((-1 : Kˣ) : K) := congrArg Units.val h4
    apply htwo
    simp only [Units.val_one, Units.val_neg] at h5
    linear_combination h5
  have hidx : (ordinaryCentralizerProjection A).range.index ≠ 1 := by
    intro h1
    rw [Subgroup.index_eq_one] at h1
    apply hnot
    rw [h1]
    exact Subgroup.mem_top _
  have hpos : 0 < (ordinaryCentralizerProjection A).range.index :=
    Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  have hi2 : (ordinaryCentralizerProjection A).range.index = 2 := by omega
  rw [← Subgroup.card_mul_index (ordinaryCentralizerProjection A).range, hi2, mul_comm]

theorem card_P_eq_mul_fixed (hK : Nat.card K = 3) (A : GL (Fin 4) K) :
    ∃ i : ℕ, 0 < i ∧ i ≤ 2 ∧
      Nat.card (Subgroup.centralizer ({ProjGenLinGroup.mk A} :
        Set (ProjGenLinGroup (Fin 4) K))) =
        Nat.card (fixedSubgroup (innerDiagonalAction 4 K A)) * i := by
  have hc : ∀ c : Kˣ, c ^ 4 = 1 := by
    intro c
    have h2 : c ^ 2 = 1 := by
      have := pow_card_eq_one' (G := Kˣ) (x := c)
      rwa [card_units_eq_two_of_card_three hK] at this
    calc c ^ 4 = (c ^ 2) ^ 2 := by rw [← pow_mul]
      _ = 1 := by rw [h2, one_pow]
  set P := Subgroup.centralizer ({ProjGenLinGroup.mk A} : Set (ProjGenLinGroup (Fin 4) K))
    with hPdef
  let f : GL (Fin 4) K →* Kˣ := Matrix.GeneralLinearGroup.det
  have hf : f.comp (GeneralLinearGroup.scalar (Fin 4)) = 1 := by
    apply MonoidHom.ext
    intro c
    simp [f, GeneralLinearGroup.det_scalar, hc c]
  let d : P →* Kˣ := (ProjGenLinGroup.lift f hf).comp P.subtype
  have hker : d.ker = CatalogueBHigherLinearInner.localPSLRange 4 K (ProjGenLinGroup.mk A) := by
    ext b
    obtain ⟨g, hg⟩ := ProjGenLinGroup.mk_surjective b.val
    have hdb : d b = Matrix.GeneralLinearGroup.det g := by
      change (ProjGenLinGroup.lift f hf) b.val = _
      rw [← hg, ProjGenLinGroup.lift_mk]
    have hmem : b ∈ CatalogueBHigherLinearInner.localPSLRange 4 K (ProjGenLinGroup.mk A) ↔
        b.val ∈ pslRange 4 K := Iff.rfl
    rw [hmem, ← hg,
      CFSG.ComponentClassification.CatalogueBHigherLinearField.mk_mem_pslRange_iff_det_power,
      MonoidHom.mem_ker, hdb]
    constructor
    · intro h1
      exact ⟨1, by rw [one_pow, h1]⟩
    · rintro ⟨c, hc4⟩
      rw [← hc4, hc c]
  have h1 : Nat.card (fixedSubgroup (innerDiagonalAction 4 K A)) = Nat.card d.ker := by
    rw [hker]
    exact Nat.card_congr (CatalogueBHigherLinearInner.innerFixedCentralizerEquiv 4 K A).toEquiv
  have h2 : d.ker.index ≤ 2 := by
    rw [Subgroup.index_ker, ← card_units_eq_two_of_card_three hK]
    exact Nat.card_le_card_of_injective _ Subtype.val_injective
  have h3 : Nat.card d.ker * d.ker.index = Nat.card P := Subgroup.card_mul_index _
  exact ⟨d.ker.index, Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite, h2, by
    rw [h1, ← h3]⟩

theorem inner_four_quadratic_two_pow_six (hK : Nat.card K = 3) (htwo : (2 : K) ≠ 0)
    {A : GL (Fin 4) K} {lambda : Kˣ} (hns : ¬ IsSquare lambda.val)
    (hsq : A ^ 2 = GeneralLinearGroup.scalar (Fin 4) lambda) :
    2 ^ 6 ∣ Nat.card (fixedSubgroup (innerDiagonalAction 4 K A)) := by
  have h1 := card_range_quad_dvd hK hns hsq
  have h2 := card_P_eq_two_mul_range htwo hns hsq
  obtain ⟨i, hi0, hi2, h3⟩ := card_P_eq_mul_fixed hK A
  have h4 : 2 ^ 7 ∣ Nat.card (fixedSubgroup (innerDiagonalAction 4 K A)) * i := by
    rw [← h3, h2, show 2 ^ 7 = 2 * 2 ^ 6 by norm_num]
    exact Nat.mul_dvd_mul_left 2 h1
  interval_cases i <;> omega

end Quad4Dvd

end CFSG.ComponentClassification.CatFC.PSLSmall
