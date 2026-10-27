module

public import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentA6ClPSLSmallInner
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHigherLinearFieldDeterminant
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBProjectiveInvolutionNonsquareComponents

public noncomputable section

namespace CFSG.ComponentClassification.CatFC.PSLSmall

open Subgroup CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank Matrix
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.CatalogueBHigherLinearAction
open CFSG.ComponentClassification.CatalogueBProjectiveInvolution
open CFSG.ComponentClassification.CatalogueBProjectiveQuadratic
open CFSG.ComponentClassification.CatalogueBProjectiveCoordinates

section Inner4

variable {K : Type} [Field K] [Finite K]

theorem card_GL_two_of_card_three (hK : Nat.card K = 3) : Nat.card (GL (Fin 2) K) = 48 := by
  letI : Fintype K := Fintype.ofFinite K
  have hK' : Fintype.card K = 3 := by rw [← Nat.card_eq_fintype_card]; exact hK
  rw [Matrix.card_GL_field, Fin.prod_univ_two, hK']
  norm_num

theorem card_GL_two_of_card_nine (hK : Nat.card K = 9) : Nat.card (GL (Fin 2) K) = 5760 := by
  letI : Fintype K := Fintype.ofFinite K
  have hK' : Fintype.card K = 9 := by rw [← Nat.card_eq_fintype_card]; exact hK
  rw [Matrix.card_GL_field, Fin.prod_univ_two, hK']
  norm_num

theorem inner_four_split_false (hK : Nat.card K = 3) (htwo : (2 : K) ≠ 0) {A : GL (Fin 4) K}
    (hσ : orderOf (innerDiagonalAction 4 K A) = 2)
    {D : Subgroup ↥(fixedSubgroup (innerDiagonalAction 4 K A))}
    (h : A6Hyp (innerDiagonalAction 4 K A) D) {lambda : Kˣ}
    (hsq : A ^ 2 = GeneralLinearGroup.scalar (Fin 4) lambda) (hsquare : IsSquare lambda.val) :
    False := by
  obtain ⟨hne, hinv⟩ := inner_proj_data (by norm_num) (Or.inl (by norm_num)) hσ
  obtain ⟨b, hb, hr, hs, hrs, e, q, hesc, -, -⟩ :=
    square_projective_centralizer_structure 4 (by norm_num) A lambda htwo hne hsq hsquare
  generalize positiveMatrixDimension A b.val = r at *
  generalize negativeMatrixDimension A b.val = s at *
  have hperf3 : commutator (SpecialLinearGroup (Fin 3) K) = ⊤ :=
    Group.isPerfect_def.mp (CatalogueBHigherLinearInner.sl_perfect 3 K (by norm_num)
      (Or.inl le_rfl))
  have h3 : 720 * 3 < Nat.card (SpecialLinearGroup (Fin 3) K) :=
    lt_card_SL_of_three_le le_rfl (by omega)
  rcases (by omega : (r = 3 ∧ s = 1) ∨ (r = 1 ∧ s = 3) ∨ (r = 2 ∧ s = 2)) with
    ⟨hr3, hs1⟩ | ⟨hr1, hs3⟩ | ⟨hr2, hs2⟩
  · subst hr3
    have := inner_factor_card_le h hs e hesc hperf3
    omega
  · subst hs3
    let e' := e.trans MulEquiv.prodComm
    have := inner_factor_card_le h hr e' (fun c => by simp [e', hesc c]) hperf3
    omega
  · subst hr2
    subst hs2
    have hdvd := h.dvd
    have h1 := card_fixed_dvd A
    have h2 := card_pglCentralizer A
    have hidx := ordinaryCentralizerProjection_range_index_le_two A hinv
    have hrange : Nat.card (ordinaryCentralizerProjection A).range ∣ 2304 := by
      rw [Nat.card_congr q.toEquiv]
      have h4 := Subgroup.card_quotient_dvd_card (splitDiagonalScalars (K := K) 2 2).range
      have h5 : Nat.card (GL (Fin 2) K × GL (Fin 2) K) = 2304 := by
        rw [Nat.card_prod, card_GL_two_of_card_three hK]
      rwa [h5] at h4
    have h5C : 5 ∣ Nat.card (fixedSubgroup (innerDiagonalAction 4 K A)) :=
      (by norm_num : 5 ∣ 360).trans hdvd
    have h5P := h5C.trans h1
    rw [h2] at h5P
    have hp5 : Nat.Prime 5 := by norm_num
    rcases hp5.dvd_mul.mp h5P with h5R | h5I
    · have := h5R.trans hrange
      omega
    · have hpos : 0 < (ordinaryCentralizerProjection A).range.index := by
        apply Nat.pos_of_ne_zero
        exact Subgroup.index_ne_zero_of_finite
      have := Nat.le_of_dvd hpos h5I
      omega

end Inner4

section Neg

variable {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]

@[expose] def Tw (A : GL ι K) (lambda : Kˣ) (_hsq : A ^ 2 = GeneralLinearGroup.scalar ι lambda) :
    Type := ι → K

instance (A : GL ι K) (lambda : Kˣ) (hsq : A ^ 2 = GeneralLinearGroup.scalar ι lambda) :
    AddCommGroup (Tw A lambda hsq) := inferInstanceAs (AddCommGroup (ι → K))

instance (A : GL ι K) (lambda : Kˣ) (hsq : A ^ 2 = GeneralLinearGroup.scalar ι lambda) :
    Module K (Tw A lambda hsq) := inferInstanceAs (Module K (ι → K))

instance (A : GL ι K) (lambda : Kˣ) (hsq : A ^ 2 = GeneralLinearGroup.scalar ι lambda) :
    Module (extension lambda.val) (Tw A lambda hsq) := matrixModule A lambda hsq

instance (A : GL ι K) (lambda : Kˣ) (hsq : A ^ 2 = GeneralLinearGroup.scalar ι lambda) :
    IsScalarTower K (extension lambda.val) (Tw A lambda hsq) :=
  matrixModule_scalarTower A lambda hsq

instance (A : GL ι K) (lambda : Kˣ) (hsq : A ^ 2 = GeneralLinearGroup.scalar ι lambda) :
    Module.Finite (extension lambda.val) (Tw A lambda hsq) := matrixModule_finite A lambda hsq

theorem Tw_root_smul (A : GL ι K) (lambda : Kˣ) (hsq : A ^ 2 = GeneralLinearGroup.scalar ι lambda)
    (v : Tw A lambda hsq) :
    (AdjoinRoot.root (quadraticPolynomial lambda.val) • v : Tw A lambda hsq) = A.val.mulVec v :=
  matrixModule_root_smul A lambda hsq v

theorem exists_conj_neg [Nonempty ι] (A : GL ι K) (lambda : Kˣ) (hns : ¬ IsSquare lambda.val)
    (hsq : A ^ 2 = GeneralLinearGroup.scalar ι lambda) :
    ∃ w : GL ι K, w * A * w⁻¹ = GeneralLinearGroup.scalar ι (-1) * A := by
  haveI : Fact (¬ IsSquare lambda.val) := ⟨hns⟩
  set s : GL ι K := GeneralLinearGroup.scalar ι (-1) with hs
  set A' : GL ι K := s * A with hA'
  have hcomm : Commute s A := GeneralLinearGroup.scalar_commute _ A
  have hsq' : A' ^ 2 = GeneralLinearGroup.scalar ι lambda := by
    rw [hA', hcomm.mul_pow, hsq, hs, ← map_pow, neg_one_sq, map_one, one_mul]
  have hd1 := matrixDimension_twice A lambda hsq
  have hd2 := matrixDimension_twice A' lambda hsq'
  have hfr : Module.finrank (extension lambda.val) (Tw A lambda hsq) =
      Module.finrank (extension lambda.val) (Tw A' lambda hsq') := by
    have e1 : Module.finrank (extension lambda.val) (Tw A lambda hsq) =
      matrixDimension A lambda hsq := rfl
    have e2 : Module.finrank (extension lambda.val) (Tw A' lambda hsq') =
      matrixDimension A' lambda hsq' := rfl
    omega
  let w : Tw A lambda hsq ≃ₗ[extension lambda.val] Tw A' lambda hsq' :=
    LinearEquiv.ofFinrankEq _ _ hfr
  let W : (ι → K) ≃ₗ[K] (ι → K) :=
    (LinearEquiv.restrictScalars K w : Tw A lambda hsq ≃ₗ[K] Tw A' lambda hsq')
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
    let v' : Tw A lambda hsq := v
    have h1 : w (AdjoinRoot.root (quadraticPolynomial lambda.val) • v') =
        AdjoinRoot.root (quadraticPolynomial lambda.val) • w v' :=
      w.map_smul _ _
    rw [Tw_root_smul] at h1
    have h2 := Tw_root_smul A' lambda hsq' (w v')
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

end Neg

section Quad4

variable {K : Type} [Field K] [Finite K]

theorem card_units_of_card_three (hK : Nat.card K = 3) : Nat.card Kˣ = 2 := by
  rw [Nat.card_units, hK]

theorem card_range_quad_ge (hK : Nat.card K = 3) {A : GL (Fin 4) K} {lambda : Kˣ}
    (hns : ¬ IsSquare lambda.val) (hsq : A ^ 2 = GeneralLinearGroup.scalar (Fin 4) lambda) :
    2880 ≤ Nat.card (ordinaryCentralizerProjection A).range := by
  haveI : Fact (¬ IsSquare lambda.val) := ⟨hns⟩
  haveI : Finite (extension lambda.val) := quadraticExtension_finite lambda.val
  have hdim := matrixDimension_twice A lambda hsq
  simp only [Fintype.card_fin] at hdim
  have hm : matrixDimension A lambda hsq = 2 := by omega
  have hE : Nat.card (extension lambda.val) = 9 := by
    rw [Module.natCard_eq_pow_finrank (K := K), extension_finrank, hK]
    norm_num
  have hGL : Nat.card (GL (Fin (matrixDimension A lambda hsq)) (extension lambda.val)) = 5760 := by
    rw [hm]
    exact card_GL_two_of_card_nine hE
  rw [Nat.card_congr (projectiveQuadraticQuotientEquiv A lambda hsq).toEquiv]
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup
    (matrixKScalars lambda.val (matrixDimension A lambda hsq)).range
  rw [hGL] at h1
  have h2 : Nat.card (matrixKScalars lambda.val (matrixDimension A lambda hsq)).range ≤ 2 := by
    rw [← card_units_of_card_three hK]
    exact Nat.card_le_card_of_surjective _ (MonoidHom.rangeRestrict_surjective _)
  have h3 : 0 < Nat.card (matrixKScalars lambda.val (matrixDimension A lambda hsq)).range :=
    Nat.card_pos
  generalize Nat.card (matrixKScalars lambda.val (matrixDimension A lambda hsq)).range = y at *
  generalize Nat.card ((GL (Fin (matrixDimension A lambda hsq)) (extension lambda.val)) ⧸
    (matrixKScalars lambda.val (matrixDimension A lambda hsq)).range) = x at *
  interval_cases y <;> omega

theorem card_P_ge (htwo : (2 : K) ≠ 0) {A : GL (Fin 4) K} {lambda : Kˣ}
    (hns : ¬ IsSquare lambda.val) (hsq : A ^ 2 = GeneralLinearGroup.scalar (Fin 4) lambda) :
    2 * Nat.card (ordinaryCentralizerProjection A).range ≤
      Nat.card (Subgroup.centralizer ({ProjGenLinGroup.mk A} : Set (ProjGenLinGroup (Fin 4) K))) := by
  obtain ⟨w, hw⟩ := exists_conj_neg A lambda hns hsq
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
  rw [card_pglCentralizer A]
  calc 2 * Nat.card (ordinaryCentralizerProjection A).range
      = Nat.card (ordinaryCentralizerProjection A).range * 2 := mul_comm _ _
    _ ≤ Nat.card (ordinaryCentralizerProjection A).range *
        (ordinaryCentralizerProjection A).range.index := Nat.mul_le_mul_left _ (by omega)

theorem card_P_le (hK : Nat.card K = 3) (A : GL (Fin 4) K) :
    Nat.card (Subgroup.centralizer ({ProjGenLinGroup.mk A} : Set (ProjGenLinGroup (Fin 4) K))) ≤
      2 * Nat.card (fixedSubgroup (innerDiagonalAction 4 K A)) := by
  have hc : ∀ c : Kˣ, c ^ 4 = 1 := by
    intro c
    have h2 : c ^ 2 = 1 := by
      have := pow_card_eq_one' (G := Kˣ) (x := c)
      rwa [card_units_of_card_three hK] at this
    calc c ^ 4 = (c ^ 2) ^ 2 := by rw [← pow_mul]
      _ = 1 := by rw [h2, one_pow]
  set P := Subgroup.centralizer ({ProjGenLinGroup.mk A} : Set (ProjGenLinGroup (Fin 4) K)) with hPdef
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
    rw [hmem, ← hg, CFSG.ComponentClassification.CatalogueBHigherLinearField.mk_mem_pslRange_iff_det_power, MonoidHom.mem_ker,
      hdb]
    constructor
    · intro h1
      exact ⟨1, by rw [one_pow, h1]⟩
    · rintro ⟨c, hc4⟩
      rw [← hc4, hc c]
  have h1 : Nat.card (fixedSubgroup (innerDiagonalAction 4 K A)) = Nat.card d.ker := by
    rw [hker]
    exact Nat.card_congr (CatalogueBHigherLinearInner.innerFixedCentralizerEquiv 4 K A).toEquiv
  have h2 : d.ker.index ≤ 2 := by
    rw [Subgroup.index_ker, ← card_units_of_card_three hK]
    exact Nat.card_le_card_of_injective _ Subtype.val_injective
  have h3 : Nat.card d.ker * d.ker.index = Nat.card P := Subgroup.card_mul_index _
  rw [h1, ← h3, mul_comm]
  exact Nat.mul_le_mul_right _ h2

theorem inner_four_quadratic_big (hK : Nat.card K = 3) (htwo : (2 : K) ≠ 0) {A : GL (Fin 4) K}
    {lambda : Kˣ} (hns : ¬ IsSquare lambda.val)
    (hsq : A ^ 2 = GeneralLinearGroup.scalar (Fin 4) lambda) :
    1440 < Nat.card (fixedSubgroup (innerDiagonalAction 4 K A)) := by
  have h1 := card_range_quad_ge hK hns hsq
  have h2 := card_P_ge htwo hns hsq
  have h3 := card_P_le hK A
  omega

theorem inner_four_big (hK : Nat.card K = 3) (htwo : (2 : K) ≠ 0) {A : GL (Fin 4) K}
    (hσ : orderOf (innerDiagonalAction 4 K A) = 2)
    {D : Subgroup ↥(fixedSubgroup (innerDiagonalAction 4 K A))}
    (h : A6Hyp (innerDiagonalAction 4 K A) D) :
    1440 < Nat.card (fixedSubgroup (innerDiagonalAction 4 K A)) := by
  obtain ⟨hne, hinv⟩ := inner_proj_data (by norm_num) (Or.inl (by norm_num)) hσ
  obtain ⟨lambda, hsq⟩ := matrix_square_scalar A hinv
  by_cases hsquare : IsSquare lambda.val
  · exact (inner_four_split_false hK htwo hσ h hsq hsquare).elim
  · exact inner_four_quadratic_big hK htwo hsquare hsq

end Quad4

end CFSG.ComponentClassification.CatFC.PSLSmall
