module

public import CFSG.LieType.SpecialLinear.BorelTwist.CoverType
public import CFSG.LieType.SpecialLinear.BorelTwist.Upper
public import CFSG.LieType.SpecialLinear.TwoEnd.CoverType
public import CFSG.LocalAnalysis.StandardType.GGTypeAFiveProofCrossMat
public import CFSG.LieType.SpecialLinear.NormalizerLift.FieldGraph

public section

namespace CFSG.LieType.SpecialLinear

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.ComponentClassification
  CFSG.LieType.Universal.SpecialLinear CFSG.Quasithin.SmithCurtis
  CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisTw
open scoped MatrixGroups

variable (m : ℕ) (F : Type) [Field F] [Finite F] [CharP F 2]
variable (A : GL (Fin (m + 1)) F)

@[expose] noncomputable def upperDiag (hA : IsUpperGL A) : Fin (m + 1) → Fˣ :=
  TauCeti.UpperTriangularGroup.diag
    ⟨A, TauCeti.UpperTriangularGroup.mem_iff.mpr hA⟩

@[expose] noncomputable def upperDiagGL (hA : IsUpperGL A) : GL (Fin (m + 1)) F :=
  TauCeti.diagGL (upperDiag m F A hA)

@[expose] noncomputable def upperUnipotentGL (hA : IsUpperGL A) : GL (Fin (m + 1)) F :=
  A * (upperDiagGL m F A hA)⁻¹

omit [Finite F] [CharP F 2] in
theorem coe_upperDiagGL (hA : IsUpperGL A) (i j : Fin (m + 1)) :
    ((upperDiagGL m F A hA : GL (Fin (m + 1)) F) :
        Matrix (Fin (m + 1)) (Fin (m + 1)) F) i j =
      if i = j then ((upperDiag m F A hA i : Fˣ) : F) else 0 := by
  rw [upperDiagGL, TauCeti.diagGL_apply]

omit [Finite F] [CharP F 2] in
theorem upperDiag_apply_val (hA : IsUpperGL A) (i : Fin (m + 1)) :
    ((upperDiag m F A hA i : Fˣ) : F) =
      (A : Matrix (Fin (m + 1)) (Fin (m + 1)) F) i i :=
  TauCeti.UpperTriangularGroup.diag_apply_val
    ⟨A, TauCeti.UpperTriangularGroup.mem_iff.mpr hA⟩ i

omit [Finite F] [CharP F 2] in
theorem upperDiagGL_off (hA : IsUpperGL A) {i j : Fin (m + 1)} (hij : i ≠ j) :
    ((upperDiagGL m F A hA : GL (Fin (m + 1)) F) :
        Matrix (Fin (m + 1)) (Fin (m + 1)) F) i j = 0 := by
  rw [coe_upperDiagGL]
  exact if_neg hij

omit [Finite F] [CharP F 2] in
theorem coe_upperDiagGL_inv (hA : IsUpperGL A) (i j : Fin (m + 1)) :
    (((upperDiagGL m F A hA)⁻¹ : GL (Fin (m + 1)) F) :
        Matrix (Fin (m + 1)) (Fin (m + 1)) F) i j =
      if i = j then (((upperDiag m F A hA i)⁻¹ : Fˣ) : F) else 0 := by
  have h : (upperDiagGL m F A hA)⁻¹ =
      TauCeti.diagGL (fun i => (upperDiag m F A hA i)⁻¹) := by
    rw [upperDiagGL]
    exact (map_inv TauCeti.diagGL (upperDiag m F A hA)).symm
  rw [h, TauCeti.diagGL_apply]

omit [Finite F] [CharP F 2] in
theorem eq_upperUnipotent_mul_diag (hA : IsUpperGL A) :
    A = upperUnipotentGL m F A hA * upperDiagGL m F A hA := by
  rw [upperUnipotentGL]
  group

omit [Finite F] [CharP F 2] in
theorem upperUnipotent_isUpperUnitriangular (hA : IsUpperGL A) :
    ((upperUnipotentGL m F A hA : GL (Fin (m + 1)) F) :
        Matrix (Fin (m + 1)) (Fin (m + 1)) F).IsUpperUnitriangular := by
  have hAtri : (A : Matrix (Fin (m + 1)) (Fin (m + 1)) F).IsUpperTriangular := hA
  have hTtri : ((upperDiagGL m F A hA : GL (Fin (m + 1)) F) :
      Matrix (Fin (m + 1)) (Fin (m + 1)) F).IsUpperTriangular := by
    intro i j hij
    exact upperDiagGL_off m F A hA (ne_of_gt hij)
  have hTinv : (((upperDiagGL m F A hA)⁻¹ : GL (Fin (m + 1)) F) :
      Matrix (Fin (m + 1)) (Fin (m + 1)) F).IsUpperTriangular := by
    intro i j hij
    rw [coe_upperDiagGL_inv]
    exact if_neg (ne_of_gt hij)
  have htri : ((upperUnipotentGL m F A hA : GL (Fin (m + 1)) F) :
      Matrix (Fin (m + 1)) (Fin (m + 1)) F).IsUpperTriangular := by
    rw [upperUnipotentGL]
    simpa [Matrix.coe_units_inv] using hAtri.mul hTinv
  refine (Matrix.isUpperUnitriangular_def _).mpr ⟨htri, fun i => ?_⟩
  rw [upperUnipotentGL, Units.val_mul, Matrix.mul_apply_diag_of_isUpperTriangular hAtri hTinv i,
    coe_upperDiagGL_inv, if_pos rfl, ← upperDiag_apply_val]
  exact Units.mul_inv (upperDiag m F A hA i)

omit [Finite F] [CharP F 2] in
theorem upperUnipotent_det (hA : IsUpperGL A) :
    ((upperUnipotentGL m F A hA : GL (Fin (m + 1)) F) :
        Matrix (Fin (m + 1)) (Fin (m + 1)) F).det = 1 := by
  have htri := ((Matrix.isUpperUnitriangular_def _).mp
    (upperUnipotent_isUpperUnitriangular m F A hA)).1
  have hdiag := ((Matrix.isUpperUnitriangular_def _).mp
    (upperUnipotent_isUpperUnitriangular m F A hA)).2
  rw [Matrix.det_of_isUpperTriangular htri]
  exact Finset.prod_eq_one fun i _ => hdiag i

@[expose] noncomputable def upperUnipotentSL (hA : IsUpperGL A) :
    SpecialLinearGroup (Fin (m + 1)) F :=
  ⟨upperUnipotentGL m F A hA, upperUnipotent_det m F A hA⟩

theorem upperUnipotentSL_mem_U (hA : IsUpperGL A) :
    upperUnipotentSL m F A hA ∈ (curtisDatum m F 2).U := by
  rw [mem_curtisDatum_U_iff]
  have h := (Matrix.isUpperUnitriangular_def _).mp
    (upperUnipotent_isUpperUnitriangular m F A hA)
  exact ⟨h.2, h.1⟩

omit [Finite F] [CharP F 2] in
theorem coe_diagGL (d : Fin (m + 1) → Fˣ) :
    ((TauCeti.diagGL d : GL (Fin (m + 1)) F) :
        Matrix (Fin (m + 1)) (Fin (m + 1)) F) =
      Matrix.diagonal (fun i => (d i : F)) :=
  TauCeti.diagGL_coe d

omit [Finite F] [CharP F 2] in
theorem coe_diagGL_inv (d : Fin (m + 1) → Fˣ) :
    (((TauCeti.diagGL d)⁻¹ : GL (Fin (m + 1)) F) :
        Matrix (Fin (m + 1)) (Fin (m + 1)) F) =
      Matrix.diagonal (fun i => ((d i)⁻¹ : F)) := by
  rw [← map_inv, coe_diagGL]
  simp [Units.val_inv_eq_inv_val]

omit [Finite F] [CharP F 2] in
theorem diagonal_mul_single_mul_diagonal (d : Fin (m + 1) → F) (i j : Fin (m + 1)) (c : F) :
    Matrix.diagonal d * Matrix.single i j c *
        Matrix.diagonal (fun k => (d k)⁻¹) =
      Matrix.single i j (d i * c * (d j)⁻¹) := by
  ext r s
  by_cases h : r = i ∧ s = j
  · obtain ⟨rfl, rfl⟩ := h
    simp [Matrix.mul_diagonal]
  · have h' : ¬(i = r ∧ j = s) := fun hh => h ⟨hh.1.symm, hh.2.symm⟩
    simp [Matrix.mul_diagonal, h']

omit [Finite F] [CharP F 2] in
theorem slConjugation_diagGL_transvection (d : Fin (m + 1) → Fˣ)
    {i j : Fin (m + 1)} (hij : i ≠ j) (a : F) :
    CatalogueBHigherLinearAction.slConjugation (m + 1) F (TauCeti.diagGL d)
        (SpecialLinearGroup.transvection hij a) =
      SpecialLinearGroup.transvection hij ((d i : F) * a * ((d j)⁻¹ : F)) := by
  apply Subtype.ext
  rw [CatalogueBHigherLinearAction.slConjugation_matrix, coe_diagGL, coe_diagGL_inv,
    SpecialLinearGroup.transvection_coe, SpecialLinearGroup.transvection_coe]
  rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one]
  rw [Matrix.diagonal_mul_diagonal, diagonal_mul_single_mul_diagonal]
  simp

omit [Finite F] [CharP F 2] in
theorem diagonal_mul_permMatrix_mul_diagonal (d : Fin (m + 1) → F)
    (π : Equiv.Perm (Fin (m + 1))) :
    Matrix.diagonal d * LinearFlag.permMatrix (m + 1) F π *
        Matrix.diagonal (fun k => (d k)⁻¹) =
      Matrix.diagonal (fun r => d r * (d (π.symm r))⁻¹) *
        LinearFlag.permMatrix (m + 1) F π := by
  ext r s
  rw [Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.diagonal_mul]
  by_cases h : r = π s
  · subst r
    simp [LinearFlag.permMatrix_apply, Equiv.symm_apply_apply]
  · simp [LinearFlag.permMatrix_apply, if_neg h]

omit [Finite F] in
theorem slConjugation_diagGL_weylRep (d : Fin (m + 1) → Fˣ) (s : Fin m) :
    CatalogueBHigherLinearAction.slConjugation (m + 1) F (TauCeti.diagGL d)
        (weylRep m F s) =
      hdiag m F s (d s.castSucc * (d s.succ)⁻¹) * weylRep m F s := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul]
  rw [CatalogueBHigherLinearAction.slConjugation_matrix, coe_diagGL, coe_diagGL_inv,
    coe_weylRep', weylMatrix_eq_permMatrix]
  have hh : ((hdiag m F s (d s.castSucc * (d s.succ)⁻¹) :
      SpecialLinearGroup (Fin (m + 1)) F) :
        Matrix (Fin (m + 1)) (Fin (m + 1)) F) =
      Matrix.diagonal (fun r => if r = s.castSucc then
          ((d s.castSucc : F) * ((d s.succ)⁻¹ : F)) else
        if r = s.succ then ((d s.succ : F) * ((d s.castSucc)⁻¹ : F)) else 1) := by
    simpa using hdiag_matrix m F s (d s.castSucc * (d s.succ)⁻¹)
  rw [hh]
  rw [diagonal_mul_permMatrix_mul_diagonal (m := m) (F := F)
    (fun i => (d i : F)) (Equiv.swap s.castSucc s.succ)]
  congr 1
  rw [Matrix.diagonal_injective.eq_iff]
  funext r
  by_cases ha : r = s.castSucc
  · subst ha
    simp [Equiv.swap_apply_left]
  · by_cases hb : r = s.succ
    · subst hb
      simp [Equiv.swap_apply_right, ha]
    · simp [Equiv.swap_apply_of_ne_of_ne ha hb, ha, hb]

omit [Finite F] [CharP F 2] in
theorem hdiag_mul_transvection (s : Fin m) (c : Fˣ) (a : F) :
    hdiag m F s c * SpecialLinearGroup.transvection
        (Fin.castSucc_lt_succ (i := s)).ne a =
      SpecialLinearGroup.transvection (Fin.castSucc_lt_succ (i := s)).ne
          (((c : F) * (c : F)) * a) * hdiag m F s c := by
  let d : Fin (m + 1) → F := fun i =>
    if i = s.castSucc then (c : F) else if i = s.succ then ((c⁻¹ : Fˣ) : F) else 1
  have hdiag_eq : ((hdiag m F s c : SpecialLinearGroup (Fin (m + 1)) F) :
      Matrix (Fin (m + 1)) (Fin (m + 1)) F) = Matrix.diagonal d := by
    rw [hdiag_matrix]
  have hconj := conj_transvection_of_coe_eq_diagonal (g := hdiag m F s c) (d := d)
    hdiag_eq (Fin.castSucc_lt_succ (i := s)).ne a
  have hd : d s.castSucc * a * (d s.succ)⁻¹ = ((c : F) * (c : F)) * a := by
    simp [d, (Fin.castSucc_lt_succ (i := s)).ne.symm]
    ring
  have h1 : hdiag m F s c * SpecialLinearGroup.transvection
        (Fin.castSucc_lt_succ (i := s)).ne a =
      (hdiag m F s c * SpecialLinearGroup.transvection
        (Fin.castSucc_lt_succ (i := s)).ne a * (hdiag m F s c)⁻¹) * hdiag m F s c := by
    group
  rw [h1, hconj, hd]

theorem coverId_nhat_eq (s : Fin m) :
    (coverId m F 2).nhat s = (curtisDatum m F 2).n s := by
  rw [CentralCoverData.nhat]
  have h := (coverId m F 2).map_nhatW ((curtisCoxeterSystem m).simple s)
  simp only [MonoidHom.id_apply] at h
  rw [h, CentralCoverData.nW_simple]

omit [Finite F] [CharP F 2] in
theorem toGL_upperUnipotentSL (hA : IsUpperGL A) :
    Matrix.SpecialLinearGroup.toGL (upperUnipotentSL m F A hA) =
      upperUnipotentGL m F A hA := by
  ext
  rfl

omit [Finite F] [CharP F 2] in
theorem stdAut_zero_factor (hA : IsUpperGL A) (σ : F ≃+* F) :
    CFSG.QuasithinUnique.K1.stdAut A σ 0 =
      MulAut.conj (upperUnipotentSL m F A hA) *
        CatalogueBHigherLinearAction.slConjugation (m + 1) F
          (upperDiagGL m F A hA) *
        CatalogueBHigherLinearField.slFieldAut (Fin (m + 1)) F σ := by
  rw [CFSG.QuasithinUnique.K1.stdAut, pow_zero, mul_one]
  set u := upperUnipotentSL m F A hA with hu
  set t := upperDiagGL m F A hA with ht
  have hAdecomp : A = Matrix.SpecialLinearGroup.toGL u * t := by
    have h1 : A = upperUnipotentGL m F A hA * upperDiagGL m F A hA :=
      eq_upperUnipotent_mul_diag m F A hA
    rw [h1, hu, ht, toGL_upperUnipotentSL]
  calc
    CatalogueBHigherLinearAction.slConjugation (m + 1) F A *
        CatalogueBHigherLinearField.slFieldAut (Fin (m + 1)) F σ =
      CatalogueBHigherLinearAction.slConjugation (m + 1) F
          (Matrix.SpecialLinearGroup.toGL u * t) *
        CatalogueBHigherLinearField.slFieldAut (Fin (m + 1)) F σ := by rw [hAdecomp]
    _ = (CatalogueBHigherLinearAction.slConjugation (m + 1) F
            (Matrix.SpecialLinearGroup.toGL u) *
          CatalogueBHigherLinearAction.slConjugation (m + 1) F t) *
        CatalogueBHigherLinearField.slFieldAut (Fin (m + 1)) F σ := by rw [map_mul]
    _ = (MulAut.conj u *
          CatalogueBHigherLinearAction.slConjugation (m + 1) F t) *
        CatalogueBHigherLinearField.slFieldAut (Fin (m + 1)) F σ := by
      have hconj : CatalogueBHigherLinearAction.slConjugation (m + 1) F
          (Matrix.SpecialLinearGroup.toGL u) = MulAut.conj u := by
        ext g
        rw [slConjugation_toGL, MulAut.conj_apply]
      rw [hconj]

private theorem heckeT_comp_stdAut_zero_apply (A : GL (Fin (m + 1)) F) (hA : IsUpperGL A)
    (σ : F ≃+* F) {k V : Type*} [Field k] [AddCommGroup V] [Module k V]
    (ρ : Representation k (SpecialLinearGroup (Fin (m + 1)) F) V) (s : Fin m) {y : V}
    (hy : y ∈ (coverId m F 2).datum.fixU ρ) :
    (coverId m F 2).datum.heckeT (ρ.comp (CFSG.QuasithinUnique.K1.stdAut A σ 0).toMonoidHom) s y =
      ρ (upperUnipotentSL m F A hA)
        (ρ (hdiag m F s (upperDiag m F A hA s.castSucc * (upperDiag m F A hA s.succ)⁻¹))
          ((coverId m F 2).datum.heckeT ρ s y)) := by
  let : Fintype F := Fintype.ofFinite F
  set lam : Fˣ := upperDiag m F A hA s.castSucc * (upperDiag m F A hA s.succ)⁻¹ with hlam
  set n : SpecialLinearGroup (Fin (m + 1)) F := weylRep m F s with hn
  have hn' : (coverId m F 2).nhat s = n := by
    rw [hn, coverId_nhat_eq]
    rfl
  set u : SpecialLinearGroup (Fin (m + 1)) F := upperUnipotentSL m F A hA with hu
  set h' : SpecialLinearGroup (Fin (m + 1)) F := n⁻¹ * hdiag m F s lam * n with hh'
  have hyu : ρ u⁻¹ y = y := by
    have hyU : y ∈ (coverId m F 2).datum.fixU ρ := hy
    rw [CurtisDatum.mem_fixU] at hyU
    refine hyU u⁻¹ ?_
    rw [coverId_datum_U, hu]
    exact inv_mem (upperUnipotentSL_mem_U m F A hA)
  have hdtv (a : F) : (CatalogueBHigherLinearAction.slConjugation (m + 1) F
      (TauCeti.diagGL (upperDiag m F A hA)))
      (SpecialLinearGroup.transvection (Fin.castSucc_lt_succ (i := s)).ne (σ a)) =
      SpecialLinearGroup.transvection (Fin.castSucc_lt_succ (i := s)).ne ((lam : F) * σ a) := by
    rw [slConjugation_diagGL_transvection]
    congr 1
    simp only [lam, Units.val_mul, Units.val_inv_eq_inv_val]
    ring
  have hdw : (CatalogueBHigherLinearAction.slConjugation (m + 1) F
      (TauCeti.diagGL (upperDiag m F A hA))) (weylRep m F s) =
      hdiag m F s lam * weylRep m F s := by
    rw [slConjugation_diagGL_weylRep]
  have hfull : ∀ a : F,
      (CatalogueBHigherLinearAction.slConjugation (m + 1) F (upperDiagGL m F A hA))
        ((CatalogueBHigherLinearField.slFieldAut (Fin (m + 1)) F σ)
          ((rankOne m F 2).x s a * weylRep m F s)) =
      (rankOne m F 2).x s ((lam : F) * σ a) * weylRep m F s * h' := by
    intro a
    change (CatalogueBHigherLinearAction.slConjugation (m + 1) F (upperDiagGL m F A hA))
      ((CatalogueBHigherLinearField.slFieldAut (Fin (m + 1)) F σ)
        (SpecialLinearGroup.transvection (Fin.castSucc_lt_succ (i := s)).ne a *
          weylRep m F s)) =
      SpecialLinearGroup.transvection (Fin.castSucc_lt_succ (i := s)).ne ((lam : F) * σ a) *
        weylRep m F s * h'
    rw [map_mul, CFSG.StandardType.slFieldAut_transvection, CFSG.StandardType.slFieldAut_weylRep]
    rw [map_mul]
    rw [show (CatalogueBHigherLinearAction.slConjugation (m + 1) F (upperDiagGL m F A hA))
        (SpecialLinearGroup.transvection (Fin.castSucc_lt_succ (i := s)).ne (σ a)) =
        SpecialLinearGroup.transvection (Fin.castSucc_lt_succ (i := s)).ne ((lam : F) * σ a) from by
      simpa [upperDiagGL] using hdtv a]
    rw [show (CatalogueBHigherLinearAction.slConjugation (m + 1) F (upperDiagGL m F A hA))
        (weylRep m F s) = hdiag m F s lam * weylRep m F s from by
      simpa [upperDiagGL] using hdw]
    rw [← hn, hh']
    group
  have hterm : ∀ a : F,
      (CFSG.QuasithinUnique.K1.stdAut A σ 0) ((rankOne m F 2).x s a * n) =
        u * ((rankOne m F 2).x s ((lam : F) * σ a) * n * h') * u⁻¹ := by
    intro a
    rw [stdAut_zero_factor m F A hA σ]
    simp only [MulAut.mul_apply, MulAut.conj_apply]
    rw [← hu]
    have h := hfull a
    simpa [hn, hn'] using congrArg
      (fun z => u * z * u⁻¹) h
  have hT' : (coverId m F 2).datum.heckeT
      (ρ.comp (CFSG.QuasithinUnique.K1.stdAut A σ 0).toMonoidHom) s y =
      ∑ a : F, ρ ((CFSG.QuasithinUnique.K1.stdAut A σ 0)
        ((rankOne m F 2).x s a * n)) y := by
    rw [CoverRankOne.heckeT_datum (C := coverId m F 2) (R := rankOne m F 2)
      (ρ := ρ.comp (CFSG.QuasithinUnique.K1.stdAut A σ 0).toMonoidHom) (s := s) (v := y),
      hn']
    rfl
  have hT : (coverId m F 2).datum.heckeT ρ s y =
      ∑ a : F, ρ ((rankOne m F 2).x s a * n) y := by
    rw [CoverRankOne.heckeT_datum (C := coverId m F 2) (R := rankOne m F 2) (ρ := ρ)
      (s := s) (v := y),
      hn']
  have hnh : n * h' = hdiag m F s lam * n := by
    rw [hh']
    group
  have hx : ∀ b : F,
      SpecialLinearGroup.transvection (Fin.castSucc_lt_succ (i := s)).ne b *
          hdiag m F s lam =
        hdiag m F s lam *
          SpecialLinearGroup.transvection (Fin.castSucc_lt_succ (i := s)).ne
            (((lam⁻¹ : Fˣ) : F) * ((lam⁻¹ : Fˣ) : F) * b) := by
    intro b
    have h := hdiag_mul_transvection (m := m) (F := F) s lam⁻¹ b
    rw [← hdiag_inv m F s lam] at h
    calc
      SpecialLinearGroup.transvection (Fin.castSucc_lt_succ (i := s)).ne b * hdiag m F s lam
          = hdiag m F s lam * ((hdiag m F s lam)⁻¹ *
              SpecialLinearGroup.transvection (Fin.castSucc_lt_succ (i := s)).ne b) *
            hdiag m F s lam := by group
      _ = hdiag m F s lam *
            (SpecialLinearGroup.transvection (Fin.castSucc_lt_succ (i := s)).ne
              (((lam⁻¹ : Fˣ) : F) * ((lam⁻¹ : Fˣ) : F) * b) * (hdiag m F s lam)⁻¹) *
            hdiag m F s lam := by rw [h]
      _ = hdiag m F s lam *
            SpecialLinearGroup.transvection (Fin.castSucc_lt_succ (i := s)).ne
              (((lam⁻¹ : Fˣ) : F) * ((lam⁻¹ : Fˣ) : F) * b) := by group
  have hx' : ∀ a : F,
      SpecialLinearGroup.transvection (Fin.castSucc_lt_succ (i := s)).ne ((lam : F) * σ a) *
          hdiag m F s lam =
        hdiag m F s lam *
          SpecialLinearGroup.transvection (Fin.castSucc_lt_succ (i := s)).ne
            (((lam⁻¹ : Fˣ) : F) * σ a) := by
    intro a
    rw [hx]
    congr 1
    congr 1
    simp only [Units.val_inv_eq_inv_val]
    field_simp
  calc
    (coverId m F 2).datum.heckeT (ρ.comp (CFSG.QuasithinUnique.K1.stdAut A σ 0).toMonoidHom) s y
        = ∑ a : F, ρ ((CFSG.QuasithinUnique.K1.stdAut A σ 0)
            ((rankOne m F 2).x s a * n)) y := hT'
    _ = ∑ a : F, ρ u (ρ ((rankOne m F 2).x s ((lam : F) * σ a) * n * h') y) := by
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [hterm a]
      simp only [map_mul, Module.End.mul_apply, hyu]
    _ = ρ u (∑ a : F, ρ ((rankOne m F 2).x s ((lam : F) * σ a) * n * h') y) := by
      rw [map_sum]
    _ = ρ u (∑ a : F, ρ ((rankOne m F 2).x s ((lam : F) * σ a) * n) (ρ h' y)) := by
      congr 1
      refine Finset.sum_congr rfl fun a _ => ?_
      simp only [map_mul, Module.End.mul_apply]
    _ = ρ u (∑ a : F, ρ ((rankOne m F 2).x s ((lam : F) * σ a) *
          hdiag m F s lam * n) y) := by
      congr 1
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [← Module.End.mul_apply, ← map_mul]
      congr 1
      rw [hh']
      group
    _ = ρ u (∑ a : F, ρ (hdiag m F s lam *
          (rankOne m F 2).x s (((lam⁻¹ : Fˣ) : F) * σ a) * n) y) := by
      congr 1
      refine Finset.sum_congr rfl fun a _ => ?_
      change ρ (SpecialLinearGroup.transvection (Fin.castSucc_lt_succ (i := s)).ne
          ((lam : F) * σ a) * hdiag m F s lam * n) y =
        ρ (hdiag m F s lam * SpecialLinearGroup.transvection
          (Fin.castSucc_lt_succ (i := s)).ne (((lam⁻¹ : Fˣ) : F) * σ a) * n) y
      rw [hx']
    _ = ρ u (ρ (hdiag m F s lam)
          (∑ a : F, ρ (((rankOne m F 2).x s (((lam⁻¹ : Fˣ) : F) * σ a)) * n) y)) := by
      congr 1
      rw [map_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      simp only [map_mul, Module.End.mul_apply]
    _ = ρ u (ρ (hdiag m F s lam) (∑ b : F, ρ ((rankOne m F 2).x s b * n) y)) := by
      congr 1
      congr 1
      exact Equiv.sum_comp (Equiv.ofBijective (fun a : F => ((lam⁻¹ : Fˣ) : F) * (σ a))
        (Function.Bijective.comp (mulLeft_bijective₀ ((lam⁻¹ : Fˣ) : F) (Units.ne_zero _))
          σ.bijective))
        (fun b : F => ρ ((rankOne m F 2).x s b * n) y)
    _ = ρ u (ρ (hdiag m F s lam) ((coverId m F 2).datum.heckeT ρ s y)) := by
      rw [hT]

theorem heckeT_comp_stdAut_zero_eq_zero_iff (A : GL (Fin (m + 1)) F) (hA : IsUpperGL A)
    (σ : F ≃+* F) {k V : Type*} [Field k] [AddCommGroup V] [Module k V]
    (ρ : Representation k (SpecialLinearGroup (Fin (m + 1)) F) V) (s : Fin m) {y : V}
    (hy : y ∈ (coverId m F 2).datum.fixU ρ) :
    (coverId m F 2).datum.heckeT (ρ.comp (CFSG.QuasithinUnique.K1.stdAut A σ 0).toMonoidHom) s y =
        0 ↔
      (coverId m F 2).datum.heckeT ρ s y = 0 := by
  rw [heckeT_comp_stdAut_zero_apply (A := A) (hA := hA) (σ := σ) (ρ := ρ) (s := s) (hy := hy)]
  have hu_inj : Function.Injective (ρ (upperUnipotentSL m F A hA)) := by
    intro a b h
    have := congrArg (ρ (upperUnipotentSL m F A hA)⁻¹) h
    simpa only [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one,
      Module.End.one_apply] using this
  have hd_inj : Function.Injective
      (ρ (hdiag m F s (upperDiag m F A hA s.castSucc * (upperDiag m F A hA s.succ)⁻¹))) := by
    intro a b h
    have := congrArg (ρ (hdiag m F s (upperDiag m F A hA s.castSucc *
      (upperDiag m F A hA s.succ)⁻¹))⁻¹) h
    simpa only [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one,
      Module.End.one_apply] using this
  constructor
  · intro h
    have h1 : ρ (hdiag m F s (upperDiag m F A hA s.castSucc *
        (upperDiag m F A hA s.succ)⁻¹))
        ((coverId m F 2).datum.heckeT ρ s y) = 0 := hu_inj (by simpa using h)
    exact hd_inj (by simpa using h1)
  · intro h
    simp [h]

theorem isCoverType_comp_stdAut_zero.{uK, vV} (A : GL (Fin (m + 1)) F)
    (hA : IsUpperGL A) (σ : F ≃+* F)
    {k : Type uK} {V : Type vV} [Field k] [AddCommGroup V] [Module k V]
    {ρ : Representation k (SpecialLinearGroup (Fin (m + 1)) F) V} {y : V} {χ : _ → k}
    {J : Finset (Fin m)}
    (ht : IsCoverType (rankOne m F 2) ρ y χ J) :
    IsCoverType (rankOne m F 2)
      (ρ.comp (CFSG.QuasithinUnique.K1.stdAut A σ 0).toMonoidHom) y
      (χ ∘ CatalogueBHigherLinearField.slFieldAut (Fin (m + 1)) F σ) J := by
  unfold IsCoverType at ht ⊢
  rw [CurtisDatum.mem_fixU] at ht
  rw [coverId_datum_U m F 2] at ht
  refine ⟨?_, ht.2.1, ?_, ?_⟩
  · rw [CurtisDatum.mem_fixU]
    intro u hu
    rw [MonoidHom.comp_apply]
    change ρ ((CFSG.QuasithinUnique.K1.stdAut A σ 0) u) y = y
    rw [coverId_datum_U m F 2] at hu
    exact ht.1 _ (stdAut_zero_mem_U m F A hA σ hu)
  · intro h hh
    rw [MonoidHom.comp_apply]
    have hhH : h ∈ (curtisDatum m F 2).H := by simpa using hh
    change ρ ((CFSG.QuasithinUnique.K1.stdAut A σ 0) h) y =
      χ (CatalogueBHigherLinearField.slFieldAut (Fin (m + 1)) F σ h) • y
    set h' : SpecialLinearGroup (Fin (m + 1)) F :=
      CatalogueBHigherLinearField.slFieldAut (Fin (m + 1)) F σ h with hh'
    have hu : h'⁻¹ * (CFSG.QuasithinUnique.K1.stdAut A σ 0) h ∈
        (curtisDatum m F 2).U :=
      stdAut_zero_torus m F A hA σ hhH
    have hEq : (CFSG.QuasithinUnique.K1.stdAut A σ 0) h =
        h' * (h'⁻¹ * (CFSG.QuasithinUnique.K1.stdAut A σ 0) h) := by group
    rw [hEq, map_mul]
    change ρ h' (ρ (h'⁻¹ * (CFSG.QuasithinUnique.K1.stdAut A σ 0) h) y) =
      χ h' • y
    have hfix : ρ (h'⁻¹ * (CFSG.QuasithinUnique.K1.stdAut A σ 0) h) y = y :=
      ht.1 _ hu
    rw [hfix]
    exact ht.2.2.1 h'
      (by simpa [hh'] using slFieldAut_mem_H (m := m) (F := F) σ hhH)
  · intro s
    have hyU : y ∈ (coverId m F 2).datum.fixU ρ := by
      rw [CurtisDatum.mem_fixU]
      intro u hu
      rw [coverId_datum_U m F 2] at hu
      exact ht.1 u hu
    have hhecke := heckeT_comp_stdAut_zero_eq_zero_iff (A := A) (hA := hA) (σ := σ)
      (ρ := ρ) (s := s) (hy := hyU)
    have hchar : (∀ u : ((fun x => F) s)ˣ,
        (χ ∘ CatalogueBHigherLinearField.slFieldAut (Fin (m + 1)) F σ)
          ((rankOne m F 2).hh s u) = 1) ↔
        (∀ u : ((fun x => F) s)ˣ, χ ((rankOne m F 2).hh s u) = 1) := by
      constructor
      · intro hχ u
        have h := hχ (Units.map σ.symm.toMonoidHom u)
        have hcomp : (Units.map σ.toMonoidHom) ((Units.map σ.symm.toMonoidHom) u) = u := by
          ext
          simp [Units.coe_map, RingEquiv.apply_symm_apply]
        have hh : CatalogueBHigherLinearField.slFieldAut (Fin (m + 1)) F σ
            (hdiag m F s ((Units.map σ.symm.toMonoidHom) u)) = hdiag m F s u := by
          rw [slFieldAut_hdiag, hcomp]
        have h' : χ (hdiag m F s u) = 1 := by
          rw [← hh]
          simpa [Function.comp, rankOne] using h
        simpa [rankOne] using h'
      · intro hχ u
        have h := hχ (Units.map σ.toMonoidHom u)
        simpa [Function.comp, slFieldAut_hdiag, rankOne, Units.coe_map] using h
    constructor
    · intro hs
      have h := (ht.2.2.2 s).mp hs
      exact ⟨hchar.mpr h.1, hhecke.mpr h.2⟩
    · rintro ⟨hχ, hT⟩
      exact (ht.2.2.2 s).mpr ⟨hchar.mp hχ, hhecke.mp hT⟩

theorem isCoverType_comp_borelStd.{uK, vV} (A : GL (Fin (m + 1)) F) (hA : IsUpperGL A)
    (σ : F ≃+* F) {ε : ℕ} (hε : ε ≤ 1)
    {k : Type uK} {V : Type vV} [Field k] [AddCommGroup V] [Module k V]
    {ρ : Representation k (SpecialLinearGroup (Fin (m + 1)) F) V} {y : V} {χ : _ → k}
    {J : Finset (Fin m)}
    (ht : IsCoverType (rankOne m F 2) ρ y χ J) :
    IsCoverType (rankOne m F 2)
      (ρ.comp (borelStd (m + 1) F A σ ε).toMonoidHom) y
      (borelStdChar (m := m) (k := k) (χ := χ) (σ := σ) (ε := ε))
      (borelStdSet (m := m) J ε) := by
  have hε' : ε = 0 ∨ ε = 1 := by omega
  rcases hε' with rfl | rfl
  · simpa [borelStdSet, borelStdChar, borelStd_zero] using
      isCoverType_comp_stdAut_zero (m := m) (F := F) (A := A) hA σ ht
  · have hstd := isCoverType_comp_stdAut_zero (m := m) (F := F) (A := A) hA σ ht
    have hgraph := isCoverType_comp_borelGraph (m := m) (F := F) hstd
    have hcomp : (CFSG.QuasithinUnique.K1.stdAut A σ 0 * borelGraph (m + 1) F).toMonoidHom =
        (CFSG.QuasithinUnique.K1.stdAut A σ 0).toMonoidHom.comp
          (borelGraph (m + 1) F).toMonoidHom := rfl
    rw [show borelStd (m + 1) F A σ 1 = CFSG.QuasithinUnique.K1.stdAut A σ 0 *
        borelGraph (m + 1) F from rfl, hcomp, ← MonoidHom.comp_assoc]
    simpa [borelStdSet, borelStdChar] using hgraph

theorem coverType_intertwine_unique (hA : IsUpperGL A) (σ : F ≃+* F) {ε : ℕ} (hε : ε = 1)
    {k : Type} {V : Type} [Field k] [Algebra F k] [AddCommGroup V] [Module k V]
    [CharP k 2]
    {ρ : Representation k (SpecialLinearGroup (Fin (m + 1)) F) V} (hρ : IsSimpleRep ρ)
    {y : V} {χ : _ → k} {J : Finset (Fin m)}
    {T : V ≃ₗ[k] V}
    (hT : ∀ g v, T (ρ g v) = ρ (borelStd (m + 1) F A σ ε g) (T v))
    (ht : IsCoverType (rankOne m F 2) ρ y χ J) :
    (∀ h ∈ (curtisDatum m F 2).H,
        ((χ ∘ CatalogueBHigherLinearField.slFieldAut (Fin (m + 1)) F σ) ∘
          borelGraph (m + 1) F) h = χ h) ∧
      borelStdSet (m := m) J ε = J := by
  have htw := isCoverType_comp_borelStd (m := m) (F := F) (A := A) hA σ (ε := ε)
    (by rw [hε]) ht
  have hsymm : ∀ g v,
      T.symm ((ρ.comp (borelStd (m + 1) F A σ ε).toMonoidHom) g v) = ρ g (T.symm v) := by
    intro g v
    have h := congrArg T.symm (hT g (T.symm v))
    simpa [T.apply_symm_apply] using h.symm
  have htrans := IsCoverType.of_linearEquiv (e := T.symm) hsymm htw
  have htrans' : IsCoverType (rankOne m F 2) ρ (T.symm y)
      ((χ ∘ CatalogueBHigherLinearField.slFieldAut (Fin (m + 1)) F σ) ∘
        borelGraph (m + 1) F) (borelStdSet (m := m) J ε) := by
    simpa [borelStdChar, hε] using htrans
  exact isCoverType_unique_sl (m := m) (F := F) (p := 2) hρ htrans' ht

theorem coverType_rev_eq_of_intertwine (hA : IsUpperGL A) (σ : F ≃+* F) {ε : ℕ} (hε : ε = 1)
    {k : Type} {V : Type} [Field k] [Algebra F k] [AddCommGroup V] [Module k V]
    [CharP k 2]
    {ρ : Representation k (SpecialLinearGroup (Fin (m + 1)) F) V} (hρ : IsSimpleRep ρ)
    {y : V} {χ : _ → k} {J : Finset (Fin m)}
    {T : V ≃ₗ[k] V}
    (hT : ∀ g v, T (ρ g v) = ρ (borelStd (m + 1) F A σ ε g) (T v))
    (ht : IsCoverType (rankOne m F 2) ρ y χ J) :
    J.map Fin.revPerm.toEmbedding = J := by
  have h := (coverType_intertwine_unique (m := m) (F := F) A hA σ hε hρ hT ht).2
  simpa [borelStdSet, hε] using h

theorem mem_iff_rev_mem_of_intertwine (hA : IsUpperGL A) (σ : F ≃+* F) {ε : ℕ} (hε : ε = 1)
    {k : Type} {V : Type} [Field k] [Algebra F k] [AddCommGroup V] [Module k V]
    [CharP k 2]
    {ρ : Representation k (SpecialLinearGroup (Fin (m + 1)) F) V} (hρ : IsSimpleRep ρ)
    {y : V} {χ : _ → k} {J : Finset (Fin m)}
    {T : V ≃ₗ[k] V}
    (hT : ∀ g v, T (ρ g v) = ρ (borelStd (m + 1) F A σ ε g) (T v))
    (ht : IsCoverType (rankOne m F 2) ρ y χ J) (s : Fin m) :
    s ∈ J ↔ Fin.rev s ∈ J := by
  have h := coverType_rev_eq_of_intertwine (m := m) (F := F) A hA σ hε hρ hT ht
  constructor
  · intro hs
    have hm : Fin.rev s ∈ J.map Fin.revPerm.toEmbedding :=
      Finset.mem_map.mpr ⟨s, hs, rfl⟩
    rwa [h] at hm
  · intro hs
    have hm : s ∈ J.map Fin.revPerm.toEmbedding :=
      Finset.mem_map.mpr ⟨Fin.rev s, hs, by simp [Fin.revPerm]⟩
    rwa [h] at hm

end CFSG.LieType.SpecialLinear
