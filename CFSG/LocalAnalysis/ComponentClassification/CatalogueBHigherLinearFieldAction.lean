module

public import CFSG.Adapters.LinearFieldTransport
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.ProjectiveSemilinear

public section

namespace CFSG.ComponentClassification.CatalogueBHigherLinearField

noncomputable section

open Matrix

universe u v

@[expose] def glFieldEquiv {K : Type u} {F : Type v} [Field K] [Field F]
    (ι : Type*) [Fintype ι] [DecidableEq ι] (e : K ≃+* F) :
    GL ι K ≃* GL ι F where
  toFun := GeneralLinearGroup.map e.toRingHom
  invFun := GeneralLinearGroup.map e.symm.toRingHom
  left_inv A := by
    apply GeneralLinearGroup.ext
    intro i j
    exact e.symm_apply_apply (A i j)
  right_inv A := by
    apply GeneralLinearGroup.ext
    intro i j
    exact e.apply_symm_apply (A i j)
  map_mul' := map_mul _

theorem glFieldEquiv_entry {K : Type u} {F : Type v} [Field K] [Field F]
    (ι : Type*) [Fintype ι] [DecidableEq ι] (e : K ≃+* F)
    (A : GL ι K) (i j : ι) : glFieldEquiv ι e A i j = e (A i j) := rfl

theorem glFieldEquiv_scalar {K : Type u} {F : Type v} [Field K] [Field F]
    (ι : Type*) [Fintype ι] [DecidableEq ι] (e : K ≃+* F) (c : Kˣ) :
    glFieldEquiv ι e (GeneralLinearGroup.scalar ι c) =
      GeneralLinearGroup.scalar ι (Units.map e.toMonoidHom c) :=
  GeneralLinearGroup.map_scalar e.toRingHom c

abbrev slFieldEquiv {K : Type u} {F : Type v} [Field K] [Field F]
    (ι : Type*) [Fintype ι] [DecidableEq ι] (e : K ≃+* F) :
    SpecialLinearGroup ι K ≃* SpecialLinearGroup ι F :=
  CFSG.ClassicalModels.specialLinearFieldEquiv e ι

theorem slFieldEquiv_entry {K : Type u} {F : Type v} [Field K] [Field F]
    (ι : Type*) [Fintype ι] [DecidableEq ι] (e : K ≃+* F)
    (A : SpecialLinearGroup ι K) (i j : ι) :
    slFieldEquiv ι e A i j = e (A i j) := rfl

theorem toGL_slFieldEquiv {K : Type u} {F : Type v} [Field K] [Field F]
    (ι : Type*) [Fintype ι] [DecidableEq ι] (e : K ≃+* F)
    (A : SpecialLinearGroup ι K) :
    SpecialLinearGroup.toGL (slFieldEquiv ι e A) =
      glFieldEquiv ι e (SpecialLinearGroup.toGL A) := by
  apply GeneralLinearGroup.ext
  intro i j
  rfl

@[expose] def pglFieldEquiv {K : Type u} {F : Type v} [Field K] [Field F]
    (ι : Type*) [Fintype ι] [DecidableEq ι] (e : K ≃+* F) :
    ProjGenLinGroup ι K ≃* ProjGenLinGroup ι F where
  toFun := ProjGenLinGroup.map e.toRingHom
  invFun := ProjGenLinGroup.map e.symm.toRingHom
  left_inv x := by
    obtain ⟨A, rfl⟩ := ProjGenLinGroup.mk_surjective x
    change ProjGenLinGroup.mk (glFieldEquiv ι e.symm (glFieldEquiv ι e A)) = _
    congr 1
    apply GeneralLinearGroup.ext
    intro i j
    exact e.symm_apply_apply (A i j)
  right_inv x := by
    obtain ⟨A, rfl⟩ := ProjGenLinGroup.mk_surjective x
    change ProjGenLinGroup.mk (glFieldEquiv ι e (glFieldEquiv ι e.symm A)) = _
    congr 1
    apply GeneralLinearGroup.ext
    intro i j
    exact e.apply_symm_apply (A i j)
  map_mul' := map_mul _

theorem pglFieldEquiv_mk {K : Type u} {F : Type v} [Field K] [Field F]
    (ι : Type*) [Fintype ι] [DecidableEq ι] (e : K ≃+* F) (A : GL ι K) :
    pglFieldEquiv ι e (ProjGenLinGroup.mk A) =
      ProjGenLinGroup.mk (GeneralLinearGroup.map e.toRingHom A) := rfl

abbrev pslFieldEquiv {K : Type u} {F : Type v} [Field K] [Field F]
    (ι : Type*) [Fintype ι] [DecidableEq ι] (e : K ≃+* F) :
    ProjectiveSpecialLinearGroup ι K ≃* ProjectiveSpecialLinearGroup ι F :=
  CFSG.ClassicalModels.projectiveSpecialLinearFieldEquiv e ι

theorem pslFieldEquiv_mk {K : Type u} {F : Type v} [Field K] [Field F]
    (ι : Type*) [Fintype ι] [DecidableEq ι] (e : K ≃+* F)
    (A : SpecialLinearGroup ι K) :
    pslFieldEquiv ι e (QuotientGroup.mk A) =
      QuotientGroup.mk (SpecialLinearGroup.map e.toRingHom A) := rfl

theorem toPGL_pslFieldEquiv {K : Type u} {F : Type v} [Field K] [Field F]
    (ι : Type*) [Fintype ι] [DecidableEq ι] (e : K ≃+* F)
    (x : ProjectiveSpecialLinearGroup ι K) :
    ProjectiveSpecialLinearGroup.toPGL (pslFieldEquiv ι e x) =
      pglFieldEquiv ι e (ProjectiveSpecialLinearGroup.toPGL x) := by
  obtain ⟨A, rfl⟩ := QuotientGroup.mk'_surjective
    (Subgroup.center (SpecialLinearGroup ι K)) x
  change ProjGenLinGroup.mk (SpecialLinearGroup.toGL (slFieldEquiv ι e A)) =
    ProjGenLinGroup.mk (glFieldEquiv ι e (SpecialLinearGroup.toGL A))
  rw [toGL_slFieldEquiv]

@[expose] def glFieldAut (ι : Type*) [Fintype ι] [DecidableEq ι]
    (K : Type u) [Field K] : (K ≃+* K) →* MulAut (GL ι K) where
  toFun := glFieldEquiv ι
  map_one' := by ext A i j; rfl
  map_mul' _ _ := by ext A i j; rfl

@[expose] def slFieldAut (ι : Type*) [Fintype ι] [DecidableEq ι]
    (K : Type u) [Field K] : (K ≃+* K) →* MulAut (SpecialLinearGroup ι K) where
  toFun := slFieldEquiv ι
  map_one' := by ext A i j; rfl
  map_mul' _ _ := by ext A i j; rfl

@[expose] def pglFieldAut (ι : Type*) [Fintype ι] [DecidableEq ι]
    (K : Type u) [Field K] : (K ≃+* K) →* MulAut (ProjGenLinGroup ι K) where
  toFun := pglFieldEquiv ι
  map_one' := by
    ext x
    obtain ⟨A, rfl⟩ := ProjGenLinGroup.mk_surjective x
    rfl
  map_mul' _ _ := by
    ext x
    obtain ⟨A, rfl⟩ := ProjGenLinGroup.mk_surjective x
    rfl

@[expose] def pslFieldAut (ι : Type*) [Fintype ι] [DecidableEq ι]
    (K : Type u) [Field K] :
    (K ≃+* K) →* MulAut (ProjectiveSpecialLinearGroup ι K) where
  toFun := pslFieldEquiv ι
  map_one' := by
    ext x
    obtain ⟨A, rfl⟩ := QuotientGroup.mk'_surjective
      (Subgroup.center (SpecialLinearGroup ι K)) x
    rfl
  map_mul' _ _ := by
    ext x
    obtain ⟨A, rfl⟩ := QuotientGroup.mk'_surjective
      (Subgroup.center (SpecialLinearGroup ι K)) x
    rfl

theorem pslFieldAut_mk (ι : Type*) [Fintype ι] [DecidableEq ι]
    (K : Type u) [Field K] (sigma : K ≃+* K) (A : SpecialLinearGroup ι K) :
    pslFieldAut ι K sigma (QuotientGroup.mk A) =
      QuotientGroup.mk (SpecialLinearGroup.map sigma.toRingHom A) := rfl

theorem toPGL_pslFieldAut (ι : Type*) [Fintype ι] [DecidableEq ι]
    (K : Type u) [Field K] (sigma : K ≃+* K)
    (x : ProjectiveSpecialLinearGroup ι K) :
    ProjectiveSpecialLinearGroup.toPGL (pslFieldAut ι K sigma x) =
      pglFieldAut ι K sigma (ProjectiveSpecialLinearGroup.toPGL x) :=
  toPGL_pslFieldEquiv ι sigma x

theorem pglFieldAut_two (K : Type u) [Field K] :
    pglFieldAut (Fin 2) K = CFSG.GorensteinWalter.pgl2FieldAut K := by
  ext sigma x
  obtain ⟨A, rfl⟩ := ProjGenLinGroup.mk_surjective x
  change QuotientGroup.mk' (Subgroup.center _) (GeneralLinearGroup.map sigma.toRingHom A) =
    CFSG.GorensteinWalter.pgl2RingEquiv sigma (QuotientGroup.mk' (Subgroup.center _) A)
  exact (CFSG.GorensteinWalter.pgl2RingEquiv_mk sigma A).symm

theorem pslFieldAut_two (K : Type u) [Field K] :
    pslFieldAut (Fin 2) K = CFSG.GorensteinWalter.psl2FieldAut K := by
  ext sigma x
  obtain ⟨A, rfl⟩ := QuotientGroup.mk'_surjective
    (Subgroup.center (SpecialLinearGroup (Fin 2) K)) x
  change QuotientGroup.mk' (Subgroup.center _) (SpecialLinearGroup.map sigma.toRingHom A) =
    CFSG.GorensteinWalter.psl2RingEquiv sigma (QuotientGroup.mk' (Subgroup.center _) A)
  exact (CFSG.GorensteinWalter.psl2RingEquiv_mk sigma A).symm

end

end CFSG.ComponentClassification.CatalogueBHigherLinearField
