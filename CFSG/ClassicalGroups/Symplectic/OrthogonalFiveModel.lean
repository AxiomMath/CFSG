module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFiveSymplectic
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticHigherParabolicData
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOddQuadraticIsotropy
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFiveStructure

public noncomputable section

open Matrix QuadraticMap
open CFSG.ComponentClassification
open CFSG.ComponentClassification.CatalogueBOrthogonalFive
open CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag

namespace CFSG.ClassicalGroups.Symplectic

variable {K : Type} [Field K]

theorem selfAdjointSymplecticImage_eq_commutator [Finite K] (hodd : Odd (Nat.card K)) :
    selfAdjointSymplecticImage (CatalogueBOddQuadratic.two_ne_zero_of_odd_card hodd) =
      commutator (TauCeti.QuadraticMap.orthogonalGroup (selfAdjointForm K)) := by
  let h2 := CatalogueBOddQuadratic.two_ne_zero_of_odd_card hodd
  apply le_antisymm
  · haveI : Group.IsPerfect ↥(symplecticMultiplier (K := K)).ker :=
      (symplecticKernel_quasisimple hodd).1
    have hmap : Subgroup.map (selfAdjointSymplecticAction h2) ⁅(⊤ : Subgroup ↥(symplecticMultiplier (K := K)).ker), ⊤⁆ =
        ⁅(selfAdjointSymplecticAction h2).range, (selfAdjointSymplecticAction h2).range⁆ := by
      rw [Subgroup.map_commutator, ← MonoidHom.range_eq_map]
    have hcomm : ⁅(⊤ : Subgroup ↥(symplecticMultiplier (K := K)).ker), ⊤⁆ = ⊤ :=
      Group.IsPerfect.commutator_eq_top
    rw [hcomm, Subgroup.map_top] at hmap
    change (selfAdjointSymplecticAction h2).range ≤
      commutator (TauCeti.QuadraticMap.orthogonalGroup (selfAdjointForm K))
    rw [hmap]
    exact Subgroup.commutator_mono le_top le_top
  · exact selfAdjoint_commutator_le_symplecticImage h2

private theorem coe_mulEquivGLSymplectic_symm (X : TauCeti.GLSymplectic (Fin 2) K) :
    ((TauCeti.GLSymplecticFin.mulEquivGLSymplectic 2 K).symm X : GL (Fin 4) K) =
      Equiv.reindexGL finSumFinEquiv K (X : GL (Fin 2 ⊕ Fin 2) K) := by
  have h := congrArg (fun Z : TauCeti.GLSymplectic (Fin 2) K =>
    (Z : GL (Fin 2 ⊕ Fin 2) K))
    ((TauCeti.GLSymplecticFin.mulEquivGLSymplectic 2 K).apply_symm_apply X)
  rw [TauCeti.GLSymplecticFin.coe_mulEquivGLSymplectic] at h
  have h' := congrArg (Equiv.reindexGL finSumFinEquiv K) h
  simpa [Equiv.reindexGL_symm] using h'

@[expose] noncomputable def statedSpEquivSymplecticKernel :
    StatedSp 2 K ≃* (symplecticMultiplier (K := K)).ker :=
  (MulEquiv.subgroupCongr (statedSp_eq_GLSymplectic (n := 2) (K := K))).trans
    (symplecticKernelEquiv.symm)

theorem statedSpEquivSymplecticKernel_val (A : StatedSp 2 K) :
    ((statedSpEquivSymplecticKernel (K := K) A : (symplecticMultiplier (K := K)).ker) : GL (Fin 4) K) =
      Equiv.reindexGL finSumFinEquiv K (A : GL (Fin 2 ⊕ Fin 2) K) := by
  change ((TauCeti.GLSymplecticFin.mulEquivGLSymplectic 2 K).symm
    ((MulEquiv.subgroupCongr (statedSp_eq_GLSymplectic (n := 2) (K := K))) A) :
      GL (Fin 4) K) = _
  rw [coe_mulEquivGLSymplectic_symm]
  rfl

theorem reindexGL_finSumFinEquiv_scalar (c : Kˣ) :
    Equiv.reindexGL finSumFinEquiv K (GeneralLinearGroup.scalar (Fin 2 ⊕ Fin 2) c) =
      GeneralLinearGroup.scalar (Fin 4) c := by
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  rw [Equiv.coe_reindexGL, Matrix.GeneralLinearGroup.coe_scalar,
    Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.scalar_apply,
    Matrix.submatrix_apply]
  by_cases hij : i = j
  · subst hij; simp
  · simp [hij, Equiv.apply_eq_iff_eq_symm_apply]

noncomputable def selfAdjointStatedSpAction (h2 : (2 : K) ≠ 0) :
    StatedSp 2 K →* TauCeti.QuadraticMap.orthogonalGroup (selfAdjointForm K) :=
  (selfAdjointSymplecticAction h2).comp (statedSpEquivSymplecticKernel (K := K)).toMonoidHom

theorem selfAdjointStatedSpAction_ker (h2 : (2 : K) ≠ 0) :
    (selfAdjointStatedSpAction h2).ker = spScalars 2 K := by
  ext A
  rw [MonoidHom.mem_ker]
  constructor
  · intro hA
    have hA' : selfAdjointOrthogonalAction h2 (statedSpEquivSymplecticKernel (K := K) A).val = 1 := hA
    obtain ⟨c, hc⟩ := (selfAdjointOrthogonalAction_eq_one_iff h2 _).mp hA'
    have hval : ((statedSpEquivSymplecticKernel (K := K) A :
        (symplecticMultiplier (K := K)).ker) : GL (Fin 4) K) =
        GeneralLinearGroup.scalar (Fin 4) c := hc
    have hAeq : (A : GL (Fin 2 ⊕ Fin 2) K) =
        GeneralLinearGroup.scalar (Fin 2 ⊕ Fin 2) c := by
      apply (Equiv.reindexGL finSumFinEquiv K).injective
      rw [← statedSpEquivSymplecticKernel_val A, hval, reindexGL_finSumFinEquiv_scalar]
    rw [Subgroup.mem_subgroupOf, StatedScalars, MonoidHom.mem_range]
    exact ⟨c, hAeq.symm⟩
  · intro hA
    rw [Subgroup.mem_subgroupOf, StatedScalars, MonoidHom.mem_range] at hA
    obtain ⟨c, hc⟩ := hA
    have heA : (statedSpEquivSymplecticKernel (K := K) A).val = selfAdjointScalarSimilitude c := by
      apply Subtype.ext
      apply Units.ext
      change ((((statedSpEquivSymplecticKernel (K := K) A :
          (symplecticMultiplier (K := K)).ker) : GL (Fin 4) K)) :
          Matrix (Fin 4) (Fin 4) K) = _
      rw [congrArg (fun g : GL (Fin 4) K => (g : Matrix (Fin 4) (Fin 4) K))
        (statedSpEquivSymplecticKernel_val (K := K) A)]
      rw [← hc, reindexGL_finSumFinEquiv_scalar]
      rfl
    change selfAdjointOrthogonalAction h2 (statedSpEquivSymplecticKernel (K := K) A).val = 1
    rw [heA]
    exact selfAdjointOrthogonalAction_scalar h2 c

noncomputable def pspFourAction (h2 : (2 : K) ≠ 0) :
    StatedProj (StatedSp 2 K) →*
      TauCeti.QuadraticMap.orthogonalGroup (selfAdjointForm K) :=
  QuotientGroup.lift (spScalars 2 K) (selfAdjointStatedSpAction h2)
    (by rw [← selfAdjointStatedSpAction_ker h2])

theorem pspFourAction_range (h2 : (2 : K) ≠ 0) :
    (pspFourAction h2).range = selfAdjointSymplecticImage h2 := by
  ext g
  constructor
  · rintro ⟨x, rfl⟩
    obtain ⟨A, rfl⟩ := QuotientGroup.mk_surjective x
    exact ⟨statedSpEquivSymplecticKernel (K := K) A, rfl⟩
  · rintro ⟨A, rfl⟩
    refine ⟨QuotientGroup.mk ((statedSpEquivSymplecticKernel (K := K)).symm A), ?_⟩
    change selfAdjointStatedSpAction h2 ((statedSpEquivSymplecticKernel (K := K)).symm A) = _
    simp [selfAdjointStatedSpAction]

theorem pspFourAction_injective (h2 : (2 : K) ≠ 0) :
    Function.Injective (pspFourAction h2) := by
  intro x y hxy
  obtain ⟨A, rfl⟩ := QuotientGroup.mk_surjective x
  obtain ⟨B, rfl⟩ := QuotientGroup.mk_surjective y
  have h1 : selfAdjointStatedSpAction h2 A = selfAdjointStatedSpAction h2 B := by
    simpa [pspFourAction] using hxy
  have h : selfAdjointStatedSpAction h2 (A⁻¹ * B) = 1 := by
    rw [map_mul, map_inv, h1, inv_mul_cancel]
  refine QuotientGroup.eq.mpr ?_
  change A⁻¹ * B ∈ spScalars 2 K
  rw [← selfAdjointStatedSpAction_ker h2]
  exact MonoidHom.mem_ker.mpr h

@[expose] noncomputable def pspFourEquivDerivedOrthogonal [Finite K] (hodd : Odd (Nat.card K)) :
    StatedProj (StatedSp 2 K) ≃*
      commutator (TauCeti.QuadraticMap.orthogonalGroup (selfAdjointForm K)) := by
  let h2 := CatalogueBOddQuadratic.two_ne_zero_of_odd_card hodd
  let psi := pspFourAction (K := K) h2
  have hpsi : Function.Injective psi := pspFourAction_injective h2
  let e : StatedProj (StatedSp 2 K) ≃* psi.range :=
    MulEquiv.ofBijective psi.rangeRestrict
      ⟨fun x y h => hpsi (Subtype.ext_iff.mp h), MonoidHom.rangeRestrict_surjective psi⟩
  have hrange : psi.range = commutator (TauCeti.QuadraticMap.orthogonalGroup
      (selfAdjointForm K)) := by
    rw [show psi = pspFourAction h2 from rfl, pspFourAction_range,
      selfAdjointSymplecticImage_eq_commutator hodd]
  exact e.trans (MulEquiv.subgroupCongr hrange)

theorem pspFourEquivDerivedOrthogonal_proj [Finite K] (hodd : Odd (Nat.card K))
    (x : StatedSp 2 K) :
    (pspFourEquivDerivedOrthogonal (K := K) hodd (proj 2 K x) :
        TauCeti.QuadraticMap.orthogonalGroup (selfAdjointForm K)) =
      selfAdjointOrthogonalAction (CatalogueBOddQuadratic.two_ne_zero_of_odd_card hodd)
        (statedSpEquivSymplecticKernel (K := K) x) := by
  rfl

@[expose] noncomputable def diagonalSimilitude (u : Kˣ) : symplecticSimilitudes K :=
  ⟨TauCeti.diagGL (fun i : Fin 4 => if i = 0 then u else if i = 1 then u else 1),
    u, by
    rw [TauCeti.diagGL_coe]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [symplecticGram, Matrix.diagonal, Matrix.mul_apply, Fin.sum_univ_four] <;>
      ring⟩

private theorem diagonalSimilitude_val (u : Kˣ) :
    Units.val ((diagonalSimilitude u : ↥(symplecticSimilitudes K)) : GL (Fin 4) K) =
      (TauCeti.diagGL (fun i : Fin 4 => if i = 0 then u else if i = 1 then u else 1) :
        Matrix (Fin 4) (Fin 4) K) := rfl

private theorem diagonalSimilitude_spec (u : Kˣ) :
    (Units.val ((diagonalSimilitude u : ↥(symplecticSimilitudes K)) : GL (Fin 4) K))ᵀ *
      symplecticGram K *
      (Units.val ((diagonalSimilitude u : ↥(symplecticSimilitudes K)) : GL (Fin 4) K)) =
      (u : K) • symplecticGram K := by
  rw [diagonalSimilitude_val u, TauCeti.diagGL_coe]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [symplecticGram, Matrix.diagonal, Matrix.mul_apply, Fin.sum_univ_four] <;> ring

theorem symplecticMultiplier_diagonalSimilitude (u : Kˣ) :
    symplecticMultiplier (diagonalSimilitude u) = u := by
  apply symplectic_multiplier_unique _ _ u (symplecticMultiplier_spec _)
  exact diagonalSimilitude_spec u

private theorem diagonalSimilitude_inv_val (u : Kˣ) :
    Units.val (((diagonalSimilitude u : ↥(symplecticSimilitudes K)) : GL (Fin 4) K)⁻¹) =
      (TauCeti.diagGL (fun i : Fin 4 => if i = 0 then u⁻¹ else if i = 1 then u⁻¹ else 1) :
        Matrix (Fin 4) (Fin 4) K) := by
  rw [show ((diagonalSimilitude u : ↥(symplecticSimilitudes K)) : GL (Fin 4) K) =
      TauCeti.diagGL (fun i : Fin 4 => if i = 0 then u else if i = 1 then u else 1) from rfl,
    ← map_inv, TauCeti.diagGL_coe, TauCeti.diagGL_coe]
  congr 1
  ext i
  fin_cases i <;> simp

private theorem selfAdjointConjugation_diagonalSimilitude_coordinates
    (h2 : (2 : K) ≠ 0) (u : Kˣ) (x : Fin 5 → K) :
    (selfAdjointCoordinates h2).symm
        (selfAdjointConjugation (diagonalSimilitude u) (selfAdjointCoordinates h2 x)) =
      ![x 0, x 1, x 2, (u : K) * x 3, ((u⁻¹ : Kˣ) : K) * x 4] := by
  apply (selfAdjointCoordinates h2).injective
  rw [LinearEquiv.apply_symm_apply]
  apply Subtype.ext
  rw [selfAdjointConjugation_val]
  change Units.val ((diagonalSimilitude u : ↥(symplecticSimilitudes K)) : GL (Fin 4) K) *
      ((selfAdjointCoordinates h2) x).val *
      Units.val (((diagonalSimilitude u : ↥(symplecticSimilitudes K)) : GL (Fin 4) K)⁻¹) =
    ((selfAdjointCoordinates h2) ![x 0, x 1, x 2, (u : K) * x 3,
      ((u⁻¹ : Kˣ) : K) * x 4]).val
  rw [diagonalSimilitude_val u, diagonalSimilitude_inv_val u,
    TauCeti.diagGL_coe, TauCeti.diagGL_coe]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.diagonal, Matrix.mul_apply, Fin.sum_univ_four,
      selfAdjointCoordinates_val] <;>
    field_simp

private theorem selfAdjointOrthogonalAction_diagonalSimilitude_det
    (h2 : (2 : K) ≠ 0) (u : Kˣ) :
    LinearEquiv.det ((selfAdjointOrthogonalAction h2 (diagonalSimilitude u)).val) = 1 := by
  let e := selfAdjointCoordinates h2
  let F : selfAdjointSubmodule K ≃ₗ[K] selfAdjointSubmodule K :=
    (selfAdjointOrthogonalAction h2 (diagonalSimilitude u)).val
  let T : (Fin 5 → K) ≃ₗ[K] (Fin 5 → K) := (e.trans F).trans e.symm
  have hTdet : LinearEquiv.det T = LinearEquiv.det F := by
    change LinearEquiv.det ((e.trans F).trans e.symm) = LinearEquiv.det F
    exact LinearEquiv.det_conj F e.symm
  have hmat : LinearMap.toMatrix' (T : (Fin 5 → K) →ₗ[K] (Fin 5 → K)) =
      Matrix.diagonal (fun k : Fin 5 =>
        if k = 0 then (1 : K) else if k = 1 then 1 else if k = 2 then 1
          else if k = 3 then (u : K) else ((u⁻¹ : Kˣ) : K)) := by
    ext i j
    rw [LinearMap.toMatrix'_apply]
    have hFval (X : selfAdjointSubmodule K) :
        (↑(selfAdjointOrthogonalAction h2 (diagonalSimilitude u)) :
          selfAdjointSubmodule K ≃ₗ[K] selfAdjointSubmodule K) X =
          selfAdjointConjugation (diagonalSimilitude u) X := rfl
    have hcoord := selfAdjointConjugation_diagonalSimilitude_coordinates h2 u (Pi.single j 1)
    change T (Pi.single j 1) i = _
    dsimp [T, e, F]
    rw [hFval, hcoord]
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.diagonal]
  have hT : LinearEquiv.det T = 1 := by
    apply Units.ext
    rw [LinearEquiv.coe_det, ← LinearMap.det_toMatrix' (T : (Fin 5 → K) →ₗ[K] (Fin 5 → K)),
      hmat, Matrix.det_diagonal, Fin.prod_univ_five]
    norm_num
  rw [← hTdet]
  exact hT


private theorem orthogonalDet_negOrthogonal (h2 : (2 : K) ≠ 0) :
    QuadraticMap.orthogonalDet (selfAdjointForm K)
      (QuadraticMap.negOrthogonal (selfAdjointForm K)) = -1 := by
  rw [QuadraticMap.orthogonalDet_apply, QuadraticMap.coe_negOrthogonal]
  apply Units.ext
  rw [LinearEquiv.coe_det]
  change LinearMap.det (-(LinearMap.id : selfAdjointSubmodule K →ₗ[K] selfAdjointSubmodule K)) =
    (-1 : K)
  rw [show (-(LinearMap.id : selfAdjointSubmodule K →ₗ[K] selfAdjointSubmodule K)) =
    (-1 : K) • LinearMap.id by ext x; simp]
  rw [LinearMap.det_smul, LinearMap.det_id, selfAdjoint_finrank h2, mul_one]
  norm_num

private theorem selfAdjointOrthogonalAction_orthogonalDet_eq_one [Finite K]
    (hodd : Odd (Nat.card K)) (A : symplecticSimilitudes K) :
    QuadraticMap.orthogonalDet (selfAdjointForm K)
      (selfAdjointOrthogonalAction (CatalogueBOddQuadratic.two_ne_zero_of_odd_card hodd) A) = 1 := by
  let h2 := CatalogueBOddQuadratic.two_ne_zero_of_odd_card hodd
  let B : (symplecticMultiplier (K := K)).ker :=
    ⟨(diagonalSimilitude (symplecticMultiplier A))⁻¹ * A, by
      rw [MonoidHom.mem_ker, map_mul, map_inv, symplecticMultiplier_diagonalSimilitude,
        inv_mul_cancel]⟩
  have hAeq : A = diagonalSimilitude (symplecticMultiplier A) * B.val := by
    change A = diagonalSimilitude (symplecticMultiplier A) *
      ((diagonalSimilitude (symplecticMultiplier A))⁻¹ * A)
    group
  have hD : QuadraticMap.orthogonalDet (selfAdjointForm K)
      (selfAdjointOrthogonalAction h2 (diagonalSimilitude (symplecticMultiplier A))) = 1 := by
    rw [QuadraticMap.orthogonalDet_apply]
    exact selfAdjointOrthogonalAction_diagonalSimilitude_det h2 _
  have hB : QuadraticMap.orthogonalDet (selfAdjointForm K)
      (selfAdjointOrthogonalAction h2 B) = 1 := by
    haveI : Group.IsPerfect ↥(symplecticMultiplier (K := K)).ker :=
      (symplecticKernel_quasisimple hodd).1
    let f : ↥(symplecticMultiplier (K := K)).ker →* Kˣ :=
      (QuadraticMap.orthogonalDet (selfAdjointForm K)).comp (selfAdjointSymplecticAction h2)
    haveI : Group.IsPerfect f.range := Group.IsPerfect.range f
    haveI : IsMulCommutative f.range := inferInstance
    haveI : Subsingleton f.range := Group.IsPerfect.subsingleton_of_isMulCommutative
    have h1 : f B = 1 := by
      have hmem : f B ∈ f.range := ⟨B, rfl⟩
      have hsub : (⟨f B, hmem⟩ : f.range) = 1 := Subsingleton.elim _ _
      exact congrArg Subtype.val hsub
    simpa [f, selfAdjointSymplecticAction, MonoidHom.comp_apply] using h1
  rw [hAeq, map_mul, map_mul, hD, hB, one_mul]

theorem selfAdjointOrthogonalAction_det_eq_one [Finite K]
    (hodd : Odd (Nat.card K)) (A : symplecticSimilitudes K) :
    LinearEquiv.det
      ((selfAdjointOrthogonalAction (CatalogueBOddQuadratic.two_ne_zero_of_odd_card hodd) A).val) = 1 := by
  rw [← QuadraticMap.orthogonalDet_apply]
  exact selfAdjointOrthogonalAction_orthogonalDet_eq_one hodd A

theorem selfAdjointOrthogonalAction_range [Finite K] (hodd : Odd (Nat.card K)) :
    (selfAdjointOrthogonalAction (CatalogueBOddQuadratic.two_ne_zero_of_odd_card hodd)).range =
      QuadraticMap.specialOrthogonalWithin (selfAdjointForm K) := by
  let h2 := CatalogueBOddQuadratic.two_ne_zero_of_odd_card hodd
  apply le_antisymm
  · rintro _ ⟨A, rfl⟩
    rw [QuadraticMap.mem_specialOrthogonalWithin_iff]
    exact selfAdjointOrthogonalAction_det_eq_one hodd A
  · intro g hg
    rw [QuadraticMap.mem_specialOrthogonalWithin_iff] at hg
    obtain ⟨A, hA | hA⟩ := selfAdjoint_isometry_exhaustion h2 g
    · exact ⟨A, hA.symm⟩
    · exfalso
      have hdetg : QuadraticMap.orthogonalDet (selfAdjointForm K) g = 1 := by
        rw [QuadraticMap.orthogonalDet_apply]
        exact hg
      have hneg : QuadraticMap.orthogonalDet (selfAdjointForm K)
          (QuadraticMap.negOrthogonal (selfAdjointForm K)) = -1 :=
        orthogonalDet_negOrthogonal h2
      have hdetA : QuadraticMap.orthogonalDet (selfAdjointForm K)
          (selfAdjointOrthogonalAction h2 A) = 1 :=
        selfAdjointOrthogonalAction_orthogonalDet_eq_one hodd A
      rw [hA, map_mul, hneg, hdetA] at hdetg
      have hneg1 : (-1 : Kˣ) = 1 := by simpa using hdetg
      have hfield : (-1 : K) = 1 := congrArg (fun u : Kˣ => (u : K)) hneg1
      have h2' : (2 : K) = 0 := by linear_combination -hfield
      exact h2 h2'

private theorem selfAdjointOrthogonalAction_mem_symplecticImage_iff_isSquare
    (h2 : (2 : K) ≠ 0) (A : symplecticSimilitudes K) :
    selfAdjointOrthogonalAction h2 A ∈ selfAdjointSymplecticImage h2 ↔
      IsSquare (symplecticMultiplier A : K) := by
  constructor
  · rintro ⟨B, hB⟩
    have hB' : selfAdjointOrthogonalAction h2 B.val = selfAdjointOrthogonalAction h2 A := by
      simpa [selfAdjointSymplecticAction] using hB
    have h1 : selfAdjointOrthogonalAction h2 (A * B.val⁻¹) = 1 := by
      rw [map_mul, map_inv, hB']
      group
    obtain ⟨c, hc⟩ := (selfAdjointOrthogonalAction_eq_one_iff h2 (A * B.val⁻¹)).mp h1
    have heq : A * B.val⁻¹ = selfAdjointScalarSimilitude c := Subtype.ext hc
    have hBker : symplecticMultiplier B.val = 1 := MonoidHom.mem_ker.mp B.property
    have hcalc : symplecticMultiplier (A * B.val⁻¹) = symplecticMultiplier A := by
      rw [map_mul, map_inv, hBker, inv_one, mul_one]
    have hmul : symplecticMultiplier A = c ^ 2 := by
      rw [← hcalc, heq, symplecticMultiplier_scalar]
    refine ⟨(c : K), ?_⟩
    have hval := congrArg (fun u : Kˣ => (u : K)) hmul
    rw [Units.val_pow_eq_pow_val, pow_two] at hval
    exact hval
  · rintro ⟨r, hr⟩
    classical
    have hr0 : r ≠ 0 := by
      rintro rfl
      have hzero : (symplecticMultiplier A : K) = 0 := by simpa using hr
      exact Units.ne_zero (symplecticMultiplier A) hzero
    let c : Kˣ := Units.mk0 r hr0
    have hc : symplecticMultiplier A = c ^ 2 := by
      apply Units.ext
      rw [Units.val_pow_eq_pow_val, pow_two]
      exact hr
    let B : (symplecticMultiplier (K := K)).ker :=
      ⟨A * (selfAdjointScalarSimilitude c)⁻¹, by
        rw [MonoidHom.mem_ker, map_mul, map_inv, symplecticMultiplier_scalar, hc,
          mul_inv_cancel]⟩
    refine ⟨B, ?_⟩
    change selfAdjointOrthogonalAction h2 B.val = selfAdjointOrthogonalAction h2 A
    rw [show B.val = A * (selfAdjointScalarSimilitude c)⁻¹ from rfl,
      map_mul, map_inv, selfAdjointOrthogonalAction_scalar, inv_one, mul_one]

theorem selfAdjointSymplecticImage_relIndex_specialOrthogonalWithin [Finite K]
    (hodd : Odd (Nat.card K)) :
    (selfAdjointSymplecticImage (CatalogueBOddQuadratic.two_ne_zero_of_odd_card hodd)).relIndex
      (QuadraticMap.specialOrthogonalWithin (selfAdjointForm K)) = 2 := by
  let h2 := CatalogueBOddQuadratic.two_ne_zero_of_odd_card hodd
  change ((selfAdjointSymplecticImage h2).subgroupOf
    (QuadraticMap.specialOrthogonalWithin (selfAdjointForm K))).index = 2
  rw [Subgroup.index_eq_two_iff_exists_notMem_and]
  classical
  have hchar : ringChar K ≠ 2 := CatalogueBOddQuadratic.char_ne_two_of_odd_card hodd
  obtain ⟨x, hx⟩ := FiniteField.exists_nonsquare hchar
  have hx0 : x ≠ 0 := fun h => hx (h ▸ IsSquare.zero)
  let u₀ : Kˣ := Units.mk0 x hx0
  have hu₀ : ¬ IsSquare (u₀ : K) := by
    intro hsq
    obtain ⟨r, hr⟩ := hsq
    exact hx ⟨r, by simpa [u₀] using hr⟩
  let a : QuadraticMap.specialOrthogonalWithin (selfAdjointForm K) :=
    ⟨selfAdjointOrthogonalAction h2 (diagonalSimilitude u₀), by
      rw [← selfAdjointOrthogonalAction_range hodd]
      exact ⟨diagonalSimilitude u₀, rfl⟩⟩
  refine ⟨a, ?_, ?_⟩
  · rw [Subgroup.mem_subgroupOf]
    intro haP
    have hsq := (selfAdjointOrthogonalAction_mem_symplecticImage_iff_isSquare h2
      (diagonalSimilitude u₀)).mp haP
    rw [symplecticMultiplier_diagonalSimilitude] at hsq
    exact hu₀ hsq
  · intro b
    have hbRange : (b : TauCeti.QuadraticMap.orthogonalGroup (selfAdjointForm K)) ∈
        (selfAdjointOrthogonalAction h2).range :=
      (selfAdjointOrthogonalAction_range hodd).symm ▸ b.property
    obtain ⟨A, hA⟩ := hbRange
    by_cases hsqA : IsSquare (symplecticMultiplier A : K)
    · right
      rw [Subgroup.mem_subgroupOf]
      rw [← hA]
      exact (selfAdjointOrthogonalAction_mem_symplecticImage_iff_isSquare h2 A).mpr hsqA
    · left
      rw [Subgroup.mem_subgroupOf]
      rw [Subgroup.coe_mul]
      change (b : TauCeti.QuadraticMap.orthogonalGroup (selfAdjointForm K)) *
        selfAdjointOrthogonalAction h2 (diagonalSimilitude u₀) ∈
          selfAdjointSymplecticImage h2
      rw [← hA]
      have hprod : IsSquare ((symplecticMultiplier A : K) * (u₀ : K)) := by
        letI : Fintype K := Fintype.ofFinite K
        rw [← quadraticChar_one_iff_isSquare
          (mul_ne_zero (Units.ne_zero (symplecticMultiplier A)) (Units.ne_zero u₀))]
        rw [map_mul, quadraticChar_neg_one_iff_not_isSquare.mpr hsqA,
          quadraticChar_neg_one_iff_not_isSquare.mpr hu₀]
        norm_num
      have hsq : IsSquare (symplecticMultiplier (A * diagonalSimilitude u₀) : K) := by
        rw [map_mul, symplecticMultiplier_diagonalSimilitude]
        simpa [Units.val_mul] using hprod
      rw [← map_mul]
      exact (selfAdjointOrthogonalAction_mem_symplecticImage_iff_isSquare h2
        (A * diagonalSimilitude u₀)).mpr hsq

theorem commutator_relIndex_specialOrthogonalWithin [Finite K]
    (hodd : Odd (Nat.card K)) :
    (commutator (TauCeti.QuadraticMap.orthogonalGroup (selfAdjointForm K))).relIndex
      (QuadraticMap.specialOrthogonalWithin (selfAdjointForm K)) = 2 := by
  rw [← selfAdjointSymplecticImage_eq_commutator hodd]
  exact selfAdjointSymplecticImage_relIndex_specialOrthogonalWithin hodd

end CFSG.ClassicalGroups.Symplectic
