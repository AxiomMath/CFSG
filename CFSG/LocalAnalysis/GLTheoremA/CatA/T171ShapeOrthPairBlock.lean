module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeOrthModelPaired
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeExcU2Ind
public import CFSG.Quasithin.Vol2.Ch12Sec6P31LieH
import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeSpModelPairedMain

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T171Sh

open Polynomial Module
open CFSG.Open CFSG.Assembly CFSG.Yardstones.Md0ec50421ce4
open CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KCOrthogonal CFSG.RankThree.Classical2
open CFSG.RankThree.PartOne.KCPrimary CFSG.ClassicalGroups.Orthogonal
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open CFSG.ComponentClassification.AssemblyBPredicates

variable {K V : Type} [Field K] [Finite K] [CharP K 2] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V} {p : ℕ} {x : ↥(orthDerived Q)}
  {h : K[X]} [Fact (Irreducible h)]

@[expose] noncomputable def orthPairedBasis :
    Module.Basis (Fin (primaryMultiplicity (x : V ≃ₗ[K] V).toLinearMap h))
      (AdjoinRoot h) (primaryComponent (x : V ≃ₗ[K] V).toLinearMap h) :=
  Module.finBasisOfFinrankEq _ _ rfl

@[expose] noncomputable def orthPairedStatedSL (hx : OddOrderIsometry Q p (x : V ≃ₗ[K] V))
    (hh : h ∈ primaryFactors (x : V ≃ₗ[K] V).toLinearMap)
    (hne : h ≠ reciprocalPolynomial h) :
    ↥(specialBlock Q (x : V ≃ₗ[K] V) h) ≃*
      StatedSL (primaryMultiplicity (x : V ≃ₗ[K] V).toLinearMap h) (AdjoinRoot h) :=
  (MulEquiv.ofBijective (specialToSL Q (x : V ≃ₗ[K] V) h)
    ⟨hx.specialToSL_injective hh, hx.specialToSL_surjective_paired hh hne⟩).trans
    ((Matrix.SpecialLinearGroup.toLin_equiv orthPairedBasis).symm.trans
      (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL _ _))

@[expose] noncomputable def orthPairedGL
    (d : ↥(specialBlock Q (x : V ≃ₗ[K] V) h)) :
    LinearMap.GeneralLinearGroup (AdjoinRoot h)
      (primaryComponent (x : V ≃ₗ[K] V).toLinearMap h) :=
  LinearMap.GeneralLinearGroup.ofLinearEquiv
    (specialToSL Q (x : V ≃ₗ[K] V) h d).toLinearEquiv

theorem orthPairedStatedSL_toLin (hx : OddOrderIsometry Q p (x : V ≃ₗ[K] V))
    (hh : h ∈ primaryFactors (x : V ≃ₗ[K] V).toLinearMap)
    (hne : h ≠ reciprocalPolynomial h)
    (d : ↥(specialBlock Q (x : V ≃ₗ[K] V) h)) :
    Matrix.GeneralLinearGroup.toLin' orthPairedBasis
      ((orthPairedStatedSL hx hh hne d : StatedSL _ _) : GL _ _) =
      orthPairedGL d := by
  rw [← (LinearMap.GeneralLinearGroup.generalLinearEquiv (AdjoinRoot h)
    (primaryComponent (x : V ≃ₗ[K] V).toLinearMap h)).injective.eq_iff]
  change (Matrix.SpecialLinearGroup.toLin_equiv orthPairedBasis
      ((Matrix.SpecialLinearGroup.toLin_equiv orthPairedBasis).symm
        (specialToSL Q (x : V ≃ₗ[K] V) h d))).toLinearEquiv =
    (specialToSL Q (x : V ≃ₗ[K] V) h d).toLinearEquiv
  rw [MulEquiv.apply_symm_apply]

theorem orthPairedGL_conj
    {y : V ≃ₗ[K] V}
    (hycen : y ∈ Subgroup.centralizer ({(x : V ≃ₗ[K] V)} : Set (V ≃ₗ[K] V)))
    {d : ↥(specialBlock Q (x : V ≃ₗ[K] V) h)}
    (hd : y⁻¹ * d.1 * y ∈ specialBlock Q (x : V ≃ₗ[K] V) h) :
    orthPairedGL ⟨y⁻¹ * d.1 * y, hd⟩ =
      (centralizerGL (x : V ≃ₗ[K] V) h ⟨y, hycen⟩)⁻¹ *
        orthPairedGL d *
        (centralizerGL (x : V ≃ₗ[K] V) h ⟨y, hycen⟩) := by
  apply (LinearMap.GeneralLinearGroup.generalLinearEquiv (AdjoinRoot h)
    (primaryComponent (x : V ≃ₗ[K] V).toLinearMap h)).injective
  change (LinearMap.GeneralLinearGroup.generalLinearEquiv (AdjoinRoot h)
      (primaryComponent (x : V ≃ₗ[K] V).toLinearMap h))
      (LinearMap.GeneralLinearGroup.ofLinearEquiv
        (specialToSL Q (x : V ≃ₗ[K] V) h ⟨y⁻¹ * d.1 * y, hd⟩).toLinearEquiv) =
    (LinearMap.GeneralLinearGroup.generalLinearEquiv (AdjoinRoot h)
        (primaryComponent (x : V ≃ₗ[K] V).toLinearMap h))
      ((centralizerGL (x : V ≃ₗ[K] V) h ⟨y, hycen⟩)⁻¹ *
        LinearMap.GeneralLinearGroup.ofLinearEquiv
          (specialToSL Q (x : V ≃ₗ[K] V) h d).toLinearEquiv *
        (centralizerGL (x : V ≃ₗ[K] V) h ⟨y, hycen⟩))
  simp only [MulEquiv.map_mul, MulEquiv.map_inv]
  have hgen : ∀ e : primaryComponent (x : V ≃ₗ[K] V).toLinearMap h ≃ₗ[AdjoinRoot h]
      primaryComponent (x : V ≃ₗ[K] V).toLinearMap h,
      (LinearMap.GeneralLinearGroup.generalLinearEquiv (AdjoinRoot h)
        (primaryComponent (x : V ≃ₗ[K] V).toLinearMap h))
        (LinearMap.GeneralLinearGroup.ofLinearEquiv e) = e := fun e => rfl
  rw [hgen, hgen]
  ext v
  have hcen : (LinearMap.GeneralLinearGroup.generalLinearEquiv (AdjoinRoot h)
        (primaryComponent (x : V ≃ₗ[K] V).toLinearMap h))
      (centralizerGL (x : V ≃ₗ[K] V) h ⟨y, hycen⟩) =
      (centralizerGL (x : V ≃ₗ[K] V) h ⟨y, hycen⟩).toLinearEquiv := rfl
  rw [hcen]
  change ((y⁻¹ * d.1 * y : V ≃ₗ[K] V) (v : V)) = y⁻¹ (d.1 (y (v : V)))
  rfl

@[expose] noncomputable def orthPairedMatrix
    {y : V ≃ₗ[K] V}
    (hycen : y ∈
      Subgroup.centralizer ({(x : V ≃ₗ[K] V)} : Set (V ≃ₗ[K] V))) :
    GL (Fin (primaryMultiplicity (x : V ≃ₗ[K] V).toLinearMap h)) (AdjoinRoot h) :=
  (Matrix.GeneralLinearGroup.toLin' orthPairedBasis).symm
    (centralizerGL (x : V ≃ₗ[K] V) h ⟨(y : V ≃ₗ[K] V), hycen⟩)

theorem orthPairedStatedSL_conj (hx : OddOrderIsometry Q p (x : V ≃ₗ[K] V))
    (hh : h ∈ primaryFactors (x : V ≃ₗ[K] V).toLinearMap)
    (hne : h ≠ reciprocalPolynomial h)
    {y : ↥(orthDerived Q)}
    (hycen : (y : V ≃ₗ[K] V) ∈
      Subgroup.centralizer ({(x : V ≃ₗ[K] V)} : Set (V ≃ₗ[K] V)))
    {d : ↥(specialBlock Q (x : V ≃ₗ[K] V) h)}
    (hd : (y : V ≃ₗ[K] V)⁻¹ * d.1 * (y : V ≃ₗ[K] V) ∈
      specialBlock Q (x : V ≃ₗ[K] V) h) :
    ((orthPairedStatedSL hx hh hne ⟨(y : V ≃ₗ[K] V)⁻¹ * d.1 * (y : V ≃ₗ[K] V), hd⟩ :
        StatedSL (primaryMultiplicity (x : V ≃ₗ[K] V).toLinearMap h) (AdjoinRoot h)) :
        GL (Fin (primaryMultiplicity (x : V ≃ₗ[K] V).toLinearMap h)) (AdjoinRoot h)) =
      (orthPairedMatrix hycen)⁻¹ *
        ((orthPairedStatedSL hx hh hne d :
          StatedSL (primaryMultiplicity (x : V ≃ₗ[K] V).toLinearMap h) (AdjoinRoot h)) :
          GL (Fin (primaryMultiplicity (x : V ≃ₗ[K] V).toLinearMap h)) (AdjoinRoot h)) *
        orthPairedMatrix hycen := by
  apply (Matrix.GeneralLinearGroup.toLin' orthPairedBasis).injective
  rw [map_mul, map_mul, map_inv, orthPairedStatedSL_toLin, orthPairedStatedSL_toLin]
  simp only [orthPairedMatrix, MulEquiv.apply_symm_apply]
  rw [orthPairedGL_conj hycen hd]

theorem orthPairedMatrix_pow
    {y : V ≃ₗ[K] V}
    (hycen : y ∈ Subgroup.centralizer ({(x : V ≃ₗ[K] V)} : Set (V ≃ₗ[K] V)))
    (hyp : y ^ p = 1) :
    orthPairedMatrix (x := x) (h := h) (y := y) hycen ^ p = 1 := by
  have hsub : (⟨y, hycen⟩ :
      ↥(Subgroup.centralizer ({(x : V ≃ₗ[K] V)} : Set (V ≃ₗ[K] V)))) ^ p = 1 := by
    apply Subtype.ext
    exact hyp
  have hmap := congrArg (centralizerGL (x : V ≃ₗ[K] V) h) hsub
  rw [map_pow, map_one] at hmap
  dsimp only [orthPairedMatrix]
  rw [← map_pow, hmap, map_one]

@[expose] noncomputable def orthPairedComponentEquiv
    (hpi : Function.Injective (piOrth Q))
    (hspecΩ : specialBlock Q (x : V ≃ₗ[K] V) h ≤ orthDerived Q)
    (J : Subgroup (ProjOrthDerived Q))
    (hJeq : J = componentImage Q (x : V ≃ₗ[K] V) h) :
    ↥(specialBlock Q (x : V ≃ₗ[K] V) h) ≃* ↥J :=
  ((Subgroup.subgroupOfEquivOfLe hspecΩ).symm.trans
    (Subgroup.equivMapOfInjective
      (H := (specialBlock Q (x : V ≃ₗ[K] V) h).subgroupOf (orthDerived Q))
      (f := piOrth Q) hpi)).trans (MulEquiv.subgroupCongr hJeq.symm)

theorem orthPairedComponentEquiv_apply
    (hpi : Function.Injective (piOrth Q))
    (hspecΩ : specialBlock Q (x : V ≃ₗ[K] V) h ≤ orthDerived Q)
    (J : Subgroup (ProjOrthDerived Q))
    (hJeq : J = componentImage Q (x : V ≃ₗ[K] V) h)
    (d : ↥(specialBlock Q (x : V ≃ₗ[K] V) h)) :
    (orthPairedComponentEquiv hpi hspecΩ J hJeq d : ProjOrthDerived Q) =
      piOrth Q ⟨d.1, hspecΩ d.2⟩ :=
  rfl

theorem indAut_orthPairedComponentEquiv
    (hpi : Function.Injective (piOrth Q))
    (hspecΩ : specialBlock Q (x : V ≃ₗ[K] V) h ≤ orthDerived Q)
    (J : Subgroup (ProjOrthDerived Q))
    (hJeq : J = componentImage Q (x : V ≃ₗ[K] V) h)
    (y : ↥(orthDerived Q))
    (hN : piOrth Q y ∈ Subgroup.normalizer (J : Set (ProjOrthDerived Q)))
    (d : ↥(specialBlock Q (x : V ≃ₗ[K] V) h))
    (hd : (y : V ≃ₗ[K] V)⁻¹ * d.1 * (y : V ≃ₗ[K] V) ∈
      specialBlock Q (x : V ≃ₗ[K] V) h) :
    MI.indAut p J (piOrth Q y) hN
        (chevQuotHom p J (orthPairedComponentEquiv hpi hspecΩ J hJeq d)) =
      chevQuotHom p J (orthPairedComponentEquiv hpi hspecΩ J hJeq
        ⟨(y : V ≃ₗ[K] V)⁻¹ * d.1 * (y : V ≃ₗ[K] V), hd⟩) := by
  rw [show MI.indAut p J (piOrth Q y) hN =
      chevAut p J ⟨(piOrth Q y)⁻¹, Subgroup.inv_mem _ hN⟩ from rfl]
  rw [CFSG.LocalAnalysis.GLTheoremA.chevAut_chevQuotHom]
  suffices h : (J.normalizerMonoidHom ⟨((piOrth Q) y)⁻¹, Subgroup.inv_mem _ hN⟩)
        (orthPairedComponentEquiv hpi hspecΩ J hJeq d) =
      orthPairedComponentEquiv hpi hspecΩ J hJeq
        ⟨(y : V ≃ₗ[K] V)⁻¹ * d.1 * (y : V ≃ₗ[K] V), hd⟩ by
    rw [h]
  apply Subtype.ext
  rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
  rw [orthPairedComponentEquiv_apply, orthPairedComponentEquiv_apply]
  simp only [Subtype.coe_mk]
  rw [← map_inv, ← map_inv, ← map_mul, ← map_mul]
  rfl

theorem exists_orthPaired_pSimpleEquiv
    (J : Subgroup (ProjOrthDerived Q))
    (eJ : ↥(specialBlock Q (x : V ≃ₗ[K] V) h) ≃* ↥J) :
    ∃ eJp : PSimple p (specialBlock Q (x : V ≃ₗ[K] V) h) ≃* PSimple p J,
      ∀ d : ↥(specialBlock Q (x : V ≃ₗ[K] V) h),
        eJp (chevQuotHom p (specialBlock Q (x : V ≃ₗ[K] V) h) d) =
          chevQuotHom p J (eJ d) := by
  let ψ : PQuot p (specialBlock Q (x : V ≃ₗ[K] V) h) ≃* PQuot p J :=
    CFSG.HardMathSupport.Dickson.I271.pQuotEquiv p eJ
  let eJp : PSimple p (specialBlock Q (x : V ≃ₗ[K] V) h) ≃* PSimple p J :=
    QuotientGroup.congr (Subgroup.center (PQuot p (specialBlock Q (x : V ≃ₗ[K] V) h)))
      (Subgroup.center (PQuot p J)) ψ (Subgroup.map_center_eq ψ)
  refine ⟨eJp, ?_⟩
  intro d
  dsimp only [eJp]
  rw [show chevQuotHom p (specialBlock Q (x : V ≃ₗ[K] V) h) d =
      QuotientGroup.mk' (Subgroup.center (PQuot p (specialBlock Q (x : V ≃ₗ[K] V) h)))
        (pQuotHom p (specialBlock Q (x : V ≃ₗ[K] V) h) d) from rfl]
  rw [QuotientGroup.congr_mk']
  dsimp only [ψ]
  rw [show pQuotHom p (specialBlock Q (x : V ≃ₗ[K] V) h) d = QuotientGroup.mk d from rfl]
  rw [CFSG.HardMathSupport.Dickson.I271.pQuotEquiv_mk]
  rfl

theorem exists_orthPaired_centerQuot
    (hp : p.Prime) (hq : CFSG.IsQuasisimple ↥(specialBlock Q (x : V ≃ₗ[K] V) h))
    (hd : p ∣ Nat.card ↥(specialBlock Q (x : V ≃ₗ[K] V) h)) :
    ∃ eP : (↥(specialBlock Q (x : V ≃ₗ[K] V) h) ⧸
        Subgroup.center ↥(specialBlock Q (x : V ≃ₗ[K] V) h)) ≃*
        PSimple p (specialBlock Q (x : V ≃ₗ[K] V) h),
      ∀ l : ↥(specialBlock Q (x : V ≃ₗ[K] V) h),
        eP (QuotientGroup.mk l) = QuotientGroup.mk (QuotientGroup.mk l) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hq' : CFSG.Open.IsQuasisimple ↥(specialBlock Q (x : V ≃ₗ[K] V) h) :=
    (isQuasisimple_iff_open _).mp ((isQuasisimple_iff_native _).mpr hq)
  exact exists_pSimpleEquivCenterQuot_mk hp hq' hd

theorem exists_orthPaired_pairedEquiv
    (J : Subgroup (ProjOrthDerived Q))
    (eJ : ↥(specialBlock Q (x : V ≃ₗ[K] V) h) ≃* ↥J)
    (eSL : ↥(specialBlock Q (x : V ≃ₗ[K] V) h) ≃*
      StatedSL (primaryMultiplicity (x : V ≃ₗ[K] V).toLinearMap h) (AdjoinRoot h))
    (eJp : PSimple p (specialBlock Q (x : V ≃ₗ[K] V) h) ≃* PSimple p J)
    (heJp : ∀ d : ↥(specialBlock Q (x : V ≃ₗ[K] V) h),
      eJp (chevQuotHom p (specialBlock Q (x : V ≃ₗ[K] V) h) d) = chevQuotHom p J (eJ d))
    (eP : (↥(specialBlock Q (x : V ≃ₗ[K] V) h) ⧸
        Subgroup.center ↥(specialBlock Q (x : V ≃ₗ[K] V) h)) ≃*
        PSimple p (specialBlock Q (x : V ≃ₗ[K] V) h))
    (heP : ∀ l : ↥(specialBlock Q (x : V ≃ₗ[K] V) h),
      eP (QuotientGroup.mk l) = QuotientGroup.mk (QuotientGroup.mk l)) :
    ∃ e : PSimple p J ≃* LargeEvenProj (StatedSL
        (primaryMultiplicity (x : V ≃ₗ[K] V).toLinearMap h) (AdjoinRoot h)),
      ∀ d : ↥(specialBlock Q (x : V ≃ₗ[K] V) h),
        e (chevQuotHom p J (eJ d)) = LargeEvenProjMk
          (StatedSL (primaryMultiplicity (x : V ≃ₗ[K] V).toLinearMap h) (AdjoinRoot h))
          (eSL d) := by
  let e2 : (↥(specialBlock Q (x : V ≃ₗ[K] V) h) ⧸
      Subgroup.center ↥(specialBlock Q (x : V ≃ₗ[K] V) h)) ≃*
      (↥(StatedSL (primaryMultiplicity (x : V ≃ₗ[K] V).toLinearMap h) (AdjoinRoot h)) ⧸
        Subgroup.center ↥(StatedSL (primaryMultiplicity (x : V ≃ₗ[K] V).toLinearMap h)
          (AdjoinRoot h))) :=
    QuotientGroup.congr (Subgroup.center ↥(specialBlock Q (x : V ≃ₗ[K] V) h))
      (Subgroup.center ↥(StatedSL (primaryMultiplicity (x : V ≃ₗ[K] V).toLinearMap h)
        (AdjoinRoot h))) eSL (Subgroup.map_center_eq eSL)
  let e3 : (↥(StatedSL (primaryMultiplicity (x : V ≃ₗ[K] V).toLinearMap h) (AdjoinRoot h)) ⧸
      Subgroup.center ↥(StatedSL (primaryMultiplicity (x : V ≃ₗ[K] V).toLinearMap h)
        (AdjoinRoot h))) ≃*
      LargeEvenProj (StatedSL (primaryMultiplicity (x : V ≃ₗ[K] V).toLinearMap h)
        (AdjoinRoot h)) :=
    QuotientGroup.quotientMulEquivOfEq
      (CFSG.Quasithin.H13.S126P31.center_statedSL_eq
        (primaryMultiplicity (x : V ≃ₗ[K] V).toLinearMap h) (AdjoinRoot h))
  let e : PSimple p J ≃* LargeEvenProj (StatedSL
      (primaryMultiplicity (x : V ≃ₗ[K] V).toLinearMap h) (AdjoinRoot h)) :=
    eJp.symm.trans (eP.symm.trans (e2.trans e3))
  refine ⟨e, ?_⟩
  intro d
  have h1 : eJp.symm (chevQuotHom p J (eJ d)) =
      chevQuotHom p (specialBlock Q (x : V ≃ₗ[K] V) h) d :=
    eJp.symm_apply_eq.mpr (heJp d).symm
  have h2 : eP.symm (chevQuotHom p (specialBlock Q (x : V ≃ₗ[K] V) h) d) =
      QuotientGroup.mk d := by
    apply eP.injective
    rw [MulEquiv.apply_symm_apply]
    exact (heP d).symm
  have h3 : e2 (QuotientGroup.mk d) = QuotientGroup.mk (eSL d) := rfl
  have h4 : e3 (QuotientGroup.mk (eSL d)) = LargeEvenProjMk
      (StatedSL (primaryMultiplicity (x : V ≃ₗ[K] V).toLinearMap h) (AdjoinRoot h)) (eSL d) :=
    rfl
  show e (chevQuotHom p J (eJ d)) = _
  simp only [e, MulEquiv.trans_apply, h1, h2, h3, h4]

theorem orthPaired_equiv
    (hpi : Function.Injective (piOrth Q))
    (hspecΩ : specialBlock Q (x : V ≃ₗ[K] V) h ≤ orthDerived Q)
    (J : Subgroup (ProjOrthDerived Q))
    (hJeq : J = componentImage Q (x : V ≃ₗ[K] V) h)
    (y : ↥(orthDerived Q))
    (hN : piOrth Q y ∈ Subgroup.normalizer (J : Set (ProjOrthDerived Q)))
    (hyc : (y : V ≃ₗ[K] V) ∈ isometryCentralizer Q (x : V ≃ₗ[K] V))
    (e : PSimple p J ≃* LargeEvenProj (StatedSL
      (primaryMultiplicity (x : V ≃ₗ[K] V).toLinearMap h) (AdjoinRoot h)))
    (eSL : ↥(specialBlock Q (x : V ≃ₗ[K] V) h) ≃*
      StatedSL (primaryMultiplicity (x : V ≃ₗ[K] V).toLinearMap h) (AdjoinRoot h))
    (he : ∀ d : ↥(specialBlock Q (x : V ≃ₗ[K] V) h),
      e (chevQuotHom p J (orthPairedComponentEquiv hpi hspecΩ J hJeq d)) =
        LargeEvenProjMk (StatedSL (primaryMultiplicity (x : V ≃ₗ[K] V).toLinearMap h)
          (AdjoinRoot h)) (eSL d))
    (B : GL (Fin (primaryMultiplicity (x : V ≃ₗ[K] V).toLinearMap h)) (AdjoinRoot h))
    (hBn : B ∈ Subgroup.normalizer (StatedSL (primaryMultiplicity
      (x : V ≃ₗ[K] V).toLinearMap h) (AdjoinRoot h) : Set (GL _ _)))
    (hconjSL : ∀ (d : ↥(specialBlock Q (x : V ≃ₗ[K] V) h))
      (hd : (y : V ≃ₗ[K] V)⁻¹ * d.1 * (y : V ≃ₗ[K] V) ∈
        specialBlock Q (x : V ≃ₗ[K] V) h),
      eSL ⟨(y : V ≃ₗ[K] V)⁻¹ * d.1 * (y : V ≃ₗ[K] V), hd⟩ =
        ⟨B * (eSL d : GL (Fin (primaryMultiplicity (x : V ≃ₗ[K] V).toLinearMap h))
          (AdjoinRoot h)) * B⁻¹,
          (Subgroup.mem_normalizer_iff.mp hBn
            (eSL d : GL (Fin (primaryMultiplicity (x : V ≃ₗ[K] V).toLinearMap h))
              (AdjoinRoot h))).mp (eSL d).2⟩) :
    ∀ m : ↥(StatedSL (primaryMultiplicity (x : V ≃ₗ[K] V).toLinearMap h) (AdjoinRoot h)),
      MulAut.congr e (MI.indAut p J (piOrth Q y) hN)
          (LargeEvenProjMk (StatedSL (primaryMultiplicity (x : V ≃ₗ[K] V).toLinearMap h)
            (AdjoinRoot h)) m) =
        LargeEvenProjMk (StatedSL (primaryMultiplicity (x : V ≃ₗ[K] V).toLinearMap h)
          (AdjoinRoot h))
          ⟨B * (m : GL (Fin (primaryMultiplicity (x : V ≃ₗ[K] V).toLinearMap h))
            (AdjoinRoot h)) * B⁻¹,
            (Subgroup.mem_normalizer_iff.mp hBn (m : GL (Fin (primaryMultiplicity
              (x : V ≃ₗ[K] V).toLinearMap h)) (AdjoinRoot h))).mp m.2⟩ := by
  intro m
  obtain ⟨d, rfl⟩ := eSL.surjective m
  have hd : (y : V ≃ₗ[K] V)⁻¹ * d.1 * (y : V ≃ₗ[K] V) ∈
      specialBlock Q (x : V ≃ₗ[K] V) h :=
    conj_mem_specialBlock (Subgroup.inv_mem _ hyc) d.2
  rw [show LargeEvenProjMk (StatedSL (primaryMultiplicity (x : V ≃ₗ[K] V).toLinearMap h)
      (AdjoinRoot h)) (eSL d) =
      e (chevQuotHom p J (orthPairedComponentEquiv hpi hspecΩ J hJeq d)) from (he d).symm]
  simp only [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply,
    MulEquiv.apply_symm_apply]
  rw [indAut_orthPairedComponentEquiv hpi hspecΩ J hJeq y hN d hd, he, hconjSL d hd]

theorem orthPaired_small_inner {a : ℕ} {E : Type} [Field E] [Finite E] {p : ℕ}
    {S : Type} [Group S] {J : Subgroup S} {y : S} {hN : y ∈ Subgroup.normalizer (J : Set S)}
    (e : PSimple p J ≃* LargeEvenProj (StatedSL a E))
    (B : GL (Fin a) E)
    (hBn : B ∈ Subgroup.normalizer (StatedSL a E : Set (GL (Fin a) E)))
    (hconj : MulAut.congr e (MI.indAut p J y hN) =
      CFSG.StandardType.TableB.projConj (StatedSL a E) ⟨B, hBn⟩)
    (hsmall : (a = 2 ∧ Nat.card E = 4) ∨ (a = 2 ∧ Nat.card E = 2) ∨
      (a = 3 ∧ Nat.card E = 2) ∨ (a = 4 ∧ Nat.card E = 2)) :
    MI.indAut p J y hN ∈
      CFSG.ComponentClassification.OuterAutomorphisms.inner (PSimple p J) := by
  have hinner : CFSG.StandardType.TableB.projConj (StatedSL a E) ⟨B, hBn⟩ ∈
      CFSG.ComponentClassification.OuterAutomorphisms.inner
        (LargeEvenProj (StatedSL a E)) := by
    rcases hsmall with ⟨rfl, hcard⟩ | ⟨rfl, hcard⟩ | ⟨rfl, hcard⟩ | ⟨rfl, hcard⟩
    · obtain ⟨μ, hμ⟩ := spPaired_exists_sl_scalar
        (E := E) (by rw [hcard]; norm_num) B
      have hB : B = Matrix.GeneralLinearGroup.scalar (Fin 2) μ *
          ((Matrix.GeneralLinearGroup.scalar (Fin 2) μ)⁻¹ * B) := by group
      exact @projConj_mem_inner_of_scalar_mul 2 E _ B μ
        ((Matrix.GeneralLinearGroup.scalar (Fin 2) μ)⁻¹ * B) hμ hB
    · exact projConj_mem_inner_of_card_two hcard B
    · exact projConj_mem_inner_of_card_two hcard B
    · exact projConj_mem_inner_of_card_two hcard B
  rw [← hconj] at hinner
  exact (CFSG.ComponentClassification.OuterAutomorphisms.congr_mem_inner_iff
    e (MI.indAut p J y hN)).mp hinner

end CFSG.LocalAnalysis.GLTheoremA.T171Sh

end
