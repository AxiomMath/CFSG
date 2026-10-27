module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeBoundOther
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeFamInLUComp
public import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.PslBadKey
public import CFSG.RankThree.PartOne.KC.UnitaryRigidityScalar
import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Conjugation
public import CFSG.HardMathSupport.Dickson.Sec6.I1431
public import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.BlocksAbstract
public import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.PslBadBlocks
public import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.PslBadEigen
public import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.PslSplit
public import CFSG.HardMathSupport.Dickson.Sec6.I1431LieAux.Inner
public import CFSG.HardMathSupport.Dickson.Sec6.I1431LieAux.Split

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T171Sh

open CFSG.Open CFSG.Assembly CFSG.StandardType CFSG.ClassicalGroups.UnitaryFlag
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
open CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCUnitary
open CFSG.RankThree.CALinearPrimary CFSG.ComponentClassification.CatalogueBHigherLinearAction
open Polynomial
open scoped commutatorElement

theorem glA_scalar_smul {N : ℕ} {K : Type} [Field K] (u : Kˣ) :
    ((glA (Matrix.GeneralLinearGroup.scalar (Fin N) u)) : Module.End K (Fin N → K)) =
      (u : K) • 1 := by
  ext v i
  simp [glA, Matrix.GeneralLinearGroup.toLin, Matrix.toLin'_apply,
    Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.mulVec_diagonal]

theorem linTypeOneNonComm_holds : LinTypeOneNonComm := by
  intro G _ _ p N n L J A d b K _ _ hcard hN θ hact hS hsetup M hc hnc
  classical
  obtain ⟨c, hc⟩ := hc
  let mat := M.mat
  let hmat := M.mem
  let hind := M.ind
  have hker := linKernelScalar_of_three_le (K := K) (N := N) hN
  let s : GL (Fin N) K := Matrix.GeneralLinearGroup.scalar (Fin N) c⁻¹
  let D : GL (Fin N) K := s * mat ⟨d, hsetup.d_mem⟩
  let Mb : GL (Fin N) K := mat ⟨b, hsetup.b_mem⟩
  have hs : s ∈ LargeEvenScalars (Fin N) K := by
    rw [largeEvenScalars_def]
    exact ⟨c⁻¹, rfl⟩
  have hDnorm : D ∈ Subgroup.normalizer (LargeEvenSLGroup (Fin N) K : Set (GL (Fin N) K)) :=
    Subgroup.mul_mem _ (TableB.scalar_mem_normalizer (LargeEvenSLGroup (Fin N) K) hs)
      (hS (hmat ⟨d, hsetup.d_mem⟩))
  have hBnorm : Mb ∈
      Subgroup.normalizer (LargeEvenSLGroup (Fin N) K : Set (GL (Fin N) K)) :=
    hS (hmat ⟨b, hsetup.b_mem⟩)
  have hsMd : s * mat ⟨d, hsetup.d_mem⟩ = mat ⟨d, hsetup.d_mem⟩ * s :=
    (Subgroup.mem_center_iff.mp
      (TableB.scalars_le_center hs) (mat ⟨d, hsetup.d_mem⟩)).symm
  have hsMb : s * Mb = Mb * s :=
    (Subgroup.mem_center_iff.mp (TableB.scalars_le_center hs) Mb).symm
  have hDpow : D ^ p = 1 := by
    have hsp : s ^ p = Matrix.GeneralLinearGroup.scalar (Fin N) ((c⁻¹ : Kˣ) ^ p) :=
      (map_pow (Matrix.GeneralLinearGroup.scalar (Fin N)) c⁻¹ p).symm
    rw [show D = s * mat ⟨d, hsetup.d_mem⟩ from rfl,
      Commute.mul_pow hsMd p, hsp, hc, ← map_mul, inv_pow, inv_mul_cancel, map_one]
  have hDind : LargeEvenInduces θ (conjRel d)
      (TableB.projConj (LargeEvenSLGroup (Fin N) K) ⟨D, hDnorm⟩) := by
    have hsub : (⟨D, hDnorm⟩ :
          Subgroup.normalizer (LargeEvenSLGroup (Fin N) K : Set (GL (Fin N) K))) =
        (⟨s, TableB.scalar_mem_normalizer (LargeEvenSLGroup (Fin N) K) hs⟩ :
          Subgroup.normalizer (LargeEvenSLGroup (Fin N) K : Set (GL (Fin N) K))) *
        ⟨mat ⟨d, hsetup.d_mem⟩, hS (hmat ⟨d, hsetup.d_mem⟩)⟩ := Subtype.ext rfl
    have hscalar : TableB.projConj (LargeEvenSLGroup (Fin N) K)
        (⟨s, TableB.scalar_mem_normalizer (LargeEvenSLGroup (Fin N) K) hs⟩ :
          Subgroup.normalizer (LargeEvenSLGroup (Fin N) K : Set (GL (Fin N) K))) = 1 :=
      TableB.projConj_of_scalar (LargeEvenSLGroup (Fin N) K) hs
    rw [hsub, map_mul, hscalar, one_mul]
    exact hind ⟨d, hsetup.d_mem⟩
  have hcommut : Mb * D * Mb⁻¹ * D⁻¹ ∈ LargeEvenScalars (Fin N) K := by
    have hbase := LiftMap.commutator_mem_scalars (L := L) (A := A) M hsetup
      ⟨b, hsetup.b_mem⟩ hker
    have hsc : ∀ y : GL (Fin N) K, y * s = s * y := fun y =>
      Subgroup.mem_center_iff.mp (TableB.scalars_le_center hs) y
    have heq : Mb * D * Mb⁻¹ * D⁻¹ =
        s * (Mb * mat ⟨d, hsetup.d_mem⟩ * Mb⁻¹ * (mat ⟨d, hsetup.d_mem⟩)⁻¹) * s⁻¹ := by
      calc Mb * D * Mb⁻¹ * D⁻¹
          = Mb * (s * mat ⟨d, hsetup.d_mem⟩) * Mb⁻¹ * (s * mat ⟨d, hsetup.d_mem⟩)⁻¹ := rfl
        _ = Mb * (s * mat ⟨d, hsetup.d_mem⟩) * Mb⁻¹ *
              ((mat ⟨d, hsetup.d_mem⟩)⁻¹ * s⁻¹) := by rw [mul_inv_rev]
        _ = Mb * s * mat ⟨d, hsetup.d_mem⟩ * Mb⁻¹ * (mat ⟨d, hsetup.d_mem⟩)⁻¹ * s⁻¹ := by
            group
        _ = s * Mb * mat ⟨d, hsetup.d_mem⟩ * Mb⁻¹ * (mat ⟨d, hsetup.d_mem⟩)⁻¹ * s⁻¹ := by
            rw [hsc Mb]
        _ = s * (Mb * mat ⟨d, hsetup.d_mem⟩ * Mb⁻¹ * (mat ⟨d, hsetup.d_mem⟩)⁻¹) *
              s⁻¹ := by group
    rw [heq]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hs hbase) (Subgroup.inv_mem _ hs)
  obtain ⟨ζ, hζ⟩ := by
    rw [largeEvenScalars_def, MonoidHom.mem_range] at hcommut
    exact hcommut
  have hconj : Mb * D * Mb⁻¹ = Matrix.GeneralLinearGroup.scalar (Fin N) ζ * D := by
    calc Mb * D * Mb⁻¹ = (Mb * D * Mb⁻¹ * D⁻¹) * D := by group
      _ = Matrix.GeneralLinearGroup.scalar (Fin N) ζ * D := by rw [← hζ]
  have hζ1 : ζ ≠ 1 := by
    intro h1
    apply hnc
    have hMD : Mb * D = D * Mb := by
      calc Mb * D = (Mb * D * Mb⁻¹) * Mb := by group
        _ = (Matrix.GeneralLinearGroup.scalar (Fin N) ζ * D) * Mb := by rw [hconj]
        _ = D * Mb := by rw [h1, map_one, one_mul]
    have h1' : Mb * (s * mat ⟨d, hsetup.d_mem⟩) =
        (s * mat ⟨d, hsetup.d_mem⟩) * Mb := by simpa only [D] using hMD
    have h3 : Mb * (s * mat ⟨d, hsetup.d_mem⟩) = s * (Mb * mat ⟨d, hsetup.d_mem⟩) := by
      calc Mb * (s * mat ⟨d, hsetup.d_mem⟩) = (Mb * s) * mat ⟨d, hsetup.d_mem⟩ :=
            (mul_assoc _ _ _).symm
        _ = (s * Mb) * mat ⟨d, hsetup.d_mem⟩ := by rw [← hsMb]
        _ = s * (Mb * mat ⟨d, hsetup.d_mem⟩) := mul_assoc _ _ _
    have h4 : (s * mat ⟨d, hsetup.d_mem⟩) * Mb = s * (mat ⟨d, hsetup.d_mem⟩ * Mb) :=
      mul_assoc _ _ _
    rw [h3, h4] at h1'
    exact mul_left_cancel h1'
  have hζp : (ζ : K) ^ p = 1 := by
    have hcommζD : Commute (Matrix.GeneralLinearGroup.scalar (Fin N) ζ) D := by
      rw [Commute]
      exact (Subgroup.mem_center_iff.mp
        (TableB.scalars_le_center (show Matrix.GeneralLinearGroup.scalar (Fin N) ζ ∈
          LargeEvenScalars (Fin N) K from ⟨ζ, rfl⟩)) D).symm
    have h1 : (Mb * D * Mb⁻¹) ^ p = 1 := by
      rw [show Mb * D * Mb⁻¹ = (MulAut.conj Mb) D from (MulAut.conj_apply Mb D).symm,
        ← map_pow, hDpow, map_one]
    rw [hconj, Commute.mul_pow hcommζD p, hDpow, mul_one] at h1
    haveI : Nonempty (Fin N) := ⟨⟨0, by omega⟩⟩
    have hinj := Matrix.GeneralLinearGroup.scalar_injective (n := Fin N) (R := K)
    have h2 : (ζ : Kˣ) ^ p = 1 := by
      apply hinj
      rw [map_pow, h1, map_one]
    simpa [Units.val_pow_eq_pow_val] using congrArg (fun u : Kˣ => (u : K)) h2
  haveI : Fact p.Prime := ⟨hsetup.prime⟩
  have hζroot : IsPrimitiveRoot (ζ : K) p := by
    have h := IsPrimitiveRoot.orderOf (ζ : K)
    rwa [orderOf_eq_prime hζp (fun h => hζ1 (Units.ext h))] at h
  have hodd : p ≠ 2 := hsetup.odd
  have hp0 : 0 < p := hsetup.prime.pos
  haveI : Fintype K := Fintype.ofFinite K
  haveI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  haveI : CharP K 2 := charP_of_card_eq_prime_pow (p := 2) (f := n) (by
    rw [← Nat.card_eq_fintype_card]; exact hcard)
  have hpk : (p : K) ≠ 0 := by
    rw [Ne, CharP.cast_eq_zero_iff K 2]
    intro hdvd
    have h2p : p = 2 := ((Nat.prime_dvd_prime_iff_eq (by norm_num) hsetup.prime).1 hdvd).symm
    exact hodd h2p
  have hDp' : D ^ p = Matrix.GeneralLinearGroup.scalar (Fin N) (1 : Kˣ) := by
    simpa using hDpow
  have hsq : Squarefree (minpoly K (glA D : Module.End K (Fin N → K))) :=
    squarefree_minpoly_glA (p := p) hpk hDp'
  have hann : aeval (glA D : Module.End K (Fin N → K)) ((X : K[X]) ^ p - 1) = 0 := by
    have hp : (glA D : LinearMap.GeneralLinearGroup K (Fin N → K)) ^ p = 1 := by
      rw [← map_pow, hDpow, map_one]
    have hp' : ((glA D : LinearMap.GeneralLinearGroup K (Fin N → K)) :
        Module.End K (Fin N → K)) ^ p = 1 := by
      rw [← Units.val_pow_eq_pow_val, hp]
      rfl
    rw [map_sub, map_pow, aeval_X, map_one]
    exact sub_eq_zero.mpr hp'
  have hdvd : minpoly K (glA D : Module.End K (Fin N → K)) ∣ (X : K[X]) ^ p - 1 :=
    minpoly.dvd K _ hann
  have hprod : (X : K[X]) ^ p - 1 = ∏ μ ∈ nthRootsFinset p (1 : K), (X - C μ) :=
    Polynomial.X_pow_sub_one_eq_prod hp0 hζroot
  obtain ⟨⟨⟨f, hf⟩, hgood⟩, hJeq⟩ :=
    specialFactor_of_component (K := K) (N := N) hsetup hcard θ D hDnorm hDpow hDind
  have hirr : Irreducible f := irreducible_of_mem_primaryFactors hf
  have hmonic : f.Monic := monic_of_mem_primaryFactors hf
  have hfmin : f ∣ minpoly K (glA D : Module.End K (Fin N → K)) := (mem_primaryFactors.mp hf).2.2
  have hfdvd : f ∣ X ^ p - 1 := hfmin.trans hdvd
  rw [hprod] at hfdvd
  obtain ⟨μ, hμmem, hμdvd⟩ := (Prime.dvd_finset_prod_iff hirr.prime (fun μ => X - C μ)).1 hfdvd
  have hdeg1 : f.natDegree = 1 := by
    have hle := natDegree_le_of_dvd hμdvd (monic_X_sub_C μ).ne_zero
    have hge : 1 ≤ f.natDegree := hirr.natDegree_pos
    have h1 : (X - C μ : K[X]).natDegree = 1 := natDegree_X_sub_C μ
    omega
  have hfeq : f = X - C μ :=
    (Polynomial.eq_of_monic_of_dvd_of_natDegree_le hmonic (monic_X_sub_C μ) hμdvd
      (by rw [natDegree_X_sub_C]; exact le_of_eq hdeg1.symm)).symm
  let ε : K := -f.coeff 0
  have hεμ : ε = μ := by
    simp [ε, hfeq]
  have hform' : f = X - C ε := by
    rw [hfeq, hεμ]
  have hμp : μ ^ p = 1 := (mem_nthRootsFinset hp0 (1 : K)).mp hμmem
  have hεp : ε ^ p = 1 := by rw [hεμ]; exact hμp
  have hε0 : ε ≠ 0 := by
    intro h0
    rw [h0, zero_pow hp0.ne'] at hεp
    exact zero_ne_one hεp
  let DlinG : LinearMap.GeneralLinearGroup K (Fin N → K) := glA D
  let MblinG : LinearMap.GeneralLinearGroup K (Fin N → K) := glA Mb
  let MbinvG : LinearMap.GeneralLinearGroup K (Fin N → K) := MblinG⁻¹
  let Dlin : Module.End K (Fin N → K) := (DlinG : Module.End K (Fin N → K))
  let Mblin : Module.End K (Fin N → K) := (MblinG : Module.End K (Fin N → K))
  let Mbinv : Module.End K (Fin N → K) := (MbinvG : Module.End K (Fin N → K))
  have hg : (Matrix.GeneralLinearGroup.toLin (Mb * D * Mb⁻¹) :
        LinearMap.GeneralLinearGroup K (Fin N → K)) =
      Matrix.GeneralLinearGroup.toLin
        (Matrix.GeneralLinearGroup.scalar (Fin N) ζ * D) := by
    rw [hconj]
  have hg' : MblinG * DlinG * MbinvG =
      (glA (Matrix.GeneralLinearGroup.scalar (Fin N) ζ) :
        LinearMap.GeneralLinearGroup K (Fin N → K)) * DlinG := by
    simpa [MblinG, DlinG, MbinvG, glA, map_mul] using hg
  have hlinconj : Mblin * Dlin * Mbinv = (ζ : K) • Dlin := by
    have h := congrArg (fun g : LinearMap.GeneralLinearGroup K (Fin N → K) =>
      (g : Module.End K (Fin N → K))) hg'
    simp only [Units.val_mul] at h
    rw [glA_scalar_smul] at h
    simpa [Mblin, Dlin, Mbinv, MblinG, DlinG, MbinvG, mul_smul] using h
  have hMDv : ∀ w : Fin N → K, Mblin (Dlin w) = (ζ : K) • Dlin (Mblin w) := by
    intro w
    have hbinv : Mbinv (Mblin w) = w := by
      show ((MbinvG : Module.End K (Fin N → K))) ((MblinG : Module.End K (Fin N → K)) w) = w
      rw [← Module.End.mul_apply, ← Units.val_mul, inv_mul_cancel, Units.val_one,
        Module.End.one_apply]
    have h := congrArg (fun T : Module.End K (Fin N → K) => T (Mblin w)) hlinconj
    simpa [Module.End.mul_apply, Mbinv, MbinvG, hbinv] using h
  have hVε : primaryComponent (glA D : Module.End K (Fin N → K)) f =
      Module.End.eigenspace (glA D : Module.End K (Fin N → K)) ε := by
    rw [hform']
    ext v
    rw [CFSG.RankThree.PartOne.KCUnitaryScalar.mem_primaryComponent_X_sub_C,
      Module.End.mem_eigenspace_iff]
  have hVne : primaryComponent (glA D : Module.End K (Fin N → K)) f ≠ ⊥ :=
    primaryComponent_ne_bot hsq hf
  have hbinvL : ∀ w : Fin N → K, Mbinv (Mblin w) = w := by
    intro w
    show ((MbinvG : Module.End K (Fin N → K))) ((MblinG : Module.End K (Fin N → K)) w) = w
    rw [← Module.End.mul_apply, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Module.End.one_apply]
  have hbinvR : ∀ w : Fin N → K, Mblin (Mbinv w) = w := by
    intro w
    show ((MblinG : Module.End K (Fin N → K))) ((MbinvG : Module.End K (Fin N → K)) w) = w
    rw [← Module.End.mul_apply, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Module.End.one_apply]
  have hMinj : Function.Injective Mblin := by
    intro x y hxy
    have h := congrArg Mbinv hxy
    rwa [hbinvL, hbinvL] at h
  let g : K[X] := X - C (ε / ζ)
  have hMV : (primaryComponent (glA D : Module.End K (Fin N → K)) f).map Mblin =
      primaryComponent (glA D : Module.End K (Fin N → K)) g := by
    ext w
    constructor
    · rintro ⟨v, hv, rfl⟩
      have hv' : Dlin v = ε • v := by
        rw [hform'] at hv
        exact (CFSG.RankThree.PartOne.KCUnitaryScalar.mem_primaryComponent_X_sub_C).mp hv
      have h := hMDv v
      rw [hv', map_smul] at h
      have hζ0 : (ζ : K) ≠ 0 := ζ.ne_zero
      have h2 := congrArg (fun x : Fin N → K => (ζ : K)⁻¹ • x) h
      simp only [smul_smul, inv_mul_cancel₀ hζ0, one_smul] at h2
      dsimp only [g]
      refine (CFSG.RankThree.PartOne.KCUnitaryScalar.mem_primaryComponent_X_sub_C).mpr ?_
      rw [div_eq_mul_inv, mul_comm]
      exact h2.symm
    · intro hw
      have hw' : Dlin w = (ε / ζ) • w := by
        dsimp only [g] at hw
        exact (CFSG.RankThree.PartOne.KCUnitaryScalar.mem_primaryComponent_X_sub_C).mp hw
      refine ⟨Mbinv w, ?_, hbinvR w⟩
      rw [hform']
      refine (CFSG.RankThree.PartOne.KCUnitaryScalar.mem_primaryComponent_X_sub_C).mpr ?_
      apply hMinj
      rw [hMDv (Mbinv w), hbinvR, hw', map_smul, hbinvR]
      rw [smul_smul]
      have hζdiv : (ζ : K) * (ε / ζ) = ε := by field_simp
      rw [hζdiv]
  have hgmem : g ∈ primaryFactors (glA D : Module.End K (Fin N → K)) := by
    have hgne : Module.End.eigenspace (glA D : Module.End K (Fin N → K)) (ε / ζ) ≠ ⊥ := by
      obtain ⟨v, hv, hvne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hVne
      refine Submodule.ne_bot_iff _ |>.mpr ⟨Mblin v, ?_, by simpa using hMinj.ne hvne⟩
      have hv' : Dlin v = ε • v := by
        rw [hform'] at hv
        exact (CFSG.RankThree.PartOne.KCUnitaryScalar.mem_primaryComponent_X_sub_C).mp hv
      have h := hMDv v
      rw [hv', map_smul] at h
      rw [Module.End.mem_eigenspace_iff]
      have hζ0 : (ζ : K) ≠ 0 := ζ.ne_zero
      have h2 := congrArg (fun x : Fin N → K => (ζ : K)⁻¹ • x) h
      simp only [smul_smul, inv_mul_cancel₀ hζ0, one_smul] at h2
      rw [div_eq_mul_inv, mul_comm]
      exact h2.symm
    exact CFSG.RankThree.PartOne.KCUnitaryScalar.X_sub_C_mem_primaryFactors
      (Module.End.hasEigenvalue_iff.mpr hgne)
  have hgf : g ≠ f := by
    intro h
    rw [hform'] at h
    have h1 : ε / ζ = ε := by
      have h := congrArg (fun p : K[X] => p.coeff 0) h
      dsimp only [g] at h
      simpa using h
    have h2 : ε = ε * (ζ : K) := (div_eq_iff ζ.ne_zero).mp h1
    have h3 : (ζ : K) = 1 := by
      exact (mul_left_cancel₀ hε0 (by rw [mul_one]; exact h2)).symm
    exact hζ1 (Units.ext h3)
  let e := CFSG.LocalAnalysis.GLTheoremA.I2015.linRecipeEquiv N K
  let φ : MulAut (LargeEvenProj (LargeEvenSLGroup (Fin N) K)) :=
    TableB.projConj (LargeEvenSLGroup (Fin N) K) ⟨Mb, hBnorm⟩
  let PJ : Subgroup (LargeEvenProj (LargeEvenSLGroup (Fin N) K)) :=
    (J.subgroupOf L).map (piCenterQuot θ)
  let K₀ : Subgroup (projectiveSL N K) := (specialFactor D f).map (proj N K)
  have hJ' : PJ.map e.symm.toMonoidHom = K₀ := hJeq
  have hbL : b ∈ Subgroup.normalizer (L : Set G) :=
    CFSG.LocalAnalysis.GLTheoremA.S11.le_normalizer_of_innerDiag hsetup.idiag hsetup.b_mem
  have hPJle : PJ.map φ.toMonoidHom ≤ PJ := by
    rintro y ⟨x, hx, rfl⟩
    obtain ⟨j, hj, rfl⟩ := Subgroup.mem_map.mp hx
    have hjJ : (j : G) ∈ J := (Subgroup.mem_subgroupOf).mp hj
    have hmemL : b⁻¹ * (j : G) * b ∈ L := by
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hbL) (j : G)).mp j.2
      simpa using this
    have hmemJ : b⁻¹ * (j : G) * b ∈ J := by
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hsetup.b_norm) (j : G)).mp hjJ
      simpa using this
    have hrel : conjRel b j ⟨b⁻¹ * (j : G) * b, hmemL⟩ := rfl
    have h := hind ⟨b, hsetup.b_mem⟩ j ⟨b⁻¹ * (j : G) * b, hmemL⟩ hrel
    refine Subgroup.mem_map.mpr ⟨⟨b⁻¹ * (j : G) * b, hmemL⟩,
      Subgroup.mem_subgroupOf.mpr hmemJ, ?_⟩
    exact h.symm
  have hPJinv : PJ.map φ.toMonoidHom = PJ := by
    refine Subgroup.eq_of_le_of_card_ge hPJle ?_
    rw [show Nat.card ↥(Subgroup.map (MulEquiv.toMonoidHom φ) PJ) = Nat.card ↥PJ from
      Subgroup.card_map_of_injective (f := MulEquiv.toMonoidHom φ) φ.injective]
  have hcomp : (LinearFlag.conjAut N K Mb).toMonoidHom.comp e.symm.toMonoidHom =
      e.symm.toMonoidHom.comp φ.toMonoidHom := by
    ext x
    have hrecipe : MulAut.congr e.symm φ = LinearFlag.conjAut N K Mb :=
      projConj_recipe (K := K) (N := N) Mb hBnorm
    have h := congrArg (fun α : MulAut (projectiveSL N K) => α (e.symm x)) hrecipe
    simpa [MulAut.congr_apply] using h.symm
  have hK0inv : K₀.map (LinearFlag.conjAut N K Mb).toMonoidHom = K₀ := by
    rw [← hJ', Subgroup.map_map, hcomp, ← Subgroup.map_map, hPJinv, hJ']
  have hfix_of_mem : ∀ (a : Matrix.SpecialLinearGroup (Fin N) K),
      a ∈ specialFactor D f → ∀ {j : K[X]}, j ∈ primaryFactors (glA D : Module.End K (Fin N → K)) →
        j ≠ f → ∀ v ∈ primaryComponent (glA D : Module.End K (Fin N → K)) j,
          (slGL N K a : Module.End K (Fin N → K)) v = v := by
    intro a ha j hj hjf v hv
    have hL : slGL N K a ∈ linearSpecialBlock (glA D) f := ha
    exact (mem_linearSpecialBlock.mp hL).2.1 j hj hjf v hv
  have hcentral_of_scalar : ∀ x : ↥(specialFactor D f),
      (∃ μ : K, ∀ v ∈ primaryComponent (glA D : Module.End K (Fin N → K)) f,
        (slGL N K (x : Matrix.SpecialLinearGroup (Fin N) K) :
          Module.End K (Fin N → K)) v = μ • v) →
      x ∈ Subgroup.center ↥(specialFactor D f) := by
    intro x hx
    obtain ⟨μ, hμ⟩ := hx
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    apply slGL_injective
    rw [Subgroup.coe_mul, Subgroup.coe_mul, map_mul, map_mul]
    apply Units.ext
    rw [Units.val_mul, Units.val_mul]
    apply ext_primaryComponent hsq
    intro j hj v hv
    by_cases hje : j = f
    · rw [hje] at hv
      have hyL : slGL N K (y : Matrix.SpecialLinearGroup (Fin N) K) ∈
          linearSpecialBlock (glA D) f := y.2
      have hyc : Commute ((slGL N K (y : Matrix.SpecialLinearGroup (Fin N) K) :
          Module.End K (Fin N → K))) (glA D : Module.End K (Fin N → K)) :=
        (mem_gl_centralizer (x := (glA D))).mp (mem_linearSpecialBlock.mp hyL).1
      have hyv : (slGL N K (y : Matrix.SpecialLinearGroup (Fin N) K) :
          Module.End K (Fin N → K)) v ∈ primaryComponent (glA D : Module.End K (Fin N → K)) f :=
        apply_mem_primaryComponent hyc hv
      simp only [Module.End.mul_apply]
      rw [hμ _ hyv, hμ _ hv, map_smul]
    · have hxf := hfix_of_mem (x : Matrix.SpecialLinearGroup (Fin N) K) x.2 hj hje v hv
      have hyf := hfix_of_mem (y : Matrix.SpecialLinearGroup (Fin N) K) y.2 hj hje v hv
      simp only [Module.End.mul_apply]
      rw [hyf, hxf]
      exact hyf
  have hnoncomm : ∃ a b : ↥(specialFactor D f), a * b ≠ b * a := by
    by_contra h
    push Not at h
    obtain ⟨a, b, hab⟩ := (isQuasisimple_specialFactor (A := D) hsq hf hgood).2.2
    obtain ⟨a', rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨b', rfl⟩ := QuotientGroup.mk_surjective b
    exact hab (by rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, h a' b'])
  have hcent : Subgroup.center ↥(specialFactor D f) ≠ ⊤ := by
    intro htop
    obtain ⟨a, b, hab⟩ := hnoncomm
    exact hab ((Subgroup.mem_center_iff.mp (by rw [htop]; exact Subgroup.mem_top a)) b).symm
  obtain ⟨x, hxnc⟩ : ∃ x : ↥(specialFactor D f), x ∉ Subgroup.center ↥(specialFactor D f) := by
    by_contra h
    exact hcent (eq_top_iff.mpr fun a _ => by
      by_contra ha
      exact h ⟨a, ha⟩)
  have hxscalar : ¬ ∃ μ : K, ∀ v ∈ primaryComponent (glA D : Module.End K (Fin N → K)) f,
      (slGL N K (x : Matrix.SpecialLinearGroup (Fin N) K) : Module.End K (Fin N → K)) v = μ • v :=
    fun h => hxnc (hcentral_of_scalar x h)
  have hproj_mem : ∀ a : Matrix.SpecialLinearGroup (Fin N) K, a ∈ specialFactor D f →
      ∃ b' ∈ specialFactor D f,
        (proj N K) (slConjugation N K Mb a) = (proj N K) b' := by
    intro a ha
    have hmem : (proj N K) a ∈ K₀ := Subgroup.mem_map.mpr ⟨a, ha, rfl⟩
    have hmem' : (LinearFlag.conjAut N K Mb) ((proj N K) a) ∈ K₀ := by
      have h := Subgroup.mem_map_of_mem (LinearFlag.conjAut N K Mb).toMonoidHom hmem
      rwa [hK0inv] at h
    rw [LinearFlag.conjAut_proj] at hmem'
    obtain ⟨b', hb', hb'eq⟩ := Subgroup.mem_map.mp hmem'
    exact ⟨b', hb', hb'eq.symm⟩
  obtain ⟨x', hx'mem, hx'proj⟩ := hproj_mem (x : Matrix.SpecialLinearGroup (Fin N) K) x.2
  have hscal : (slConjugation N K Mb
      (x : Matrix.SpecialLinearGroup (Fin N) K))⁻¹ * x' ∈ LinearFlag.scalars N K :=
    (LinearFlag.proj_eq_proj_iff).mp hx'proj
  obtain ⟨c, hcN, hcmat⟩ := LinearFlag.mem_scalars.mp hscal
  have hSL : (slConjugation N K Mb
        (x : Matrix.SpecialLinearGroup (Fin N) K))⁻¹ * x' =
      LinearFlag.scalarElement c hcN := Subtype.ext hcmat
  have heq : x' = slConjugation N K Mb
        (x : Matrix.SpecialLinearGroup (Fin N) K) * LinearFlag.scalarElement c hcN := by
    rw [← hSL]
    group
  have htoGL : Matrix.SpecialLinearGroup.toGL (LinearFlag.scalarElement c hcN) =
      Matrix.GeneralLinearGroup.scalar (Fin N) c := by
    apply Units.ext
    rw [Matrix.SpecialLinearGroup.coe_GL_coe_matrix]
    simp [LinearFlag.scalarElement]
  have hscalarGL : (slGL N K (LinearFlag.scalarElement c hcN) :
      LinearMap.GeneralLinearGroup K (Fin N → K)) =
      glA (Matrix.GeneralLinearGroup.scalar (Fin N) c) := by
    rw [← htoGL]
    rfl
  have hslconj : (slGL N K (slConjugation N K Mb
        (x : Matrix.SpecialLinearGroup (Fin N) K)) :
      LinearMap.GeneralLinearGroup K (Fin N → K)) =
      MblinG * (slGL N K (x : Matrix.SpecialLinearGroup (Fin N) K)) * MbinvG := by
    simp only [slGL, MonoidHom.comp_apply, toGL_slConjugation,
      map_mul, map_inv]
    rfl
  have hact_g : ∀ v ∈ primaryComponent (glA D : Module.End K (Fin N → K)) g,
      (slGL N K (slConjugation N K Mb
        (x : Matrix.SpecialLinearGroup (Fin N) K)) : Module.End K (Fin N → K)) v =
        ((c⁻¹ : Kˣ) : K) • v := by
    intro v hv
    have h := congrArg (fun s : Matrix.SpecialLinearGroup (Fin N) K =>
      (slGL N K s : LinearMap.GeneralLinearGroup K (Fin N → K))) heq
    rw [map_mul, hscalarGL] at h
    have h2 := congrArg (fun u : LinearMap.GeneralLinearGroup K (Fin N → K) =>
      (u : Module.End K (Fin N → K)) v) h
    rw [Units.val_mul, Module.End.mul_apply, glA_scalar_smul] at h2
    have hxv : (slGL N K x' : Module.End K (Fin N → K)) v = v :=
      hfix_of_mem x' hx'mem hgmem hgf v hv
    have h2' : v = (slGL N K (slConjugation N K Mb
        (x : Matrix.SpecialLinearGroup (Fin N) K)) : Module.End K (Fin N → K)) ((c : K) • v) := by
      calc v = (slGL N K x' : Module.End K (Fin N → K)) v := hxv.symm
        _ = (slGL N K (slConjugation
              N K Mb (x : Matrix.SpecialLinearGroup (Fin N) K)) :
              Module.End K (Fin N → K)) ((c : K) • v) := by
            simpa using h2
    rw [map_smul] at h2'
    have hc0 : (c : K) ≠ 0 := c.ne_zero
    have h3 := congrArg (fun w : Fin N → K => ((c : K)⁻¹) • w) h2'.symm
    simpa only [smul_smul, inv_mul_cancel₀ hc0, one_smul, Units.val_inv_eq_inv_val] using h3
  refine hxscalar ⟨((c⁻¹ : Kˣ) : K), fun w hw => ?_⟩
  have hMv : Mblin w ∈ primaryComponent (glA D : Module.End K (Fin N → K)) g := by
    rw [← hMV]
    exact Submodule.mem_map.mpr ⟨w, hw, rfl⟩
  have h1 : Mblin ((slGL N K (x : Matrix.SpecialLinearGroup (Fin N) K) :
      Module.End K (Fin N → K)) w) = ((c⁻¹ : Kˣ) : K) • Mblin w := by
    have h := hact_g (Mblin w) hMv
    rw [hslconj] at h
    rw [Units.val_mul, Units.val_mul, Module.End.mul_apply, Module.End.mul_apply,
      hbinvL] at h
    exact h
  exact hMinj (h1.trans (map_smul Mblin ((c⁻¹ : Kˣ) : K) w).symm)

end CFSG.LocalAnalysis.GLTheoremA.T171Sh

end
