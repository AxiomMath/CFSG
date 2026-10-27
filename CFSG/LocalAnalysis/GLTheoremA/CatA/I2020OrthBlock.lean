module

public import CFSG.LinearAlgebra.QuadraticPieceDihedral
public import CFSG.Quasithin.Vol2.Ch12Sec9Lemma3SL3Lin
public import CFSG.RankThree.CentralCover.SteinbergBNOrthogonalRepeatedSummands
public import CFSG.RankThree.PartOne.KC.SymplecticIsotypicSpecial
public import CFSG.RankThree.PartOne.KC.OrthogonalBlockQuasisimple
public import CFSG.RankThree.PartOne.KC.OrthogonalPrimarySummands
public import CFSG.RankThree.PartOne.KC.OrthogonalSelfDualBlock
public import CFSG.RankThree.PartOne.KC.OrthogonalPairedBlock
public import CFSG.RankThree.PartOne.KC.OrthogonalFixedDickson
public import Mathlib.GroupTheory.Sylow
public import Mathlib.FieldTheory.Finite.Trace
public import Mathlib.RingTheory.Norm.Defs
public import Mathlib.LinearAlgebra.Pi
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.ClassicalInvolution.Balance.PassTwoConj
public import CFSG.ClassicalInvolution.Models.LinearFrames
public import CFSG.ClassicalInvolution.Models.LinearPairs
public import CFSG.ClassicalInvolution.Models.OrthogonalPairs
public import CFSG.ClassicalInvolution.Models.SymplecticPairs
public import CFSG.ClassicalInvolution.Models.Transfer
public import CFSG.ClassicalInvolution.Models.UnitaryPairs
public import CFSG.ClassicalInvolution.Q3.ClassicalFundamentalModels
public import CFSG.ClassicalInvolution.Q3.Q3PlanParams
public import CFSG.ClassicalInvolution.RouteD.TypeAChain
public import CFSG.LieType.Ree.SmallReeModelSchreier
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBDerivedNormalSectionBound
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOddLieClassical
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOddLieE6E7Triality
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalDescentEndpoint
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFiveStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointActionModels
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointPlusBorelModel
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareField
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixComponentsCover
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixModelGeometry
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalTraceZeroCoordinates
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBProjectiveInvolutionStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups
public import CFSG.LocalAnalysis.ComponentClassification.PrimeComplementQuotientComponents
public import CFSG.LocalAnalysis.ComponentInitial.BlockOvergroupDichotomy
public import CFSG.LocalAnalysis.ComponentInitial.GeneralizedFittingProduct
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasSix
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalStandardFormsRegular
public import CFSG.LocalAnalysis.ComponentInitial.SylowPointRecovery
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.RankThree.PartOne.KC.OrthogonalBinaryDickson
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Isaacs.VII.lemma_7_7
public import Certificates.Certificate1
public import Certificates.Certificate10
public import Certificates.Certificate11
public import Certificates.Certificate12
public import Certificates.Certificate2
public import Certificates.Certificate3
public import Certificates.Certificate4
public import Certificates.Certificate42
public import Certificates.Certificate43
public import Certificates.Certificate44
public import Certificates.Certificate5
public import Certificates.Certificate6
public import Certificates.Certificate7
public import Certificates.Certificate8
public import Certificates.Certificate8046
public import Certificates.Certificate8049
public import Certificates.Certificate9
public import TauCeti.LinearAlgebra.Dimension.IsQuadraticExtension
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalBasis
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalGroup.LowRank

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I2020

open QuadraticMap

open Polynomial Module CFSG.RankThree.PartOne.KCPrimary
  CFSG.RankThree.PartOne.KCOrthogonal
open scoped Pointwise

variable {K V : Type*} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V} {p : ℕ} {x : V ≃ₗ[K] V}

private theorem finish (h2 : (2 : K) ≠ 0) (hpodd : Odd p)
    (hxQ : x ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hxp : x ^ p = 1)
    {h : K[X]} {E : Subgroup (V ≃ₗ[K] V)} (hE2 : IsPGroup 2 E)
    (hEspec : E ≤ specialBlock Q x h)
    {T : Subgroup (V ≃ₗ[K] V)} (hT : T ≤ specialBlock Q x h) (hT2 : IsPGroup 2 T)
    (hTodd : ¬ 2 ∣ (T.subgroupOf (specialBlock Q x h)).index)
    {ι : Type*} [Fintype ι] (P : ι → Submodule K V) (hspan : ⨆ i, P i = ⊤)
    (hxP : ∀ i, ∀ v ∈ P i, x v ∈ P i)
    (hplane : ∀ i, (∀ v ∈ P i, x v = v) ∨
      ∃ xP : P i ≃ₗ[K] P i, (∀ v, (xP v : V) = x v) ∧
        (QuadraticMap.polarBilin (Q.comp (P i).subtype)).Nondegenerate ∧
        Module.finrank K (P i) = 2 ∧ LinearEquiv.det xP = 1)
    (hpres : ∀ (S' : Subgroup (V ≃ₗ[K] V)), (∀ s' ∈ S', ∀ e ∈ E, s' * e = e * s') →
      ∀ s' ∈ S', ∀ i, ∀ v ∈ P i, s' v ∈ P i)
    {S : Subgroup (V ≃ₗ[K] V)} (hS2 : IsPGroup 2 S)
    (hSQ : ∀ s ∈ S, ∀ v, Q (s v) = Q v)
    (hxS : x ∈ Subgroup.normalizer (S : Set (V ≃ₗ[K] V)))
    (hST : ∀ s ∈ S, ∀ t ∈ T, s * t = t * s) :
    ∀ s ∈ S, s * x = x * s := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Finite V := Module.finite_of_finite K
  haveI : Fintype V := Fintype.ofFinite V
  haveI : Finite (V ≃ₗ[K] V) :=
    Finite.of_injective (fun g : V ≃ₗ[K] V => (g : V → V))
      (fun f g h => LinearEquiv.ext (congrFun h))
  haveI : Finite (specialBlock Q x h) := Subtype.finite
  let T' : Subgroup (specialBlock Q x h) := T.subgroupOf (specialBlock Q x h)
  have hT'2 : IsPGroup 2 T' := hT2.of_equiv (Subgroup.subgroupOfEquivOfLe hT).symm
  let E' : Subgroup (specialBlock Q x h) := E.subgroupOf (specialBlock Q x h)
  have hE'2 : IsPGroup 2 E' := hE2.of_equiv (Subgroup.subgroupOfEquivOfLe hEspec).symm
  obtain ⟨Q', hEQ'⟩ := hE'2.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (specialBlock Q x h) (hT'2.toSylow hTodd) Q'
  have hQ' : (Q' : Subgroup (specialBlock Q x h)) = MulAut.conj g • T' := by
    rw [← hg, Sylow.coe_subgroup_smul, IsPGroup.toSylow_coe]
  have hgO : ∀ v, Q ((g : V ≃ₗ[K] V) v) = Q v :=
    (mem_isometryCentralizer.mp (specialBlock_le_isometryCentralizer h g.2)).1
  have hginvO : ∀ v, Q (((g : V ≃ₗ[K] V))⁻¹ v) = Q v :=
    (mem_isometryCentralizer.mp
      (inv_mem (specialBlock_le_isometryCentralizer h g.2))).1
  have hgx : Commute (g : V ≃ₗ[K] V) x :=
    LinearEquiv.ext (mem_isometryCentralizer.mp
      (specialBlock_le_isometryCentralizer h g.2)).2
  have hconjE : ∀ e ∈ E, ∃ t ∈ T, (g : V ≃ₗ[K] V)⁻¹ * e * (g : V ≃ₗ[K] V) = t := by
    intro e he
    have he' : (⟨e, hEspec he⟩ : specialBlock Q x h) ∈ E' := he
    have hQe : (⟨e, hEspec he⟩ : specialBlock Q x h) ∈
        (Q' : Subgroup (specialBlock Q x h)) := hEQ' he'
    rw [hQ'] at hQe
    obtain ⟨t', ht', ht'e⟩ := Subgroup.mem_map.mp hQe
    refine ⟨(t' : V ≃ₗ[K] V), ht', ?_⟩
    have h1 : (g : V ≃ₗ[K] V) * (t' : V ≃ₗ[K] V) * (g : V ≃ₗ[K] V)⁻¹ = e := by
      have := congrArg (fun w : specialBlock Q x h => (w : V ≃ₗ[K] V)) ht'e
      simpa [MulAut.conj_apply] using this
    rw [← h1]
    group
  let S' : Subgroup (V ≃ₗ[K] V) := S.map (MulAut.conj (g : V ≃ₗ[K] V)).toMonoidHom
  have hS'2 : IsPGroup 2 S' := hS2.map _
  have hS'Q : S' ≤ TauCeti.QuadraticMap.orthogonalGroup Q := by
    intro s' hs'
    obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.mp hs'
    rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
    intro v
    show Q ((g : V ≃ₗ[K] V) (s ((g : V ≃ₗ[K] V)⁻¹ v))) = Q v
    rw [hgO, hSQ s hs _]
    exact hginvO v
  have hxinv_g : x⁻¹ * (g : V ≃ₗ[K] V) = (g : V ≃ₗ[K] V) * x⁻¹ := by
    have h := congrArg (fun w : V ≃ₗ[K] V => x⁻¹ * w * x⁻¹) hgx.eq
    simpa [mul_assoc] using h
  have hgx_inv : (g : V ≃ₗ[K] V)⁻¹ * x = x * (g : V ≃ₗ[K] V)⁻¹ := by
    have h : x * (g : V ≃ₗ[K] V)⁻¹ = (g : V ≃ₗ[K] V)⁻¹ * x := by
      have h' := congrArg (fun w : V ≃ₗ[K] V => (g : V ≃ₗ[K] V)⁻¹ * w * (g : V ≃ₗ[K] V)⁻¹)
        hgx.eq
      simpa [mul_assoc] using h'
    exact h.symm
  have hgx_inv' : (g : V ≃ₗ[K] V)⁻¹ * x⁻¹ = x⁻¹ * (g : V ≃ₗ[K] V)⁻¹ := by
    have h : x⁻¹ * (g : V ≃ₗ[K] V)⁻¹ = (g : V ≃ₗ[K] V)⁻¹ * x⁻¹ := by
      have h' := congrArg (fun w : V ≃ₗ[K] V => w⁻¹) hgx.eq
      simpa [mul_assoc] using h'
    exact h.symm
  have hxS' : x ∈ Subgroup.normalizer (S' : Set (V ≃ₗ[K] V)) := by
    rw [Subgroup.mem_normalizer_iff]
    intro s'
    constructor
    · intro hs'
      obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.mp hs'
      have hxs : x * s * x⁻¹ ∈ S := (Subgroup.mem_normalizer_iff.mp hxS s).mp hs
      change x * ((g : V ≃ₗ[K] V) * s * (g : V ≃ₗ[K] V)⁻¹) * x⁻¹ ∈ S'
      have heq : x * ((g : V ≃ₗ[K] V) * s * (g : V ≃ₗ[K] V)⁻¹) * x⁻¹ =
          (g : V ≃ₗ[K] V) * (x * s * x⁻¹) * (g : V ≃ₗ[K] V)⁻¹ := by
        calc x * ((g : V ≃ₗ[K] V) * s * (g : V ≃ₗ[K] V)⁻¹) * x⁻¹
            = (x * (g : V ≃ₗ[K] V)) * s * ((g : V ≃ₗ[K] V)⁻¹ * x⁻¹) := by group
          _ = ((g : V ≃ₗ[K] V) * x) * s * (x⁻¹ * (g : V ≃ₗ[K] V)⁻¹) := by
              rw [hgx.eq, hgx_inv']
          _ = (g : V ≃ₗ[K] V) * (x * s * x⁻¹) * (g : V ≃ₗ[K] V)⁻¹ := by group
      rw [heq]
      exact Subgroup.mem_map.mpr ⟨x * s * x⁻¹, hxs, rfl⟩
    · intro hs'
      obtain ⟨t, ht, hte⟩ := Subgroup.mem_map.mp hs'
      have hxt : x⁻¹ * t * x ∈ S :=
        (Subgroup.mem_normalizer_iff.mp (inv_mem hxS) t).mp ht
      have hs_eq : s' = (g : V ≃ₗ[K] V) * (x⁻¹ * t * x) * (g : V ≃ₗ[K] V)⁻¹ := by
        calc s' = x⁻¹ * (x * s' * x⁻¹) * x := by group
          _ = x⁻¹ * ((g : V ≃ₗ[K] V) * t * (g : V ≃ₗ[K] V)⁻¹) * x := by
              rw [← hte]
              rfl
          _ = (x⁻¹ * (g : V ≃ₗ[K] V)) * t * ((g : V ≃ₗ[K] V)⁻¹ * x) := by group
          _ = ((g : V ≃ₗ[K] V) * x⁻¹) * t * (x * (g : V ≃ₗ[K] V)⁻¹) := by
              rw [hxinv_g, hgx_inv]
          _ = (g : V ≃ₗ[K] V) * (x⁻¹ * t * x) * (g : V ≃ₗ[K] V)⁻¹ := by group
      rw [hs_eq]
      exact Subgroup.mem_map.mpr ⟨x⁻¹ * t * x, hxt, rfl⟩
  have hcentE : ∀ s' ∈ S', ∀ e ∈ E, s' * e = e * s' := by
    intro s' hs' e he
    obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.mp hs'
    obtain ⟨t, ht, hte⟩ := hconjE e he
    have heE : e = (g : V ≃ₗ[K] V) * t * (g : V ≃ₗ[K] V)⁻¹ := by
      rw [← hte]
      group
    calc ((g : V ≃ₗ[K] V) * s * (g : V ≃ₗ[K] V)⁻¹) * e
        = (g : V ≃ₗ[K] V) * (s * t) * (g : V ≃ₗ[K] V)⁻¹ := by rw [heE]; group
      _ = (g : V ≃ₗ[K] V) * (t * s) * (g : V ≃ₗ[K] V)⁻¹ := by rw [hST s hs t ht]
      _ = e * ((g : V ≃ₗ[K] V) * s * (g : V ≃ₗ[K] V)⁻¹) := by rw [heE]; group
  have hmain := CFSG.LinearAlgebra.commute_of_isPGroup_of_pieces (Q := Q) h2 hpodd hxQ hxp
    P hspan hxP hplane hS'2 hS'Q hxS' (hpres S' hcentE)
  intro s hs
  have hs' : (g : V ≃ₗ[K] V) * s * (g : V ≃ₗ[K] V)⁻¹ ∈ S' :=
    Subgroup.mem_map.mpr ⟨s, hs, rfl⟩
  have hcomm := hmain _ hs'
  have hconjx : (MulAut.conj (g : V ≃ₗ[K] V)) x = x := by
    rw [MulAut.conj_apply, hgx.eq]
    group
  apply (MulAut.conj (g : V ≃ₗ[K] V)).injective
  rw [map_mul, map_mul, hconjx]
  simpa [MulAut.conj_apply] using hcomm

def BlockDiagonalData (Q : QuadraticForm K V) (x : V ≃ₗ[K] V) (h : K[X]) : Prop :=
  ∃ (E : Subgroup (V ≃ₗ[K] V)), IsPGroup 2 E ∧ E ≤ specialBlock Q x h ∧
    ∃ (ι : Type), ∃ (_ : Fintype ι), ∃ (P : ι → Submodule K V),
      (⨆ i, P i = ⊤) ∧
      (∀ i, ∀ v ∈ P i, x v ∈ P i) ∧
      (∀ i, (∀ v ∈ P i, x v = v) ∨
        ∃ xP : P i ≃ₗ[K] P i, (∀ v, (xP v : V) = x v) ∧
          (QuadraticMap.polarBilin (Q.comp (P i).subtype)).Nondegenerate ∧
          Module.finrank K (P i) = 2 ∧ LinearEquiv.det xP = 1) ∧
      (∀ (S' : Subgroup (V ≃ₗ[K] V)), (∀ s' ∈ S', ∀ e ∈ E, s' * e = e * s') →
        ∀ s' ∈ S', ∀ i, ∀ v ∈ P i, s' v ∈ P i)

private theorem blockDet_conj_eq
    {h : K[X]} {g k : V ≃ₗ[K] V}
    (hg : g ∈ supportedBlock Q x h) (hk : k ∈ supportedBlock Q x h)
    (hkg : k * g * k⁻¹ ∈ supportedBlock Q x h) :
    blockDet Q x h ⟨k * g * k⁻¹, hkg⟩ = blockDet Q x h ⟨g, hg⟩ := by
  have hprod : (⟨k * g * k⁻¹, hkg⟩ : ↥(supportedBlock Q x h)) =
      ⟨k, hk⟩ * ⟨g, hg⟩ * (⟨k, hk⟩)⁻¹ := by
    ext
    rfl
  have h1 : blockDet Q x h ⟨k, hk⟩ *
      blockDet Q x h ⟨k⁻¹, Subgroup.inv_mem _ hk⟩ = 1 := by
    rw [← map_mul]
    have hk1 : (⟨k, hk⟩ * ⟨k⁻¹, Subgroup.inv_mem _ hk⟩ : ↥(supportedBlock Q x h)) = 1 := by
      ext
      simp
    rw [hk1, map_one]
  rw [hprod, map_mul, map_mul]
  calc blockDet Q x h ⟨k, hk⟩ * blockDet Q x h ⟨g, hg⟩ *
        blockDet Q x h ⟨k⁻¹, Subgroup.inv_mem _ hk⟩
      = blockDet Q x h ⟨g, hg⟩ *
          (blockDet Q x h ⟨k, hk⟩ *
            blockDet Q x h ⟨k⁻¹, Subgroup.inv_mem _ hk⟩) := by
        rw [mul_comm (blockDet Q x h ⟨k, hk⟩), mul_assoc]
    _ = blockDet Q x h ⟨g, hg⟩ * 1 := by rw [h1]
    _ = blockDet Q x h ⟨g, hg⟩ := mul_one _

private theorem blockDiagonalData_of_repeated
    (hx : OddOrderIsometry Q p x) (hp : p.Prime) (hp2 : p ≠ 2) (h2 : (2 : K) ≠ 0)
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hdim : Module.finrank K V ≤ 8)
    {h : K[X]} (hh : h ∈ primaryFactors x.toLinearMap) {m : ℕ} (hm : 3 ≤ m)
    {R W : Type*} [AddCommGroup R] [Module K R] [AddCommGroup W] [Module K W]
    (QR : QuadraticForm K R) (QW : QuadraticForm K W)
    (ψ : V ≃ₗ[K] R × (Fin m → W))
    (hQsum : ∀ v, Q v = QR (ψ v).1 + ∑ i, QW ((ψ v).2 i))
    (hQWnd : (QuadraticMap.polarBilin QW).Nondegenerate)
    (hWnt : Nontrivial W)
    (h0 : W ≃ₗ[K] W) (hh0 : h0 ∈ TauCeti.QuadraticMap.orthogonalGroup QW)
    (h0ord : orderOf h0 = p)
    (hxact : ∀ (i : Fin m) (w : W),
      x (ψ.symm (0, Pi.single i w)) = ψ.symm (0, Pi.single i (h0 w)))
    (hRmem : ∀ r : R, ψ.symm (r, 0) ∈ othersSpace x.toLinearMap h)
    (hWmem : ∀ w : Fin m → W, ψ.symm (0, w) ∈ orbitSpace x.toLinearMap h) :
    BlockDiagonalData (K := K) (V := V) Q x h := by
  classical
  haveI : Nontrivial W := hWnt
  have hmpos : 0 < m := by omega
  let i₀ : Fin m := ⟨0, hmpos⟩
  haveI hRfin : FiniteDimensional K R := by
    haveI : FiniteDimensional K (R × (Fin m → W)) := ψ.finiteDimensional
    exact FiniteDimensional.of_surjective (LinearMap.fst K R (Fin m → W))
      fun r => ⟨(r, 0), rfl⟩
  haveI hWfin : FiniteDimensional K (Fin m → W) := by
    haveI : FiniteDimensional K (R × (Fin m → W)) := ψ.finiteDimensional
    exact FiniteDimensional.of_surjective (LinearMap.snd K R (Fin m → W))
      fun w => ⟨(0, w), rfl⟩
  haveI : FiniteDimensional K W :=
    FiniteDimensional.of_surjective (LinearMap.proj i₀) fun w => ⟨fun _ => w, rfl⟩
  let Rpart : Submodule K V :=
    LinearMap.range (ψ.symm.toLinearMap.comp (LinearMap.inl K R (Fin m → W)))
  let Wpart : Submodule K V :=
    LinearMap.range (ψ.symm.toLinearMap.comp (LinearMap.inr K R (Fin m → W)))
  have hRsub : Rpart ≤ othersSpace x.toLinearMap h := by
    rintro v ⟨r, rfl⟩
    exact hRmem r
  have hWsub : Wpart ≤ orbitSpace x.toLinearMap h := by
    rintro v ⟨w, rfl⟩
    exact hWmem w
  have htop : Rpart ⊔ Wpart = ⊤ := by
    rw [eq_top_iff]
    intro v _
    have hsplit : ψ v = ((ψ v).1, (0 : Fin m → W)) + (0, (ψ v).2) := by ext <;> simp
    rw [← ψ.symm_apply_apply v, hsplit, map_add]
    refine Submodule.add_mem_sup ?_ ?_
    · exact ⟨(ψ v).1, rfl⟩
    · exact ⟨(ψ v).2, rfl⟩
  have hcompl := hx.isCompl_orbit_others hh
  have hdisjR : othersSpace x.toLinearMap h ⊓ Wpart = ⊥ := by
    rw [eq_bot_iff]
    intro v hv
    obtain ⟨hvO, hvW⟩ := Submodule.mem_inf.mp hv
    exact Submodule.disjoint_def.mp hcompl.disjoint v (hWsub hvW) hvO
  have hRpart_eq : Rpart = othersSpace x.toLinearMap h := by
    have hmod := sup_inf_assoc_of_le (x := Rpart) (y := Wpart)
      (z := othersSpace x.toLinearMap h) hRsub
    have hdisjR' : Wpart ⊓ othersSpace x.toLinearMap h = ⊥ := by
      rw [inf_comm, hdisjR]
    rw [htop, top_inf_eq, hdisjR', sup_bot_eq] at hmod
    exact hmod.symm
  have hxRpart : ∀ v ∈ Rpart, x v ∈ Rpart := by
    intro v hv
    rw [hRpart_eq] at hv ⊢
    refine mem_othersSpace_of_apply (g := x) ?_ hv
    rw [Subgroup.mem_centralizer_singleton_iff]
  let xR : R → R := fun r => Classical.choose (hxRpart (ψ.symm (r, 0)) ⟨r, rfl⟩)
  have hxR_spec (r : R) : x (ψ.symm (r, 0)) = ψ.symm (xR r, 0) :=
    (Classical.choose_spec (hxRpart (ψ.symm (r, 0)) ⟨r, rfl⟩)).symm
  have hpair_sum (w : Fin m → W) :
      ((0 : R), w) = ∑ i, ((0 : R), Pi.single i (w i)) := by
    ext j
    · have hfst : (∑ i, ((0 : R), Pi.single i (w i))).1 = ∑ i : Fin m, (0 : R) :=
        map_sum (LinearMap.fst K R (Fin m → W))
          (fun i => ((0 : R), Pi.single i (w i))) Finset.univ
      rw [hfst]
      simp
    · have hsnd : (∑ i, ((0 : R), Pi.single i (w i))).2 =
          ∑ i, Pi.single i (w i) :=
        map_sum (LinearMap.snd K R (Fin m → W))
          (fun i => ((0 : R), Pi.single i (w i))) Finset.univ
      rw [hsnd, Finset.univ_sum_single]
  have hxW : ∀ w : Fin m → W,
      x (ψ.symm (0, w)) = ψ.symm (0, fun i => h0 (w i)) := by
    intro w
    have hwsum : ψ.symm (0, w) = ∑ i, ψ.symm (0, Pi.single i (w i)) := by
      rw [← map_sum, hpair_sum]
    calc x (ψ.symm (0, w)) = x (∑ i, ψ.symm (0, Pi.single i (w i))) := by rw [hwsum]
      _ = ∑ i, x (ψ.symm (0, Pi.single i (w i))) := by rw [map_sum]
      _ = ∑ i, ψ.symm (0, Pi.single i (h0 (w i))) := by simp [hxact]
      _ = ψ.symm (0, fun i => h0 (w i)) := by
          rw [← map_sum, ← hpair_sum]
  have hsplit_model : ∀ (r : R) (w : Fin m → W),
      ψ.symm (r, w) = ψ.symm (r, 0) + ψ.symm (0, w) := by
    intro r w
    rw [← map_add]
    congr 1
    ext <;> simp
  have hx_apply_model : ∀ (r : R) (w : Fin m → W),
      x (ψ.symm (r, w)) = ψ.symm (xR r, fun i => h0 (w i)) := by
    intro r w
    rw [hsplit_model, map_add, hxR_spec, hxW, ← hsplit_model]
  let sUnit (c : Fin m → ℤˣ) (i : Fin m) : Kˣ :=
    Units.map (algebraMap ℤ K).toMonoidHom (c i)
  have hsUnit_apply (c : Fin m → ℤˣ) (i : Fin m) :
      (sUnit c i : K) = algebraMap ℤ K (c i : ℤ) := rfl
  let signAut : (Fin m → ℤˣ) →* (Fin m → (W ≃ₗ[K] W)) :=
    { toFun := fun c i => DistribMulAction.toModuleAut K W (sUnit c i)
      map_one' := by
        ext i
        simp [sUnit]
      map_mul' := by
        intro c d
        ext i
        simp [sUnit, Pi.mul_apply, mul_smul] }
  have hsignAut_apply (c : Fin m → ℤˣ) (i : Fin m) (w : W) :
      signAut c i w = (sUnit c i : K) • w := by
    change (sUnit c i : K) • w = (sUnit c i : K) • w
    rfl
  let Φ : (Fin m → ℤˣ) →* (V ≃ₗ[K] V) :=
    (CFSG.RankThree.CentralCover.coordAut ψ).comp
      ((CFSG.RankThree.CentralCover.piAut K W m).comp signAut)
  have hΦ_apply (c : Fin m → ℤˣ) (r : R) (w : Fin m → W) :
      Φ c (ψ.symm (r, w)) =
        ψ.symm (r, CFSG.RankThree.CentralCover.piAut K W m (signAut c) w) := by
    simp [Φ, CFSG.RankThree.CentralCover.coordAut_symm_apply]
  have hpiZero (c : Fin m → ℤˣ) :
      CFSG.RankThree.CentralCover.piAut K W m (signAut c) (0 : Fin m → W) = 0 :=
    map_zero _
  have hΦ_R (c : Fin m → ℤˣ) (r : R) : Φ c (ψ.symm (r, 0)) = ψ.symm (r, 0) := by
    rw [hΦ_apply, hpiZero]
  have hΦ_fix (c : Fin m → ℤˣ) : ∀ v ∈ othersSpace x.toLinearMap h, Φ c v = v := by
    intro v hv
    rw [← hRpart_eq] at hv
    obtain ⟨r, rfl⟩ := hv
    exact hΦ_R c r
  have hsignAut_mem (c : Fin m → ℤˣ) (i : Fin m) :
      signAut c i ∈ TauCeti.QuadraticMap.orthogonalGroup QW := by
    rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
    intro w
    rw [hsignAut_apply, QuadraticMap.map_smul]
    have hsq : (sUnit c i : K) * (sUnit c i : K) = 1 := by
      change algebraMap ℤ K (c i : ℤ) * algebraMap ℤ K (c i : ℤ) = 1
      rcases Int.units_eq_one_or (c i) with h | h <;> simp [h]
    rw [hsq, one_smul]
  have hΦO (c : Fin m → ℤˣ) : Φ c ∈ TauCeti.QuadraticMap.orthogonalGroup Q := by
    rw [show Φ c = CFSG.RankThree.CentralCover.coordAut ψ
        (CFSG.RankThree.CentralCover.piAut K W m (signAut c)) by rfl]
    exact CFSG.RankThree.CentralCover.coordAut_piAut_mem hQsum (hsignAut_mem c)
  have hΦ_comm (c : Fin m → ℤˣ) : Φ c * x = x * Φ c := by
    ext v
    obtain ⟨r, w, hvw⟩ : ∃ r w, ψ.symm (r, w) = v :=
      ⟨(ψ v).1, (ψ v).2, by simp⟩
    rw [← hvw]
    have hL : (Φ c * x) (ψ.symm (r, w)) =
        ψ.symm (xR r, CFSG.RankThree.CentralCover.piAut K W m (signAut c)
          (fun i => h0 (w i))) := by
      rw [LinearEquiv.mul_apply, hx_apply_model, hΦ_apply]
    have hR : (x * Φ c) (ψ.symm (r, w)) =
        ψ.symm (xR r, fun i =>
          h0 ((CFSG.RankThree.CentralCover.piAut K W m (signAut c) w) i)) := by
      rw [LinearEquiv.mul_apply, hΦ_apply, hx_apply_model]
    rw [hL, hR]
    congr 1
    refine Prod.ext rfl ?_
    ext i
    change CFSG.RankThree.CentralCover.piAut K W m (signAut c) (fun i => h0 (w i)) i =
      h0 (CFSG.RankThree.CentralCover.piAut K W m (signAut c) w i)
    rw [CFSG.RankThree.CentralCover.piAut_apply,
      CFSG.RankThree.CentralCover.piAut_apply, hsignAut_apply, hsignAut_apply, map_smul]
  have hΦ_supported (c : Fin m → ℤˣ) : Φ c ∈ supportedBlock Q x h := by
    refine mem_supportedBlock.mpr ⟨?_, hΦ_fix c⟩
    refine mem_isometryCentralizer.mpr ⟨fun v => ?_, fun v => ?_⟩
    · exact (TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp (hΦO c)) v
    · have := congrArg (fun e : V ≃ₗ[K] V => e v) (hΦ_comm c)
      simpa [LinearEquiv.mul_apply] using this
  let σOf (τ : Equiv.Perm (Fin m)) : V ≃ₗ[K] V :=
    CFSG.RankThree.CentralCover.coordAut ψ
      (CFSG.RankThree.CentralCover.permAut K W m τ)
  have hσOf_apply (τ : Equiv.Perm (Fin m)) (r : R) (w : Fin m → W) :
      σOf τ (ψ.symm (r, w)) =
        ψ.symm (r, CFSG.RankThree.CentralCover.permAut K W m τ w) := by
    simp [σOf, CFSG.RankThree.CentralCover.coordAut_symm_apply]
  have hσOf_inv (τ : Equiv.Perm (Fin m)) : (σOf τ)⁻¹ = σOf τ⁻¹ := by
    simp [σOf, map_inv]
  have hσOf_fix (τ : Equiv.Perm (Fin m)) :
      ∀ v ∈ othersSpace x.toLinearMap h, σOf τ v = v := by
    intro v hv
    rw [← hRpart_eq] at hv
    obtain ⟨r, rfl⟩ := hv
    change σOf τ (ψ.symm (r, 0)) = ψ.symm (r, 0)
    rw [hσOf_apply]
    congr 1
  have hσOf_comm (τ : Equiv.Perm (Fin m)) : σOf τ * x = x * σOf τ := by
    ext v
    obtain ⟨r, w, hvw⟩ : ∃ r w, ψ.symm (r, w) = v :=
      ⟨(ψ v).1, (ψ v).2, by simp⟩
    rw [← hvw]
    calc (σOf τ * x) (ψ.symm (r, w))
        = σOf τ (x (ψ.symm (r, w))) := rfl
      _ = σOf τ (ψ.symm (xR r, fun i => h0 (w i))) := by rw [hx_apply_model]
      _ = ψ.symm (xR r, CFSG.RankThree.CentralCover.permAut K W m τ
            (fun i => h0 (w i))) := by rw [hσOf_apply]
      _ = ψ.symm (xR r, fun i => h0 (CFSG.RankThree.CentralCover.permAut K W m τ w i)) := by
          congr 1
      _ = x (ψ.symm (r, CFSG.RankThree.CentralCover.permAut K W m τ w)) := by
          rw [hx_apply_model]
      _ = x (σOf τ (ψ.symm (r, w))) := by rw [hσOf_apply]
      _ = (x * σOf τ) (ψ.symm (r, w)) := rfl
  have hσOf_supported (τ : Equiv.Perm (Fin m)) : σOf τ ∈ supportedBlock Q x h := by
    refine mem_supportedBlock.mpr ⟨?_, hσOf_fix τ⟩
    refine mem_isometryCentralizer.mpr ⟨fun v => ?_, fun v => ?_⟩
    · exact (TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp
        (CFSG.RankThree.CentralCover.coordAut_permAut_mem hQsum τ)) v
    · have := congrArg (fun e : V ≃ₗ[K] V => e v) (hσOf_comm τ)
      simpa [LinearEquiv.mul_apply] using this
  have hσOf_conj (τ : Equiv.Perm (Fin m)) (c : Fin m → ℤˣ) :
      σOf τ * Φ c * (σOf τ)⁻¹ = Φ (fun k => c (τ.symm k)) := by
    calc σOf τ * Φ c * (σOf τ)⁻¹
        = CFSG.RankThree.CentralCover.coordAut ψ
            (CFSG.RankThree.CentralCover.permAut K W m τ *
              CFSG.RankThree.CentralCover.piAut K W m (signAut c) *
              (CFSG.RankThree.CentralCover.permAut K W m τ)⁻¹) := by
          simp [σOf, Φ, map_mul, map_inv]
      _ = CFSG.RankThree.CentralCover.coordAut ψ
            (CFSG.RankThree.CentralCover.piAut K W m
              (fun j => signAut c (τ.symm j))) := by
          rw [CFSG.RankThree.CentralCover.permAut_conj_piAut]
          rfl
      _ = Φ (fun k => c (τ.symm k)) := rfl

  have hσOf_conj_neg (i j : Fin m) (hij : i ≠ j) :
      σOf (Equiv.swap i j) * Φ (Pi.mulSingle i (-1)) * (σOf (Equiv.swap i j))⁻¹ =
        Φ (Pi.mulSingle j (-1)) := by
    rw [hσOf_conj]
    congr 1
    funext k
    by_cases hki : k = i
    · subst hki
      simp [Pi.mulSingle, hij, Ne.symm hij]
    by_cases hkj : k = j
    · subst hkj
      simp [Pi.mulSingle, hij]
    · have hswap_ne_i : Equiv.swap i j k ≠ i := by
        intro h
        have hk : k = j := by
          have := (Equiv.swap_apply_eq_iff).mp h
          simpa using this
        exact hkj hk
      have hswap_ne_j : Equiv.swap i j k ≠ j := by
        intro h
        have hk : k = i := by
          have := (Equiv.swap_apply_eq_iff).mp h
          simpa using this
        exact hki hk
      simp [Pi.mulSingle, hki, hkj, hswap_ne_i, hswap_ne_j]
  let negSign (i : Fin m) : Fin m → ℤˣ := Pi.mulSingle i (-1)
  let nAut (i : Fin m) : V ≃ₗ[K] V := Φ (negSign i)
  let signPair (i j : Fin m) : Fin m → ℤˣ := negSign i * negSign j
  let dAut (i j : Fin m) : V ≃ₗ[K] V := Φ (signPair i j)
  have hnAut_sq (i : Fin m) : nAut i * nAut i = 1 := by
    rw [show nAut i * nAut i = Φ (negSign i * negSign i) by
      simp [nAut, map_mul]]
    have hneg : negSign i * negSign i = 1 := by
      funext k
      simp [negSign, Pi.mulSingle]
    rw [hneg, map_one]
  have hσneg_conj (i j : Fin m) (hij : i ≠ j) :
      σOf (Equiv.swap i j) * nAut i * (σOf (Equiv.swap i j))⁻¹ = nAut j := by
    simpa [nAut, negSign] using hσOf_conj_neg i j hij
  have hdAut_supported (i j : Fin m) : dAut i j ∈ supportedBlock Q x h := by
    simpa [dAut, signPair] using hΦ_supported (signPair i j)
  have hdAut_blockDet (i j : Fin m) (hij : i ≠ j) :
      blockDet Q x h ⟨dAut i j, hdAut_supported i j⟩ = 1 := by
    have hd_eq : dAut i j = nAut i * nAut j := by
      simp [dAut, signPair, nAut, map_mul]
    have hni : nAut i ∈ supportedBlock Q x h := by
      simpa [nAut, negSign] using hΦ_supported (negSign i)
    have hnj : nAut j ∈ supportedBlock Q x h := by
      simpa [nAut, negSign] using hΦ_supported (negSign j)
    have hσ : σOf (Equiv.swap i j) ∈ supportedBlock Q x h := hσOf_supported _
    have hconj_supp : σOf (Equiv.swap i j) * nAut i * (σOf (Equiv.swap i j))⁻¹ ∈
        supportedBlock Q x h := by
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hσ hni) (Subgroup.inv_mem _ hσ)
    have hconj_det := blockDet_conj_eq (Q := Q) (x := x) (h := h)
      (g := nAut i) (k := σOf (Equiv.swap i j)) hni hσ hconj_supp
    have hconj_eq : (⟨σOf (Equiv.swap i j) * nAut i * (σOf (Equiv.swap i j))⁻¹,
        hconj_supp⟩ : ↥(supportedBlock Q x h)) =
        ⟨nAut j, hnj⟩ := by
      exact Subtype.ext (hσneg_conj i j hij)
    have hd_eq' : (⟨dAut i j, hdAut_supported i j⟩ : ↥(supportedBlock Q x h)) =
        ⟨nAut i, hni⟩ * ⟨nAut j, hnj⟩ := by
      exact Subtype.ext hd_eq
    rw [hd_eq', map_mul]
    have hni_eq_nj : blockDet Q x h ⟨nAut j, hnj⟩ = blockDet Q x h ⟨nAut i, hni⟩ := by
      rw [← hconj_eq]
      exact hconj_det
    rw [hni_eq_nj]
    have hsq : blockDet Q x h ⟨nAut i, hni⟩ * blockDet Q x h ⟨nAut i, hni⟩ =
        blockDet Q x h ⟨1, Subgroup.one_mem _⟩ := by
      have hprod : (⟨nAut i, hni⟩ * ⟨nAut i, hni⟩ : ↥(supportedBlock Q x h)) =
          ⟨1, Subgroup.one_mem _⟩ := by
        exact Subtype.ext (hnAut_sq i)
      rw [← map_mul, hprod]
    have h1 : blockDet Q x h ⟨1, Subgroup.one_mem _⟩ = 1 := map_one _
    rw [h1] at hsq
    exact hsq
  let E : Subgroup (V ≃ₗ[K] V) :=
    (⊤ : Subgroup (Fin m → ℤˣ)).map Φ ⊓ specialBlock Q x h
  have hsigns2 : IsPGroup 2 (⊤ : Subgroup (Fin m → ℤˣ)) := by
    apply IsPGroup.of_card (n := m)
    rw [Subgroup.card_top, Nat.card_pi]
    simp [Nat.card_eq_fintype_card, Fintype.card_units_int]
  have hΦrange2 : IsPGroup 2 ((⊤ : Subgroup (Fin m → ℤˣ)).map Φ) := hsigns2.map Φ
  have hE2 : IsPGroup 2 E :=
    hΦrange2.of_injective (Subgroup.inclusion inf_le_left)
      (Subgroup.inclusion_injective inf_le_left)
  have hEspec : E ≤ specialBlock Q x h := inf_le_right
  have hdAut_mem (i j : Fin m) (hij : i ≠ j) : dAut i j ∈ E := by
    refine ⟨?_, ?_⟩
    · exact Subgroup.mem_map.mpr ⟨signPair i j, Subgroup.mem_top _, rfl⟩
    · exact mem_specialBlock.mpr ⟨hdAut_supported i j, hdAut_blockDet i j hij⟩
  let P : Option (Fin m) → Submodule K V
    | none => Rpart
    | some i => LinearMap.range (ψ.symm.toLinearMap.comp
        ((LinearMap.inr K R (Fin m → W)).comp
          (LinearMap.single K (fun _ : Fin m => W) i)))
  let eR : R →ₗ[K] V :=
    ψ.symm.toLinearMap.comp (LinearMap.inl K R (Fin m → W))
  have heR_apply (r : R) : eR r = ψ.symm (r, 0) := rfl

  let slotMap (i : Fin m) : W →ₗ[K] V :=
    ψ.symm.toLinearMap.comp ((LinearMap.inr K R (Fin m → W)).comp
      (LinearMap.single K (fun _ : Fin m => W) i))
  have hP_some (i : Fin m) : P (some i) = LinearMap.range (slotMap i) := rfl
  have hslot_apply (i : Fin m) (w : W) : slotMap i w = ψ.symm (0, Pi.single i w) := rfl
  have hQ_slot (i : Fin m) (w : W) : Q (slotMap i w) = QW w := by
    rw [hslot_apply, hQsum]
    simp only [LinearEquiv.apply_symm_apply]
    have hsingle : (fun x : Fin m => QW ((Pi.single i w : Fin m → W) x)) =
        fun x => if x = i then QW w else 0 := by
      funext x
      by_cases hx : x = i <;> simp [Pi.single_apply, hx]
    rw [hsingle, Finset.sum_ite_eq']
    simp
  have hQ_R (r : R) : Q (eR r) = QR r := by
    rw [heR_apply, hQsum]
    simp
  have hslot_slot_orth (i j : Fin m) (hij : i ≠ j) (w w' : W) :
      polar Q (slotMap i w) (slotMap j w') = 0 := by
    have hsum : Q (slotMap i w + slotMap j w') = QW w + QW w' := by
      have hvec : slotMap i w + slotMap j w' =
          ψ.symm (0, Pi.single i w + Pi.single j w') := by
        rw [hslot_apply, hslot_apply, ← map_add]
        congr 1
        ext k <;> simp
      rw [hvec, hQsum]
      simp only [LinearEquiv.apply_symm_apply]
      have hfun : (fun x : Fin m =>
          QW ((Pi.single i w : Fin m → W) x + (Pi.single j w' : Fin m → W) x)) =
          fun x => (if x = i then QW w else 0) + (if x = j then QW w' else 0) := by
        funext x
        by_cases hxi : x = i <;> by_cases hxj : x = j <;>
          simp [Pi.single_apply, hxi, hxj, hij, Ne.symm hij]
      simp only [Pi.add_apply]
      rw [hfun, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq']
      simp
    have hmap := QuadraticMap.map_add Q (slotMap i w) (slotMap j w')
    rw [hQ_slot, hQ_slot, hsum] at hmap
    have h : QW w + QW w' + polar Q (slotMap i w) (slotMap j w') = QW w + QW w' + 0 := by
      simpa [add_assoc] using hmap
    exact add_left_cancel h
  have hslot_R_orth (i : Fin m) (w : W) (r : R) :
      polar Q (slotMap i w) (eR r) = 0 := by
    have hsum : Q (slotMap i w + eR r) = QW w + QR r := by
      have hvec : slotMap i w + eR r = ψ.symm (r, Pi.single i w) := by
        rw [hslot_apply, heR_apply, ← map_add]
        congr 1
        ext <;> simp
      rw [hvec, hQsum]
      simp only [LinearEquiv.apply_symm_apply]
      have hsingle : (fun x : Fin m => QW ((Pi.single i w : Fin m → W) x)) =
          fun x => if x = i then QW w else 0 := by
        funext x
        by_cases hx : x = i <;> simp [Pi.single_apply, hx]
      rw [hsingle, Finset.sum_ite_eq']
      simp [add_comm]
    have hmap := QuadraticMap.map_add Q (slotMap i w) (eR r)
    rw [hQ_slot, hQ_R, hsum] at hmap
    have h : QW w + QR r + polar Q (slotMap i w) (eR r) = QW w + QR r + 0 := by
      simpa [add_assoc] using hmap
    exact add_left_cancel h
  have hdecomp (v : V) : v = ψ.symm ((ψ v).1, 0) +
      ∑ i, ψ.symm (0, Pi.single i ((ψ v).2 i)) := by
    have hpair : ψ v = ((ψ v).1, 0) + (0, (ψ v).2) := by ext <;> simp
    have hsum : (0, (ψ v).2) = ∑ i, ((0 : R), Pi.single i ((ψ v).2 i)) :=
      hpair_sum ((ψ v).2)
    calc v = ψ.symm (ψ v) := (ψ.symm_apply_apply v).symm
      _ = ψ.symm (((ψ v).1, 0) + (0, (ψ v).2)) := by
          conv_lhs => rw [hpair]
      _ = ψ.symm (((ψ v).1, 0) + ∑ i, ((0 : R), Pi.single i ((ψ v).2 i))) := by
          conv_lhs => rw [hsum]
      _ = ψ.symm ((ψ v).1, 0) + ∑ i, ψ.symm (0, Pi.single i ((ψ v).2 i)) := by
          rw [map_add, map_sum]
  have hspan : (⨆ i : Option (Fin m), P i) = ⊤ := by
    rw [iSup_option, eq_top_iff]
    intro v _
    rw [hdecomp v]
    refine Submodule.add_mem_sup ?_ ?_
    · exact ⟨(ψ v).1, rfl⟩
    · refine Submodule.sum_mem _ fun i _ => ?_
      exact Submodule.mem_iSup_of_mem (p := fun i : Fin m => P (some i)) i
        ⟨(ψ v).2 i, rfl⟩
  have hxP : ∀ i, ∀ v ∈ P i, x v ∈ P i := by
    intro i v hv
    cases i with
    | none => exact hxRpart v hv
    | some i =>
        change v ∈ LinearMap.range (ψ.symm.toLinearMap.comp
          ((LinearMap.inr K R (Fin m → W)).comp
            (LinearMap.single K (fun _ : Fin m => W) i))) at hv
        obtain ⟨w, rfl⟩ := hv
        refine ⟨h0 w, ?_⟩
        change ψ.symm (0, Pi.single i (h0 w)) =
          x (ψ.symm (0, Pi.single i w))
        rw [hxact]
  have hsignPair_i (i j : Fin m) (hij : i ≠ j) : signPair i j i = -1 := by
    simp [signPair, negSign, Pi.mulSingle, hij]
  have hsignPair_j (i j : Fin m) (hij : i ≠ j) : signPair i j j = -1 := by
    simp [signPair, negSign, Pi.mulSingle, hij, Ne.symm hij]
  have hsignPair_other (i j k : Fin m) (hki : k ≠ i) (hkj : k ≠ j) :
      signPair i j k = 1 := by
    simp [signPair, negSign, Pi.mulSingle, hki, hkj]
  have hdAut_apply (i j : Fin m) (r : R) (w : Fin m → W) :
      dAut i j (ψ.symm (r, w)) =
        ψ.symm (r, CFSG.RankThree.CentralCover.piAut K W m
          (signAut (signPair i j)) w) := by
    simpa [dAut] using hΦ_apply (signPair i j) r w
  have hdAut_R (i j : Fin m) (r : R) : dAut i j (ψ.symm (r, 0)) = ψ.symm (r, 0) := by
    rw [hdAut_apply, hpiZero]
  have hdAut_single (i j : Fin m) (hij : i ≠ j) (w : W) :
      dAut i j (ψ.symm (0, Pi.single i w)) = -ψ.symm (0, Pi.single i w) := by
    rw [hdAut_apply, ← map_neg]
    congr 1
    refine Prod.ext ?_ ?_
    · simp
    · ext k
      change CFSG.RankThree.CentralCover.piAut K W m (signAut (signPair i j))
        (Pi.single i w) k = (-(Pi.single i w : Fin m → W)) k
      rw [CFSG.RankThree.CentralCover.piAut_apply, hsignAut_apply]
      by_cases hk : k = i
      · rw [hk, hsUnit_apply, hsignPair_i i j hij]
        simp
      · simp [Pi.single_apply, hk]
  have hmem_R_iff (v : V) : v ∈ Rpart ↔ ∀ i j : Fin m, i ≠ j → dAut i j v = v := by
    constructor
    · intro hv i j hij
      obtain ⟨r, rfl⟩ := hv
      exact hdAut_R i j r
    · intro hv
      let r : R := (ψ v).1
      let w : Fin m → W := (ψ v).2
      have hw : w = 0 := by
        funext k
        obtain ⟨j, hjk⟩ : ∃ j : Fin m, j ≠ k := by
          obtain ⟨j, hj⟩ := Fin.exists_ne_and_ne_of_two_lt (i := k) (j := k)
            (by omega : 2 < m)
          exact ⟨j, hj.1⟩
        have hfix := hv k j hjk.symm
        have hcoord := congrArg (fun e : V => (ψ e).2 k) hfix
        have hdval : (ψ (dAut k j v)).2 k = -w k := by
          rw [show v = ψ.symm (r, w) by simp [r, w]]
          rw [hdAut_apply]
          simp [CFSG.RankThree.CentralCover.piAut_apply, hsignAut_apply,
            hsUnit_apply, hsignPair_i k j hjk.symm]
        rw [hdval] at hcoord
        exact CFSG.Quasithin.H13.L1293S.eq_zero_of_eq_neg h2 (by simpa using hcoord.symm)
      rw [show v = ψ.symm (r, 0) by
        rw [← ψ.symm_apply_apply v]
        congr 1
        ext <;> simp [r, w, hw]]
      exact ⟨r, rfl⟩
  have hmem_slot_iff (i : Fin m) (v : V) :
      v ∈ P (some i) ↔ ∀ j : Fin m, j ≠ i → dAut i j v = -v := by
    constructor
    · intro hv j hji
      change v ∈ LinearMap.range (ψ.symm.toLinearMap.comp
        ((LinearMap.inr K R (Fin m → W)).comp
          (LinearMap.single K (fun _ : Fin m => W) i))) at hv
      obtain ⟨w, rfl⟩ := hv
      exact hdAut_single i j hji.symm w
    · intro hv
      let r : R := (ψ v).1
      let w : Fin m → W := (ψ v).2
      obtain ⟨j, hji⟩ : ∃ j : Fin m, j ≠ i := by
        obtain ⟨j, hj⟩ := Fin.exists_ne_and_ne_of_two_lt (i := i) (j := i)
          (by omega : 2 < m)
        exact ⟨j, hj.1⟩
      have hrzero : r = 0 := by
        have hfix := hv j hji
        have hcoord := congrArg (fun e : V => (ψ e).1) hfix
        have hdval : (ψ (dAut i j v)).1 = r := by
          rw [show v = ψ.symm (r, w) by simp [r, w]]
          rw [hdAut_apply]
          simp
        have hneg : (ψ (-v)).1 = -r := by simp [r]
        rw [hdval, hneg] at hcoord
        exact CFSG.Quasithin.H13.L1293S.eq_zero_of_eq_neg h2 (by simpa using hcoord)
      have hwzero : ∀ l : Fin m, l ≠ i → w l = 0 := by
        intro l hli
        obtain ⟨j', hj'i, hj'l⟩ := Fin.exists_ne_and_ne_of_two_lt (i := i) (j := l)
          (by omega : 2 < m)
        have hfix := hv j' hj'i
        have hcoord := congrArg (fun e : V => (ψ e).2 l) hfix
        have hdval : (ψ (dAut i j' v)).2 l = w l := by
          rw [show v = ψ.symm (r, w) by simp [r, w]]
          rw [hdAut_apply]
          simp [CFSG.RankThree.CentralCover.piAut_apply, hsignAut_apply,
            hsUnit_apply, hsignPair_other i j' l hli hj'l.symm]
        have hneg : (ψ (-v)).2 l = -w l := by simp [w]
        rw [hdval, hneg] at hcoord
        exact CFSG.Quasithin.H13.L1293S.eq_zero_of_eq_neg h2 (by simpa using hcoord)
      have hw' : Pi.single i (w i) = w := by
        funext l
        by_cases hli : l = i
        · subst hli; simp
        · simp [Pi.single_apply, hli, hwzero l hli]
      rw [show v = ψ.symm (0, Pi.single i (w i)) by
        rw [← ψ.symm_apply_apply v]
        congr 1
        ext
        · simp [r, hrzero]
        · simp [w, hw']]
      exact ⟨w i, rfl⟩
  have hpres : ∀ (S' : Subgroup (V ≃ₗ[K] V)),
      (∀ s' ∈ S', ∀ e ∈ E, s' * e = e * s') →
      ∀ s' ∈ S', ∀ i, ∀ v ∈ P i, s' v ∈ P i := by
    intro S' hcent s' hs' i
    cases i with
    | none =>
        intro v hv
        rw [hmem_R_iff] at hv ⊢
        intro i j hij
        have hcomm : dAut i j (s' v) = s' (dAut i j v) := by
          have := congrArg (fun e : V ≃ₗ[K] V => e v) (hcent s' hs' _ (hdAut_mem i j hij))
          simpa [LinearEquiv.mul_apply] using this.symm
        rw [hcomm, hv i j hij]
    | some i =>
        intro v hv
        rw [hmem_slot_iff i v] at hv
        rw [hmem_slot_iff i (s' v)]
        intro j hji
        have hcomm : dAut i j (s' v) = s' (dAut i j v) := by
          have := congrArg (fun e : V ≃ₗ[K] V => e v) (hcent s' hs' _ (hdAut_mem i j hji.symm))
          simpa [LinearEquiv.mul_apply] using this.symm
        rw [hcomm, hv j hji, map_neg]
  have hdim_eq : Module.finrank K V = Module.finrank K R + m * Module.finrank K W := by
    rw [LinearEquiv.finrank_eq ψ, Module.finrank_prod, Module.finrank_pi_fintype]
    simp [Finset.card_fin, mul_comm]
  have hWpos : 0 < Module.finrank K W := finrank_pos_iff.mpr inferInstance
  have hWle2 : Module.finrank K W ≤ 2 := by
    have hmul : m * Module.finrank K W ≤ 8 := by
      rw [hdim_eq] at hdim
      omega
    have h3 : 3 * Module.finrank K W ≤ m * Module.finrank K W :=
      Nat.mul_le_mul_right _ hm
    omega
  have hWne1 : Module.finrank K W ≠ 1 := by
    intro hW1
    have hodd0 : Odd (orderOf h0) := by
      rw [h0ord]
      exact hp.odd_of_ne_two hp2
    have hdet0 : LinearEquiv.det h0 = 1 :=
      CFSG.ClassicalInvolution.Q3.det_eq_one_of_odd_orderOf h2 hQWnd hh0 hodd0
    have h0id : h0 = 1 := by
      let γ : LinearMap.GeneralLinearGroup K W :=
        LinearMap.GeneralLinearGroup.ofLinearEquiv h0
      have hγdet : LinearMap.det (γ : Module.End K W) = 1 := by
        change LinearMap.det ((h0 : W ≃ₗ[K] W) : Module.End K W) = 1
        rw [← LinearEquiv.coe_det, hdet0]
        rfl
      have hγ1 : γ = 1 :=
        CFSG.RankThree.PartOne.KCSpIsotypic.eq_one_of_det_eq_one_of_finrank_le_one
          (le_of_eq hW1) γ hγdet
      have hEnd : (γ : Module.End K W) = 1 :=
        congrArg (fun g : LinearMap.GeneralLinearGroup K W =>
          (g : Module.End K W)) hγ1
      ext w
      have := congrArg (fun e : Module.End K W => e w) hEnd
      simpa [γ] using this
    have : orderOf h0 = 1 := by simp [h0id]
    rw [h0ord] at this
    exact hp.ne_one this
  have hW2 : Module.finrank K W = 2 := by omega
  have hRle2 : Module.finrank K R ≤ 2 := by
    rw [hdim_eq, hW2] at hdim
    have hm2 : 6 ≤ m * 2 := by omega
    omega
  have hpolar_comp_Rpart (x y : Rpart) :
      polar (Q.comp Rpart.subtype) x y = polar Q (x : V) (y : V) := by
    simp [QuadraticMap.polar, map_add, map_sub]
  have heR_inj : Function.Injective eR := by
    intro r₁ r₂ h
    have := congrArg ψ h
    simpa [eR] using this
  have hRpart_nd : (QuadraticMap.polarBilin (Q.comp Rpart.subtype)).Nondegenerate := by
    constructor
    · intro u hu
      have hz : (u : V) = 0 := by
        refine hQ.1 (u : V) fun v => ?_
        have hv : v ∈ Rpart ⊔ Wpart := by rw [htop]; trivial
        obtain ⟨p, hp, w, hw, rfl⟩ := Submodule.mem_sup.mp hv
        have h1 : polar Q (u : V) p = 0 := by
          have := hu ⟨p, hp⟩
          simpa [hpolar_comp_Rpart, QuadraticMap.polarBilin_apply_apply] using this
        have h2 : polar Q (u : V) w = 0 := by
          rw [QuadraticMap.polar_comm]
          exact hx.polar_orbit_others hh (hWsub hw) (hRsub u.2)
        rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_add_right, h1, h2, add_zero]
      exact Subtype.ext hz
    · intro u hu
      have hz : (u : V) = 0 := by
        refine hQ.2 (u : V) fun v => ?_
        have hv : v ∈ Rpart ⊔ Wpart := by rw [htop]; trivial
        obtain ⟨p, hp, w, hw, rfl⟩ := Submodule.mem_sup.mp hv
        have h1 : polar Q p (u : V) = 0 := by
          have := hu ⟨p, hp⟩
          simpa [hpolar_comp_Rpart, QuadraticMap.polarBilin_apply_apply] using this
        have h2 : polar Q w (u : V) = 0 :=
          hx.polar_orbit_others hh (hWsub hw) (hRsub u.2)
        rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_add_left, h1, h2, add_zero]
      exact Subtype.ext hz
  let C (i : Fin m) : Submodule K V :=
    Rpart ⊔ ⨆ j : {j : Fin m // j ≠ i}, P (some j.1)
  have hslot_sup (i : Fin m) : P (some i) ⊔ C i = ⊤ := by
    rw [eq_top_iff]
    intro v _
    let r : R := (ψ v).1
    let w : Fin m → W := (ψ v).2
    have hsum_split : (∑ j : Fin m, ψ.symm (0, Pi.single j (w j))) =
        ψ.symm (0, Pi.single i (w i)) +
          ∑ j ∈ Finset.univ.erase i, ψ.symm (0, Pi.single j (w j)) := by
      rw [Finset.add_sum_erase Finset.univ (fun j => ψ.symm (0, Pi.single j (w j)))
        (Finset.mem_univ i)]
    have hv : v = ψ.symm (0, Pi.single i (w i)) +
        (eR r + ∑ j ∈ Finset.univ.erase i, ψ.symm (0, Pi.single j (w j))) := by
      rw [hdecomp v, hsum_split]
      simp only [eR, heR_apply, LinearMap.comp_apply, LinearMap.inl_apply]
      abel
    rw [hv]
    refine Submodule.add_mem_sup ?_ ?_
    · exact ⟨w i, rfl⟩
    · refine Submodule.add_mem_sup ?_ ?_
      · exact ⟨r, rfl⟩
      · refine Submodule.sum_mem _ fun j hj => ?_
        have hji : j ≠ i := (Finset.mem_erase.mp hj).1
        exact Submodule.mem_iSup_of_mem
          (p := fun j : {j : Fin m // j ≠ i} => P (some j.1)) ⟨j, hji⟩ ⟨w j, rfl⟩
  have horth_C (i : Fin m) (w : W) (c : V) (hc : c ∈ C i) :
      polar Q (slotMap i w) c = 0 := by
    obtain ⟨p, hp, s, hs, rfl⟩ := Submodule.mem_sup.mp hc
    obtain ⟨r, rfl⟩ := hp
    have hp0 : polar Q (slotMap i w) (eR r) = 0 := hslot_R_orth i w r
    have hs0 : polar Q (slotMap i w) s = 0 := by
      refine Submodule.iSup_induction _
        (motive := fun s => polar Q (slotMap i w) s = 0) hs ?_ (by simp)
        (fun a b ha hb => by rw [QuadraticMap.polar_add_right, ha, hb, add_zero])
      intro j s hs
      obtain ⟨w', rfl⟩ := hs
      exact hslot_slot_orth i j.1 j.2.symm w w'
    rw [QuadraticMap.polar_add_right, hp0, hs0, add_zero]
  have hslot_inj (i : Fin m) : Function.Injective (slotMap i) := by
    intro w w' h
    have := congrArg (fun v : V => (ψ v).2 i) h
    simpa [slotMap, Pi.single_eq_same] using this
  have hslot_nd (i : Fin m) :
      (QuadraticMap.polarBilin (Q.comp (P (some i)).subtype)).Nondegenerate := by
    have hPn : CFSG.ClassicalGroups.Orthogonal.PolarNondegOn Q (P (some i)) := by
      intro u hu huo
      obtain ⟨w, rfl⟩ := hu
      have hz : slotMap i w = 0 := by
        refine hQ.1 (slotMap i w) fun v => ?_
        have hv : v ∈ P (some i) ⊔ C i := by rw [hslot_sup i]; trivial
        obtain ⟨p, hp, c, hc, rfl⟩ := Submodule.mem_sup.mp hv
        have h1 : polar Q (slotMap i w) p = 0 := by
          have := huo p hp
          simpa [slotMap, QuadraticMap.polarBilin_apply_apply] using this
        have h2 : polar Q (slotMap i w) c = 0 := horth_C i w c hc
        rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_add_right, h1, h2, add_zero]
      exact hz
    have hres := CFSG.ClassicalGroups.Orthogonal.nondegenerate_polarBilin_restrict hPn
    convert hres using 1
    rfl
  have hslot_finrank (i : Fin m) : Module.finrank K (P (some i)) = 2 := by
    rw [hP_some i, LinearMap.finrank_range_of_inj (hslot_inj i), hW2]
  have hRpart_finrank : Module.finrank K Rpart = Module.finrank K R := by
    rw [← (show LinearMap.range eR = Rpart from rfl),
      LinearMap.finrank_range_of_inj heR_inj]
  have hdet_restrict (P' : Submodule K V) (hP' : ∀ v ∈ P', x v ∈ P')
      (hnd : (QuadraticMap.polarBilin (Q.comp P'.subtype)).Nondegenerate) :
      LinearEquiv.det
        (restrictEquiv P' x hP'
          (CFSG.SeitzReduction.OmegaPilot.symm_mem_of_mapsTo hP')) = 1 := by
    have horth :
        restrictEquiv P' x hP'
          (CFSG.SeitzReduction.OmegaPilot.symm_mem_of_mapsTo hP') ∈
        TauCeti.QuadraticMap.orthogonalGroup (Q.comp P'.subtype) :=
      CFSG.LinearAlgebra.restrictEquiv_mem_orthogonalGroup hx.mem hP'
        (CFSG.SeitzReduction.OmegaPilot.symm_mem_of_mapsTo hP')
    have hpow :
        (restrictEquiv P' x hP'
          (CFSG.SeitzReduction.OmegaPilot.symm_mem_of_mapsTo hP')) ^ p = 1 := by
      ext v
      rw [CFSG.LinearAlgebra.restrictEquiv_pow_apply]
      simpa using congrArg (fun e : V ≃ₗ[K] V => e (v : V)) hx.pow_eq_one
    have hodd : Odd (orderOf
        (restrictEquiv P' x hP'
          (CFSG.SeitzReduction.OmegaPilot.symm_mem_of_mapsTo hP'))) :=
      Odd.of_dvd_nat (hp.odd_of_ne_two hp2) (orderOf_dvd_iff_pow_eq_one.mpr hpow)
    exact CFSG.ClassicalInvolution.Q3.det_eq_one_of_odd_orderOf h2 hnd horth hodd
  have hxR_orth :
      restrictEquiv Rpart x hxRpart
        (CFSG.SeitzReduction.OmegaPilot.symm_mem_of_mapsTo hxRpart) ∈
      TauCeti.QuadraticMap.orthogonalGroup (Q.comp Rpart.subtype) :=
    CFSG.LinearAlgebra.restrictEquiv_mem_orthogonalGroup hx.mem hxRpart
      (CFSG.SeitzReduction.OmegaPilot.symm_mem_of_mapsTo hxRpart)
  have hxR_det : LinearEquiv.det
      (restrictEquiv Rpart x hxRpart
        (CFSG.SeitzReduction.OmegaPilot.symm_mem_of_mapsTo hxRpart)) = 1 :=
    hdet_restrict Rpart hxRpart hRpart_nd
  have hplane : ∀ i, (∀ v ∈ P i, x v = v) ∨
      ∃ xP : P i ≃ₗ[K] P i, (∀ v, (xP v : V) = x v) ∧
        (QuadraticMap.polarBilin (Q.comp (P i).subtype)).Nondegenerate ∧
        Module.finrank K (P i) = 2 ∧ LinearEquiv.det xP = 1 := by
    intro i
    cases i with
    | none =>
        by_cases hR2 : Module.finrank K R = 2
        · right
          refine ⟨restrictEquiv Rpart x hxRpart
              (CFSG.SeitzReduction.OmegaPilot.symm_mem_of_mapsTo hxRpart), fun v => rfl,
            hRpart_nd, ?_, hxR_det⟩
          rw [show P none = Rpart from rfl, hRpart_finrank, hR2]
        · left
          have hRle1 : Module.finrank K R ≤ 1 := by omega
          have hRpart_le1 : Module.finrank K Rpart ≤ 1 := by
            rw [hRpart_finrank]
            exact hRle1
          have hxRid : restrictEquiv Rpart x hxRpart
              (CFSG.SeitzReduction.OmegaPilot.symm_mem_of_mapsTo hxRpart) = 1 := by
            let γ : LinearMap.GeneralLinearGroup K Rpart :=
              LinearMap.GeneralLinearGroup.ofLinearEquiv
                (restrictEquiv Rpart x hxRpart
                  (CFSG.SeitzReduction.OmegaPilot.symm_mem_of_mapsTo hxRpart))
            have hγdet : LinearMap.det (γ : Module.End K Rpart) = 1 := by
              change LinearMap.det
                ((restrictEquiv Rpart x hxRpart
                  (CFSG.SeitzReduction.OmegaPilot.symm_mem_of_mapsTo hxRpart) :
                  Rpart ≃ₗ[K] Rpart) : Module.End K Rpart) = 1
              rw [← LinearEquiv.coe_det, hxR_det]
              rfl
            have hγ1 : γ = 1 :=
              CFSG.RankThree.PartOne.KCSpIsotypic.eq_one_of_det_eq_one_of_finrank_le_one
                hRpart_le1 γ hγdet
            have hEnd : (γ : Module.End K Rpart) = 1 :=
              congrArg (fun g : LinearMap.GeneralLinearGroup K Rpart =>
                (g : Module.End K Rpart)) hγ1
            ext v
            have := congrArg (fun e : Module.End K Rpart => e v) hEnd
            exact congrArg (fun w : Rpart => (w : V)) (by simpa [γ] using this)
          intro v hv
          have := congrArg (fun e : Rpart ≃ₗ[K] Rpart =>
            (e ⟨v, hv⟩ : V)) hxRid
          simpa using this
    | some i =>
        right
        refine ⟨restrictEquiv (P (some i)) x (hxP (some i))
            (CFSG.SeitzReduction.OmegaPilot.symm_mem_of_mapsTo (hxP (some i))),
          fun v => rfl, hslot_nd i, hslot_finrank i, ?_⟩
        exact hdet_restrict (P (some i)) (hxP (some i)) (hslot_nd i)
  exact ⟨E, hE2, hEspec, Option (Fin m), inferInstance, P, hspan, hxP, hplane, hpres⟩

theorem blockDiagonalData_of_three_le
    (hx : OddOrderIsometry Q p x) (hp : p.Prime) (hp2 : p ≠ 2) (h2 : (2 : K) ≠ 0)
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hdim : Module.finrank K V ≤ 8)
    {h : K[X]} (hh : h ∈ primaryFactors x.toLinearMap) (hne1 : h ≠ X - 1)
    (hm : 3 ≤ primaryMultiplicity x.toLinearMap h) :
    BlockDiagonalData (K := K) (V := V) Q x h := by
  classical
  by_cases hself : h = reciprocalPolynomial h
  · obtain ⟨R, W, instR, instMR, instW, instMW, QR, QW, ψ, hQsum, hQWnd, hWnt,
      ⟨h0, hh0, h0ord, hxact⟩, hRmem, hWmem⟩ :=
      hx.repeatedSummands_selfDual hp hp2 hh hne1 hself
    letI : AddCommGroup R := instR
    letI : Module K R := instMR
    letI : AddCommGroup W := instW
    letI : Module K W := instMW
    exact blockDiagonalData_of_repeated hx hp hp2 h2 hQ hdim hh hm
      (m := primaryMultiplicity x.toLinearMap h) QR QW ψ hQsum hQWnd hWnt
      h0 hh0 h0ord hxact hRmem hWmem
  · obtain ⟨R, W, instR, instMR, instW, instMW, QR, QW, ψ, hQsum, hQWnd, hWnt,
      ⟨h0, hh0, h0ord, hxact⟩, hRmem, hWmem⟩ :=
      hx.repeatedSummands_paired hp hh hne1 hself
    letI : AddCommGroup R := instR
    letI : Module K R := instMR
    letI : AddCommGroup W := instW
    letI : Module K W := instMW
    exact blockDiagonalData_of_repeated hx hp hp2 h2 hQ hdim hh hm
      (m := primaryMultiplicity x.toLinearMap h) QR QW ψ hQsum hQWnd hWnt
      h0 hh0 h0ord hxact hRmem hWmem

theorem commute_of_specialBlock_of_three_le
    (hx : OddOrderIsometry Q p x) (hp : p.Prime) (hp2 : p ≠ 2) (h2 : (2 : K) ≠ 0)
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hdim : Module.finrank K V ≤ 8)
    {h : K[X]} (hh : h ∈ primaryFactors x.toLinearMap) (hne1 : h ≠ X - 1)
    (hm : 3 ≤ primaryMultiplicity x.toLinearMap h)
    {T : Subgroup (V ≃ₗ[K] V)} (hT : T ≤ specialBlock Q x h) (hT2 : IsPGroup 2 T)
    (hTodd : ¬ 2 ∣ (T.subgroupOf (specialBlock Q x h)).index)
    {S : Subgroup (V ≃ₗ[K] V)} (hS2 : IsPGroup 2 S) (hSQ : ∀ s ∈ S, ∀ v, Q (s v) = Q v)
    (hxS : x ∈ Subgroup.normalizer (S : Set (V ≃ₗ[K] V)))
    (hST : ∀ s ∈ S, ∀ t ∈ T, s * t = t * s) :
    ∀ s ∈ S, s * x = x * s := by
  have hpodd : Odd p := hp.odd_of_ne_two hp2
  have hdata := blockDiagonalData_of_three_le hx hp hp2 h2 hQ hdim hh hne1 hm
  obtain ⟨E, hE2, hEspec, ι, hFintype, P, hspan, hxP, hplane, hpres⟩ := hdata
  letI : Fintype ι := hFintype
  exact finish h2 hpodd hx.mem hx.pow_eq_one hE2 hEspec hT hT2 hTodd P hspan hxP hplane hpres
    hS2 hSQ hxS hST

end CFSG.LocalAnalysis.GLTheoremA.I2020

end
