module

public import CFSG.GH74.GLS.LU.Local.A3InputsGH
public import CFSG.GH74.GLS.LU.Local.FiveBundles
public import CFSG.GH74.GLS.LU.Local.FiveSetup
public import CFSG.GH74.GLS.LU.Local.Torus8
public import CFSG.GH74.GLS.LU.Local.L3InvAll
public import CFSG.GH74.GLS.IVK.Proofs2.Lemma44a
public import CFSG.GH74.GLS.LU.Local.Assembly
public import Certificates.Kernel.ThCent.Leaves
public import CFSG.Certificates.WordSubgroupRel
public import CFSG.CharacterTheory.Blocks.Defs
public import CFSG.GH74.GLS.IVK.L2.F1
public import CFSG.GH74.GLS.LU.Local.L3Cover
public import CFSG.GH74.GLS.Stage1.Main.Bridge
public import CFSG.GH74.GLS.Stage2.Final.ModelFam
public import CFSG.GH74.GLS.Stage2.Final.ModelLayerBar
public import CFSG.GH74.GLS.Stage2.Final.Named
public import CFSG.GH74.GLS.Stage2.Final.Thm4.Core
public import CFSG.GH74.GLS.Stage2.Local.Statements
public import CFSG.GH74.L5U5.ModelsBridge
public import CFSG.GroupTheory.Fitting.CoprimeAutomorphisms
public import CFSG.LieType.Chevalley.RootCommutatorData
public import CFSG.LieType.Multipliers.ProductKernel
public import CFSG.LieType.Multipliers.U42Bridge
public import CFSG.LieType.Multipliers.U43Action
public import CFSG.LieType.Multipliers.U43BridgeInputs
public import CFSG.LieType.Multipliers.U62Action
public import CFSG.LieType.Multipliers.U62Bridge
public import CFSG.LieType.Multipliers.U62Kernel
public import CFSG.LieType.Universal.SpinOmega.Kernel
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalDescentEndpoint
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFiveStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareField
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixComponentsCover
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixModelGeometry
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalTraceZeroCoordinates
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBProjectiveInvolutionStructure
public import CFSG.LocalAnalysis.ComponentClassification.StandardRecognitionQuaternion
public import CFSG.LocalAnalysis.ComponentClassification.TBLitCover
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedGSCSemidihedralKernel
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedLayerOddCoreUnbalancingTriple
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherAutomorphismData
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeCheckBase
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeModel
public import CFSG.LocalAnalysis.EvenSmallLie.Sp6JCondition
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.StrongEmbedding
public import CFSG.LocalAnalysis.SectionRank.Sporadic.TitsGen
public import CFSG.Monster.B.Classical.PlaneAut
public import CFSG.Monster.B.TwoA.Amalgam.Data
public import CFSG.Monster.B.TwoA.Sp8.Par1
public import CFSG.Monster.B.TwoA.Unitary.LinThree
public import CFSG.Sporadic.Presentation.Common
public import CFSG.Sporadic.SmallOddCore.CheckSpec
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldFixedSubfieldCard
public import CFSG.Walter.J1
public import CFSG.YGroups.Y322Central
public import Certificates.Certificate1
public import Certificates.Certificate10005
public import Certificates.Certificate10006
public import Certificates.Certificate10007
public import Certificates.Certificate10008
public import Certificates.Certificate10009
public import Certificates.Certificate10010
public import Certificates.Certificate10012
public import Certificates.Certificate10013
public import Certificates.Certificate10014
public import Certificates.Certificate10016
public import Certificates.Certificate10018
public import Certificates.Certificate12041
public import Certificates.Certificate12042
public import Certificates.Certificate12043
public import Certificates.Certificate12044
public import Certificates.Certificate12045
public import Certificates.Certificate12046
public import Certificates.Certificate16015
public import Certificates.Certificate16040
public import Certificates.Certificate2
public import Certificates.Certificate2154
public import Certificates.Certificate2157
public import Certificates.Certificate2267
public import Certificates.Certificate2326
public import Certificates.Certificate3006
public import Certificates.Certificate3007
public import Certificates.Certificate3008
public import Certificates.Certificate3063
public import Certificates.Certificate3077
public import Certificates.Certificate3082
public import Certificates.Certificate3083
public import Certificates.Certificate3951
public import Certificates.Certificate8033
public import Certificates.Certificate9130
public import TauCeti.LinearAlgebra.CliffordAlgebra.Monomials
public import TauCeti.LinearAlgebra.Dimension.IsQuadraticExtension
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalBasis

public section

open Subgroup CFSG CFSG.GH74 CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.GH74.GLS CFSG.GH74.GLS.LU
  CFSG.LieType.Universal.Unitary
open scoped MatrixGroups

namespace CFSG.GH74.GLS.LU.Local

open CFSG.GH74.GLS.IVK

@[expose] def LUA3Five'_gh : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsKProperSimple G → KGH G → ∀ p f : ℕ, p.Prime → p ≠ 2 →
    5 ≤ p ^ f → p ^ f = 5 → ∀ (z : G) (S : Sylow 2 G) (K₁ K₂ : Subgroup G) (t u : G),
      A3Hyp G p f z S K₁ K₂ t u → LUEps G (p ^ f) 1 z K₁ u → FiveExtra G z S →
        A3CoreLin G p f z K₁ K₂ u

theorem LUA3Five'_gh_of (h : LUA3Five') : LUA3Five'_gh :=
  fun G _ _ hG _ => h G hG

@[expose] def LUA3Leaf'_gh : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsKProperSimple G → KGH G → ∀ p f : ℕ, p.Prime → p ≠ 2 → 5 ≤ p ^ f →
    ∀ (z : G) (S : Sylow 2 G) (K₁ K₂ : Subgroup G) (t u : G), LUComps G (p ^ f) z K₁ K₂ →
      LUSyl G z S K₁ K₂ t u → MaxOverCentralizerPSp4 z p f → LU61 G z S K₁ K₂ t u →
      (∀ c ∈ Cz z, ∃ a ∈ A0 z, ∃ k ∈ K₁ ⊔ K₂, ∃ s ∈ (S : Subgroup G),
        ∃ y ∈ Fstar (S : Subgroup G) K₁ K₂ u, c = a * k * s * y) →
      (LUEps G (p ^ f) 1 z K₁ u → (p ^ f = 5 → FiveExtra G z S) →
        ∃ (K : Type) (_ : Field K) (_ : Finite K) (u' : G) (Y : Fin 3 → Subgroup G) (h : G),
          Nat.card K = p ^ f ∧ (u' = u ∨ u' = u * z) ∧ Y 0 = K₁ ∧ Y 2 = K₂ ∧ h⁻¹ * z * h = u' ∧
          (Y 1 = cj K₁ h ∨ Y 1 = cj K₂ h) ∧ IsLinearA3Neighborhood K z u' Y ∧
          ∃ T : Subgroup G, T ≤ (⨆ i, Y i : Subgroup G) ⊓ Cz z ∧ IsPGroup 2 T ∧
            Nat.card (S : Subgroup G) ≤ Nat.card T) ∧
      (LUEps G (p ^ f) (-1) z K₁ u →
        ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K p) (F : Type) (_ : Field F)
          (_ : Finite F) (u' : G) (Y : Fin 3 → Subgroup G) (h : G),
          Nat.card K = (p ^ f) ^ 2 ∧ Nat.card F = p ^ f ∧ (u' = u ∨ u' = u * z) ∧ Y 0 = K₁ ∧
          Y 2 = K₂ ∧ h⁻¹ * z * h = u' ∧ (Y 1 = cj K₁ h ∨ Y 1 = cj K₂ h) ∧
          IsUnitaryA3Neighborhood (p ^ f) K F z u' Y ∧
          ∃ T : Subgroup G, T ≤ (⨆ i, Y i : Subgroup G) ⊓ Cz z ∧ IsPGroup 2 T ∧
            Nat.card (S : Subgroup G) ≤ Nat.card T)

@[expose] def LULocalLeaf'_gh : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsKProperSimple G → KGH G → ∀ p f : ℕ, p.Prime → p ≠ 2 → 5 ≤ p ^ f →
    ∀ (z : G) (S : Sylow 2 G) (K₁ K₂ : Subgroup G) (t u : G), LUComps G (p ^ f) z K₁ K₂ →
      LUSyl G z S K₁ K₂ t u → MaxOverCentralizerPSp4 z p f →
      (LUEps G (p ^ f) 1 z K₁ u → (p ^ f = 5 → FiveExtra G z S) →
        ∃ (K : Type) (_ : Field K) (_ : Finite K) (u' : G) (Y : Fin 3 → Subgroup G),
          Nat.card K = p ^ f ∧ IsLinearA3Neighborhood K z u' Y ∧
            Subgroup.centralizer ({z} : Set G) ≤
              Subgroup.normalizer ((⨆ i, Y i : Subgroup G) : Set G)) ∧
      (LUEps G (p ^ f) (-1) z K₁ u →
        ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K p) (F : Type) (_ : Field F)
          (_ : Finite F) (u' : G) (Y : Fin 3 → Subgroup G),
          Nat.card K = (p ^ f) ^ 2 ∧ Nat.card F = p ^ f ∧
            IsUnitaryA3Neighborhood (p ^ f) K F z u' Y ∧
            Subgroup.centralizer ({z} : Set G) ≤
              Subgroup.normalizer ((⨆ i, Y i : Subgroup G) : Set G))

theorem luA3Leaf'_gh_of_cores (hLin : LUA3Lin_gh) (hUni : LUA3Uni_gh) (hFive : LUA3Five'_gh) :
    LUA3Leaf'_gh := by
  intro G _ _ hG hKGH p f hp hp2 hq z S K₁ K₂ t u hc hs h6A h61 hgen
  have hH : A3Hyp G p f z S K₁ K₂ t u := ⟨hc, hs, h6A, h61, hgen⟩
  constructor
  · intro he hF
    have hcore : A3CoreLin G p f z K₁ K₂ u := by
      by_cases h5 : p ^ f = 5
      · exact hFive G hG hKGH p f hp hp2 hq h5 z S K₁ K₂ t u hH he (hF h5)
      · exact hLin G hG hKGH p f hp hp2 hq h5 z S K₁ K₂ t u hH he
    obtain ⟨K, hK, hKf, u', h, L, hKc, hu', hh, hLc, hα, hβ⟩ := hcore
    obtain ⟨hz1, hz2, hu'L, hzu, hcomm⟩ := a3_common hc hs hu' hh hLc
    have hN : IsLinearA3Neighborhood K z u' ![K₁, L, K₂] :=
      ⟨a3_sl2 hc K hKc hLc, hz1, hz2, hu'L, hzu, hcomm, hc.comm, hα, hβ⟩
    have := he.A0_cyc
    obtain ⟨T, hT, hTp, hTc⟩ := exists_T_of_nbhd_lin hp hp2 (by omega) hKc hc hs hN
    refine ⟨K, hK, hKf, u', ![K₁, L, K₂], h, hKc, hu', rfl, rfl, hh, hLc, hN, T, ?_, hTp, hTc⟩
    rw [iSup_vec_three]; exact hT
  · intro he
    have hcore := hUni G hG hKGH p f hp hp2 hq z S K₁ K₂ t u hH he
    obtain ⟨K, hK, hKf, hKp, F, hF, hFf, u', h, L, hKc, hFc, hu', hh, hLc, hα, hβ⟩ := hcore
    obtain ⟨hz1, hz2, hu'L, hzu, hcomm⟩ := a3_common hc hs hu' hh hLc
    have hN : IsUnitaryA3Neighborhood (p ^ f) K F z u' ![K₁, L, K₂] :=
      ⟨a3_sl2 hc F hFc hLc, hz1, hz2, hu'L, hzu, hcomm, hc.comm, hα, hβ⟩
    have := he.A0_cyc
    have : Fact p.Prime := ⟨hp⟩
    obtain ⟨T, hT, hTp, hTc⟩ := exists_T_of_nbhd_uni hp2 hq hKc hFc hc hs hN
    refine ⟨K, hK, hKf, hKp, F, hF, hFf, u', ![K₁, L, K₂], h, hKc, hFc, hu', rfl, rfl, hh, hLc, hN, T, ?_,
      hTp, hTc⟩
    rw [iSup_vec_three]; exact hT

theorem luLocalLeaf'_gh_of_leaves
    (hGen : LUGenLeaf) (hA3 : LUA3Leaf'_gh) : LULocalLeaf'_gh := by
  intro G _ _ hG hKGH p f hp hp2 hq z S K₁ K₂ t u hc hs h6A
  constructor
  · intro he hF
    obtain ⟨u₀, hu₀, hs₀, h61⟩ := normalize_u hG hp hp2 hq hc hs he.A0_cyc h6A
    have he₀ : LUEps G (p ^ f) 1 z K₁ u₀ := by
      rcases hu₀ with rfl | rfl
      · exact he
      · exact he.mul_z hc
    have hgen := hGen G hG p f hp hp2 hq z S K₁ K₂ t u₀ 1 hc hs₀ he₀ h6A h61
    obtain ⟨K, hK, hKf, u', Y, h, hKc, hu', hY0, hY2, hh, hY1, hA, T, hT, hTp, hTc⟩ :=
      (hA3 G hG hKGH p f hp hp2 hq z S K₁ K₂ t u₀ hc hs₀ h6A h61 hgen).1 he₀ hF
    refine ⟨K, hK, hKf, u', Y, hKc, hA, ?_⟩
    exact lu_F5 hc hs₀ h61 hgen (u := u₀) hu' hY0 hY2 hh hY1 (fun x hx => (hT hx).1) (fun x hx => (hT hx).2) hTp hTc
  · intro he
    obtain ⟨u₀, hu₀, hs₀, h61⟩ := normalize_u hG hp hp2 hq hc hs he.A0_cyc h6A
    have he₀ : LUEps G (p ^ f) (-1) z K₁ u₀ := by
      rcases hu₀ with rfl | rfl
      · exact he
      · exact he.mul_z hc
    have hgen := hGen G hG p f hp hp2 hq z S K₁ K₂ t u₀ (-1) hc hs₀ he₀ h6A h61
    obtain ⟨K, hK, hKf, hKp, F, hF, hFf, u', Y, h, hKc, hFc, hu', hY0, hY2, hh, hY1, hA, T, hT,
      hTp, hTc⟩ := (hA3 G hG hKGH p f hp hp2 hq z S K₁ K₂ t u₀ hc hs₀ h6A h61 hgen).2 he₀
    refine ⟨K, hK, hKf, hKp, F, hF, hFf, u', Y, hKc, hFc, hA, ?_⟩
    exact lu_F5 hc hs₀ h61 hgen (u := u₀) hu' hY0 hY2 hh hY1 (fun x hx => (hT hx).1) (fun x hx => (hT hx).2) hTp hTc

theorem luLocalLeaf'_gh_of_cores
    (hLin : LUA3Lin_gh) (hUni : LUA3Uni_gh) (hFive : LUA3Five'_gh) : LULocalLeaf'_gh :=
  luLocalLeaf'_gh_of_leaves luGenLeaf (luA3Leaf'_gh_of_cores hLin hUni hFive)

theorem luLocalLeaf'_gh_of_inputs
    (h95 : CFSG.GH74.GLS.IVK.Proofs2.IVK_9_5At_gh_all) (hCov : L3Cover)
    (hFive : LUA3Five') : LULocalLeaf'_gh :=
  luLocalLeaf'_gh_of_cores (luA3Lin_of_inputs_gh h95 hCov) (luA3Uni_of_inputs_gh h95 hCov)
    (LUA3Five'_gh_of hFive)

theorem luNeighborhood_at'_gh (hT0 : LUSetupLeaf') (hT1 : LULocalLeaf'_gh) {G : Type} [Group G]
    [Finite G] (hG : IsKProperSimple G) (hKGH : KGH G) {Gs : Type} [Group Gs] (hcompat : IsTwoCentralClassicalTypeCompat G Gs)
    {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) (h6A : LUMax6AAt G Gs p f) :
    LUNbhdConcl G Gs p f := by
  constructor
  · rintro ⟨h8, hL⟩
    obtain ⟨z, S, K₁, K₂, t, u, hc, hs, he, hF⟩ := (hT0 G hG Gs hcompat p f hp hp2 hq).1 ⟨h8, hL⟩
    obtain ⟨K, hK, hKf, u', Y, hKc, hA, hCN⟩ :=
      (hT1 G hG hKGH p f hp hp2 hq z S K₁ K₂ t u hc hs
        (h6A (Or.inl ⟨h8, hL⟩) z hs.isCentralInvolution)).1 he hF
    exact ⟨K, hK, hKf, z, u', Y, hKc, hs.isCentralInvolution, hA, hCN⟩
  · rintro ⟨h8, hU⟩
    obtain ⟨z, S, K₁, K₂, t, u, hc, hs, he⟩ := (hT0 G hG Gs hcompat p f hp hp2 hq).2 ⟨h8, hU⟩
    obtain ⟨K, hK, hKf, hKp, F, hF, hFf, u', Y, hKc, hFc, hA, hCN⟩ :=
      (hT1 G hG hKGH p f hp hp2 hq z S K₁ K₂ t u hc hs
        (h6A (Or.inr ⟨h8, hU⟩) z hs.isCentralInvolution)).2 he
    exact ⟨K, hK, hKf, hKp, F, hF, hFf, z, u', Y, hKc, hFc, hs.isCentralInvolution, hA, hCN⟩

end CFSG.GH74.GLS.LU.Local
