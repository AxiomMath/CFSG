module

public import CFSG.GH74.Generic.Certificates
public import CFSG.GH74.Generic.GKFCover
public import CFSG.GH74.Generic.S3.Front
public import CFSG.GH74.KGroups.L3EpsFour
public import CFSG.GH74.Generic.S3.L3Cover
public import CFSG.LocalAnalysis.ComponentInitial.SwappedQuasisimple
public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.PerfectResiduals
public import Certificates.Kernel.ThCent.Leaves
public import CFSG.CGT.Timmesfeld75.L2Pair
public import CFSG.CGT.Timmesfeld75.ListWCBasic
public import CFSG.Certificates.WordSubgroupRel
public import CFSG.ClassicalGroups
public import CFSG.GH74.Generic.Front.Final
public import CFSG.GH74.Generic.FrontEnd
public import CFSG.GH74.Generic.S1.LinFull
public import CFSG.GH74.Generic.S3.LeavesFine
public import CFSG.GH74.Generic.S3.Lem37
public import CFSG.LieType.Multipliers.ProductKernel
public import CFSG.LieType.Multipliers.U42Bridge
public import CFSG.LieType.Multipliers.U43Action
public import CFSG.LieType.Multipliers.U43BridgeInputs
public import CFSG.LieType.Multipliers.U62Action
public import CFSG.LieType.Multipliers.U62Bridge
public import CFSG.LieType.Multipliers.U62Kernel
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBDerivedNormalSectionBound
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalDescentEndpoint
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFiveStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFixedTransfer
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointActionModels
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointPlusBorelModel
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareField
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixComponentsCover
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixModelGeometry
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalTraceZeroCoordinates
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBProjectiveInvolutionStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticBField
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticBLinear
public import CFSG.LocalAnalysis.ComponentClassification.StandardRecognitionQuaternion
public import CFSG.LocalAnalysis.ComponentClassification.TBLitCover
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpExclusion
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedGSBFixedLayer
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalStandardFormsRegular
public import CFSG.LocalAnalysis.ComponentInitial.SylowPointRecovery
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherAllInvolutionFourGroup
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeCheckBase
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeModel
public import CFSG.LocalAnalysis.EvenSmallLie.Sp6JCondition
public import CFSG.LocalAnalysis.QuasithinUnique.Setting
public import CFSG.Monster.B.Classical.PlaneAut
public import CFSG.Monster.B.TwoA.Amalgam.Data
public import CFSG.Monster.B.TwoA.Sp8.Par1
public import CFSG.Monster.B.TwoA.Unitary.LinThree
public import CFSG.Monster.B.TwoA.Unitary.Orbit1408Points
public import CFSG.Sporadic.Bridge.LyData
public import CFSG.Sporadic.Bridge.TableSurj
public import CFSG.Sporadic.HN.LevelChainSpec
public import CFSG.Sporadic.Ly.ActionBase
public import CFSG.Sporadic.Ly.CertificateBase
public import CFSG.Sporadic.Ly.FaithSpec
public import CFSG.Sporadic.Ly.OrbitSpec
public import CFSG.Sporadic.Ly.Simple
public import CFSG.Sporadic.LyBase
public import CFSG.Sporadic.McL
public import CFSG.Sporadic.Presentation.Common
public import CFSG.Sporadic.Presentation.Ly
public import CFSG.Sporadic.Schreier.LyChain11
public import CFSG.Sporadic.SmallOddCore.CheckSpec
public import CFSG.YGroups.Y322Central
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
public import Certificates.Certificate119
public import Certificates.Certificate12041
public import Certificates.Certificate12042
public import Certificates.Certificate12043
public import Certificates.Certificate12044
public import Certificates.Certificate12045
public import Certificates.Certificate12046
public import Certificates.Certificate122
public import Certificates.Certificate16015
public import Certificates.Certificate16040
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
public import Certificates.Certificate3085Base
public import Certificates.Certificate3951
public import Certificates.Certificate9130
public import TauCeti.LinearAlgebra.Dimension.IsQuadraticExtension
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalBasis

public section

namespace CFSG.GH74.Generic

open CFSG CFSG.GH74 CFSG.Blueprint CFSG.ABGLocalTools CFSG.Assembly.LowTwoRank Subgroup
open CFSG.ComponentClassification CFSG.LocalAnalysis.ComponentInitial
open scoped commutatorElement

theorem RankCertified.of_hom_ker_le {T H' T' : Type} [Group T] [Finite T] [Group H'] [Group T']
    {r : ℕ} (ψ : T →* H') (π : T →* T') (hπ : Function.Surjective π) (hker : ψ.ker ≤ π.ker)
    (h : RankCertified T' r) : RankCertified H' r := by
  obtain ⟨K₀, A₀, _, _, _, α, β, hβ, hc, hs, hcard, hker₀⟩ := h
  let P : Subgroup (K₀ × T) := (α.comp (MonoidHom.fst K₀ T)).eqLocus (π.comp (MonoidHom.snd K₀ T))
  have hPfin : Finite P := inferInstance
  let α' : P →* H' := ψ.comp ((MonoidHom.snd K₀ T).comp P.subtype)
  let β' : P →* A₀ := (β.comp (MonoidHom.fst K₀ T)).comp P.subtype
  refine ⟨P, A₀, inferInstance, inferInstance, inferInstance, α', β', ?_, hc, hs, hcard, ?_⟩
  · intro a
    obtain ⟨k, rfl⟩ := hβ a
    obtain ⟨g, hg⟩ := hπ (α k)
    exact ⟨⟨(k, g), (hg.symm : α k = π g)⟩, rfl⟩
  · rintro ⟨⟨k, g⟩, hkg⟩ hp
    have hg : ψ g = 1 := by simpa [α'] using hp
    have hk : α k = π g := hkg
    have h1 : π g = 1 := MonoidHom.mem_ker.1 (hker (MonoidHom.mem_ker.2 hg))
    rw [h1] at hk
    have := hker₀ (MonoidHom.mem_ker.2 hk)
    simpa [β'] using this

theorem mem_center_of_perfect_of_commutator_mem_center {E : Type*} [Group E]
    (hE : Group.IsPerfect E) {a : E} (h : ∀ b : E, a * b * a⁻¹ * b⁻¹ ∈ center E) :
    a ∈ center E := by
  set N : Subgroup E := Subgroup.upperCentralSeries E 2 with hN
  have haN : a ∈ N := by
    rw [hN, show (2 : ℕ) = 1 + 1 from rfl, Subgroup.mem_upperCentralSeries_succ_iff,
      Subgroup.upperCentralSeries_one]
    exact h
  have hNc : ⁅N, (⊤ : Subgroup E)⁆ ≤ center E := by
    rw [Subgroup.commutator_le]
    intro n hn y _
    have := (Subgroup.mem_upperCentralSeries_succ_iff (G := E) (n := 1)).1
      (by rw [hN] at hn; exact hn) y
    rw [Subgroup.upperCentralSeries_one] at this
    exact this
  have hcz : ⁅center E, (⊤ : Subgroup E)⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.coe_top, Subgroup.centralizer_univ]
  have h1 : ⁅⁅(⊤ : Subgroup E), N⁆, (⊤ : Subgroup E)⁆ = ⊥ := by
    rw [Subgroup.commutator_comm (⊤ : Subgroup E) N]
    exact eq_bot_iff.2 ((Subgroup.commutator_mono hNc le_rfl).trans hcz.le)
  have h2 : ⁅⁅N, (⊤ : Subgroup E)⁆, (⊤ : Subgroup E)⁆ = ⊥ :=
    eq_bot_iff.2 ((Subgroup.commutator_mono hNc le_rfl).trans hcz.le)
  have h3 := Subgroup.commutator_commutator_eq_bot_of_rotate (H₁ := (⊤ : Subgroup E))
    (H₂ := (⊤ : Subgroup E)) (H₃ := N) h1 h2
  have hperf : ⁅(⊤ : Subgroup E), (⊤ : Subgroup E)⁆ = ⊤ := by
    have := Group.IsPerfect.commutator_eq_top (G := E)
    rwa [_root_.commutator_def] at this
  rw [hperf] at h3
  have h4 : N ≤ centralizer ((⊤ : Subgroup E) : Set E) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.1 (by rw [Subgroup.commutator_comm]; exact h3)
  rw [Subgroup.coe_top, Subgroup.centralizer_univ] at h4
  exact h4 haN

theorem rankCertified_one_of_l3 {K : Type} [Group K] [Finite K] {t : StatedLieTag} {p f : ℕ}
    (ht : t = .PSL ∨ t = .PSU) (hp2 : p ≠ 2) (hX : StatedClassicalModel K t 3 p f) :
    RankCertified K 1 := by
  obtain ⟨S⟩ : Nonempty (Sylow 2 K) := inferInstance
  obtain ⟨a, ha, b, hb, ha2, hb2, hab, ha1, hb1, hne⟩ :=
    KGroups.L3Eps.l3eps_sylow_four ht hp2 hX S.isPGroup' (fun T hT hST => (S.is_maximal' hT hST).le)
  let u : Fin 2 → K := ![a, b]
  refine rankCertified_of_commuting_involutions u ?_ ?_ ?_ (s := 1) (by norm_num)
  · intro i
    fin_cases i
    · simpa [u, pow_two] using ha2
    · simpa [u, pow_two] using hb2
  · intro i j
    fin_cases i <;> fin_cases j
    · exact Commute.refl _
    · exact hab
    · exact hab.symm
    · exact Commute.refl _
  · intro e he h
    have h0 : e 0 = 0 ∨ e 0 = 1 := by omega
    have h1 : e 1 = 0 ∨ e 1 = 1 := by omega
    rcases h0 with h0 | h0 <;> rcases h1 with h1 | h1
    · apply he
      funext i
      fin_cases i
      · exact h0
      · exact h1
    · simp [List.ofFn_succ, u, h0, h1] at h
      exact hb1 h
    · simp [List.ofFn_succ, u, h0, h1] at h
      exact ha1 h
    · simp [List.ofFn_succ, u, h0, h1] at h
      apply hne
      calc a = a * (b * b) := by rw [hb2, mul_one]
        _ = (a * b) * b := by rw [mul_assoc]
        _ = b := by rw [h, one_mul]

end CFSG.GH74.Generic
