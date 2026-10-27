module

public import CFSG.GH74.Generic.S45.LQSmall
public import CFSG.GH74.Generic.S45.LBridge
public import CFSG.LocalAnalysis.ComponentClassification.OddClassSelectorU
public import CFSG.LocalAnalysis.ComponentInitial.CommutingBlock
public import CFSG.Certificates.CosetTableShort
public import CFSG.Certificates.Kernel.LocalCompTits.Span
public import CFSG.Fischer.Uniq.CompTau
public import CFSG.GH74.Generic.FrontEnd
public import CFSG.LinearAlgebra.LinearGroups.CoordinateData
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBDerivedNormalSectionBound
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBGraphFieldArithmetic
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBGraphFieldUnitaryData
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHigherLinearFieldDeterminant
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFiveStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointActionModels
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointPlusBorelModel
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareField
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixComponentsCover
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalTraceZeroCoordinates
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBProjectiveInvolutionStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticBField
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticBLinear
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticRepresentationOdd
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBUnitaryBFixed
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueUStatement
public import CFSG.LocalAnalysis.ComponentClassification.ExcSelectorComponents
public import CFSG.LocalAnalysis.ComponentClassification.GSLitInputs
public import CFSG.LocalAnalysis.ComponentClassification.OddSelector
public import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalCTILinearSocle
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSLAllInvolutions
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSUFieldOddCore
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrCentralSylowMaximality
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedGSAContainedSource
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedLayerOddCoreUnbalancingTriple
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasSix
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalStandardFormsRegular
public import CFSG.LocalAnalysis.ComponentInitial.ProjectiveEigenspaceComponent
public import CFSG.LocalAnalysis.ComponentInitial.SylowPointRecovery
public import CFSG.LocalAnalysis.QuasithinUnique.Setting
public import CFSG.Permutation.AlternatingAutomorphism
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
public import Certificates.Certificate3085Base
public import Certificates.Kernel.J4Count.FixC
public import Certificates.Kernel.J4Count.FixCPairBase1
public import Certificates.Kernel.J4Count.KFactsBase
public import Certificates.Kernel.SporSch.J4S.NoCP
public import TauCeti.LinearAlgebra.Dimension.IsQuadraticExtension
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalBasis

public section

namespace CFSG.GH74.Generic.S45

open CFSG CFSG.Blueprint Subgroup CFSG.GH74.Uniqueness.Bender
open CFSG.ComponentClassification.ExcSelector
open CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.RestrictedStd
open CFSG.ComponentClassification.OuterAutomorphisms (inner_normal)

local notation "Inn" => CFSG.ComponentClassification.OuterAutomorphisms.inner

theorem isComponentOf_of_normal_inf' {G : Type*} [Group G] {T H B : Subgroup G} (hT : T.Normal)
    (hB : CFSG.Assembly.IsComponentOf B (T ⊓ H)) : CFSG.Assembly.IsComponentOf B H := by
  refine ⟨hB.1.trans inf_le_right, CFSG.LocalAnalysis.ComponentInitial.assembly_isSubnormal_trans
    hB.2.1 (CFSG.Assembly.IsSubnormal.step inf_le_right ?_ (CFSG.Assembly.IsSubnormal.refl H)),
    hB.2.2⟩
  rw [inf_subgroupOf_right]
  exact hT.subgroupOf H

theorem psu_ge_five_false {S : Type} [Group S] [Finite S] (hS : IsSimpleGroup S)
    (hnab : ∃ a b : S, a * b ≠ b * a) {p f n : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f)
    (hn : 5 ≤ n) (hM : LieModel S .PSU n p f) {ya : MulAut S} {Lb : Subgroup S} {q : ℕ}
    (hQ : QData S ya Lb q) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hZ : Subgroup.center S = ⊥ := center_eq_bot_of_simple_nonab hS hnab
  obtain ⟨L', hL', ⟨eLb⟩⟩ := exists_component_conj hZ ya hQ.le hQ.sub hQ.simple hQ.nonab
  have hι : Function.Injective (MulAut.conj : S →* MulAut S) := by
    intro g g' h
    have hc : g'⁻¹ * g ∈ Subgroup.center S := Subgroup.mem_center_iff.2 fun x => by
      have hx := congrArg (fun φ : MulAut S => φ x) h
      simp only [MulAut.conj_apply] at hx
      calc x * (g'⁻¹ * g) = g'⁻¹ * (g' * x * g'⁻¹) * g := by group
        _ = g'⁻¹ * (g * x * g⁻¹) * g := by rw [hx]
        _ = g'⁻¹ * g * x := by group
    rw [hZ, Subgroup.mem_bot] at hc
    exact (inv_mul_eq_one.1 hc).symm
  let e : S ≃* ↥(Inn S) := MonoidHom.ofInjective hι
  have : IsSimpleGroup S := hS
  have hWs : IsSimpleGroup ↥(Inn S) := e.symm.isSimpleGroup
  have hWnab : ∃ x y : ↥(Inn S), x * y ≠ y * x := by
    obtain ⟨a, b, hab⟩ := hnab
    refine ⟨e a, e b, fun h => hab (e.injective ?_)⟩
    rw [map_mul, map_mul]
    exact h
  have hconj : ∀ (α : MulAut S) (s : S), α * MulAut.conj s * α⁻¹ = MulAut.conj (α s) := fun α s => by
    ext x
    simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv, MulAut.apply_inv_self]
  have hCW : Subgroup.centralizer ((Inn S : Subgroup (MulAut S)) : Set (MulAut S)) = ⊥ := by
    rw [eq_bot_iff]
    intro α hα
    rw [Subgroup.mem_bot]
    ext s
    have h1 : MulAut.conj s * α = α * MulAut.conj s :=
      Subgroup.mem_centralizer_iff.1 hα (MulAut.conj s) ⟨s, rfl⟩
    have h2 : MulAut.conj (α s) = MulAut.conj s := by
      rw [← hconj α s, ← h1]
      group
    simpa using hι h2
  have ha : orderOf ya = 2 := orderOf_eq_prime (by rw [pow_two]; exact hQ.sq) hQ.ne
  have hLW : L' ≤ Inn S := hL'.1.trans inf_le_left
  have hL : CFSG.Assembly.IsComponentOf L' (Subgroup.centralizer ({ya} : Set (MulAut S))) :=
    isComponentOf_of_normal_inf' (inner_normal S) hL'
  have hs : SmallSource L' := (smallSource_iff L').2 ((smallType_congr eLb).1 hQ.smallQ8.1)
  exact CFSG.ComponentClassification.OddClassSelector.su_family_false (A := MulAut S)
    (W := Inn S) hWs hWnab hCW ha hLW hL hs hp hp2 hf hn
    (CFSG.LieType.CurtisTits.lieModel_of_mulEquiv e hM)

theorem oddRow_psu_ge_five {K : Type} [Group K] [Finite K] {y : MulAut K} {L : Subgroup K}
    (hyp : Hyp1310 K y L) {r n f : ℕ} (hr2 : r ≠ 2) (hn : 5 ≤ n)
    (hmodel : StatedClassicalModel (K ⧸ center K) .PSU n r f) : False := by
  obtain ⟨yb, Lb, q, -, hQ, -⟩ := hyp.quot_data
  exact psu_ge_five_false hyp.1.1.2.1 hyp.1.1.2.2 hmodel.1.1 hr2 hmodel.1.2.1 hn
    (Or.inl ⟨by simp [classicalTags], hmodel⟩) hQ

end CFSG.GH74.Generic.S45
