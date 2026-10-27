module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4IBLift
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4IBCentK7
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4IBCentKB
public import Certificates.Kernel.ThCent.Leaves
public import CFSG.Blueprint.OddStandardExact
public import CFSG.Blueprint.RecognitionDefs
public import CFSG.CGT.Timmesfeld75.L2Pair
public import CFSG.CGT.Timmesfeld75.ListWCBasic
public import CFSG.ClassicalGroups
public import CFSG.ClassicalInvolution.QuaternionStructure
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.LieType.BorelTits.CompleteFlag
public import CFSG.LieType.Universal.SpinOmega.Range
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBDerivedNormalSectionBound
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointActionModels
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointDataModelWitness
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSemilinearDataCompatibility
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherEvenOrthogonalModel
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.BridgeLowCenter
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.BridgeMat
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Lemma32
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10Sylow
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2FiveCard
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4Conj
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4IAutStd
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4Struct
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Standard
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.TypesCplxConj
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.TypesOmegaConj
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldPrimeOrderFixedSubfield
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.OrderThreeNormalizer
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGammaL2PSLRangeCentralizer
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinInvolutionCount
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinRestrictionSixCount
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinUDecomposition
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseEquationEleven
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseEquationTen
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseEquationTenStructuralIdentities
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCasePSL2FieldProjectionArithmetic
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCasePSL2OrderPSubgroupCount
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Suzuki.OddGraphReconstruction
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
public import Certificates.Certificate9
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalBasis

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem sec4ILift_centK (hL : IsOmega7Group L) (e : ↥L ⧸ Subgroup.center ↥L ≃* Sec4IOmega)
    {P : Subgroup G} (hP : IsSylow2Of P L) {fr : Sec4IFrame Sec4IQ}
    (hfr : Sec4IGood fr ((P.subgroupOf L).map (sec4IRho e))) :
    ∀ v, IsEvenVec v → vecWeight v = 6 → ∀ K : Subgroup G,
      IsComponentIn K (L ⊓ centralizer ({sec4ILiftPhi e fr P v} : Set G)) →
        sec4ILiftPhi e fr P v ∈ K → IsTwoU43 (↥K ⧸ oddCore ↥K) →
          centralizer (K : Set G) ⊓ sec4ILiftB e fr P = zpowers (sec4ILiftPhi e fr P v) := by
  intro v hv hv6 K hKc huK hK
  have hKle : K ≤ L ⊓ centralizer ({sec4ILiftPhi e fr P v} : Set G) := hKc.1
  have hKL : K ≤ L := hKle.trans inf_le_left
  have huB : sec4ILiftPhi e fr P v ∈ sec4ILiftB e fr P := sec4ILiftPhi_mem hL e hP hfr hv
  obtain ⟨huL, -, hρu⟩ := sec4ILiftPhi_spec hL e hP hfr hv
  have hcover := sec4ICover_odd hL e
  have hsq : ∀ x ∈ sec4ILiftB e fr P, x * x = 1 := fun x hx => by
    have := (sec4ILift_isMax hL e hP hfr).2.1.2 x hx
    rwa [pow_two] at this
  have hKu : ∀ k ∈ K, k * sec4ILiftPhi e fr P v = sec4ILiftPhi e fr P v * k := fun k hk =>
    Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp (hKle hk)).2
  apply le_antisymm
  · intro b hb
    obtain ⟨hbC, hbB⟩ := Subgroup.mem_inf.mp hb
    have hbC' : ∀ k ∈ K, k * b = b * k := fun k hk =>
      (Subgroup.mem_centralizer_iff.mp hbC k hk)
    obtain ⟨hbL, -, hbρ⟩ := (mem_sec4ILiftB_iff e fr P).mp hbB
    obtain ⟨w, hw, hwb⟩ := (mem_sec4IB0_iff fr).mp hbρ
    have h7 := sec4I_seven_dvd_map hL e hKL hK
    haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
    obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card'
      (G := ((K.subgroupOf L).map (sec4IRho e))) 7 h7
    have hy' : orderOf (y : ProjOrth Sec4IQ) = 7 := by rw [Subgroup.orderOf_coe]; exact hy
    obtain ⟨k, hk, hky⟩ := Subgroup.mem_map.mp y.2
    have hkK : (k : G) ∈ K := hk
    have hyv : (y : ProjOrth Sec4IQ) * sec4IPsi fr v = sec4IPsi fr v * (y : ProjOrth Sec4IQ) := by
      rw [← hky, ← hρu, ← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (hKu k hkK)
    have hyw : (y : ProjOrth Sec4IQ) * sec4IPsi fr w = sec4IPsi fr w * (y : ProjOrth Sec4IQ) := by
      rw [← hky, hwb, ← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (hbC' k hkK)
    rcases sec4I_centK_B0 sec4IQ_nondegenerate fr hv hv6 hw hy' hyv hyw with h0 | hwv
    · have h1 : sec4IRho e ⟨b, hbL⟩ = 1 := by rw [← hwb, h0, sec4IPsi_zero]
      have hker : (⟨b, hbL⟩ : ↥L) ∈ (sec4ICover e).ker := by
        rw [MonoidHom.mem_ker]
        exact Subtype.ext h1
      have hb1 : (⟨b, hbL⟩ : ↥L) = 1 :=
        hcover.eq_one_of_mul_self_eq_one hker (Subtype.ext (hsq b hbB))
      have hb1' : b = 1 := congrArg Subtype.val hb1
      rw [hb1']
      exact Subgroup.one_mem _
    · have h1 : sec4ICover e ⟨b, hbL⟩ = sec4ICover e ⟨sec4ILiftPhi e fr P v, huL⟩ := by
        apply Subtype.ext
        change sec4IRho e ⟨b, hbL⟩ = sec4IRho e ⟨sec4ILiftPhi e fr P v, huL⟩
        rw [hρu, ← hwb, hwv]
      have heq : (⟨b, hbL⟩ : ↥L) = ⟨sec4ILiftPhi e fr P v, huL⟩ :=
        hcover.eq_of_mul_self_eq_one (a := ⟨b, hbL⟩) (b := ⟨sec4ILiftPhi e fr P v, huL⟩)
          (Subtype.ext (hsq b hbB)) (Subtype.ext (hsq _ huB)) h1
      have hbu : b = sec4ILiftPhi e fr P v := congrArg Subtype.val heq
      rw [hbu]
      exact Subgroup.mem_zpowers _
  · rw [Subgroup.zpowers_le]
    refine Subgroup.mem_inf.mpr ⟨?_, huB⟩
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    exact hKu k hk

end CFSG.OddStandard.SmallF3.Omega
