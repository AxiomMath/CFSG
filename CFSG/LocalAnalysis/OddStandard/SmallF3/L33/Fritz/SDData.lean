module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.L33.Fritz.SDDataCore
public import CFSG.Sporadic.Schreier.J4SOrder
public import Certificates.Kernel.ThCent.Leaves
public import CFSG.Assembly.QuasithinDefs
public import CFSG.LinearAlgebra.LinearGroups.LinearTwo
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierLinearTwo
public import CFSG.LocalAnalysis.ComponentClassification.GSLitType
public import CFSG.LocalAnalysis.ComponentClassification.HSFLitA7Harada
public import CFSG.LocalAnalysis.ComponentClassification.HSFLitExclusion
public import CFSG.LocalAnalysis.ComponentClassification.PSL3FourInvolutions
public import CFSG.LocalAnalysis.ComponentClassification.TBLitIntrinsicTypes
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrCentralSylowMaximality
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedGSAContainedSource
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedLayerOddCoreUnbalancingTriple
public import CFSG.LocalAnalysis.LargeEvenClassification.SmallAbelianModels
public import CFSG.LocalAnalysis.SectionRank.EvenCover.Catalog
public import CFSG.LocalAnalysis.SectionRank.LargeRee.SuzukiData
public import CFSG.LocalAnalysis.SectionRank.OddCover.CatalogOdd
public import CFSG.LocalAnalysis.SectionRank.SectionAssemblyBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.J4LocalBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public import CFSG.LocalAnalysis.SectionRank.TitsCover
public import CFSG.Quasithin.Background.A3Components
public import CFSG.Quasithin.Background.A3ComponentsAmbient
public import CFSG.Quasithin.Background.A3Structure36BAction
public import CFSG.Quasithin.Background.A3Structure36BBasic
public import CFSG.Quasithin.Background.A3Structure36BPrime
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
public import Certificates.Certificate44
public import Certificates.Certificate5
public import Certificates.Certificate6
public import Certificates.Certificate7
public import Certificates.Certificate8
public import Certificates.Certificate9

public section

namespace CFSG.OddStandard.SmallF3.L33.KD

open CFSG Subgroup Equiv CFSG.ComponentClassification.UnbalancedLayer
open CFSG.ComponentClassification.HSFLit

variable {X : Type} [Group X]

namespace SDData

variable {t : X} {L : Subgroup X} (A : SDData t L) [Finite X]

@[expose] noncomputable def ψH : A.T →* H8 := A.ψ.codRestrict H8 A.ψ_mem_H8

@[expose] noncomputable def ψlin : A.T →* (ZMod 8)ˣ := lin8.comp A.ψH

omit [Finite X] in
theorem ψH_coe (g : A.T) : (A.ψH g : Perm (ZMod 8)) = A.ψ g := rfl

omit [Finite X] in
theorem exists_finset_closure_eq_of_le_T {U : Subgroup X} (hU : U ≤ A.T) :
    ∃ s : Finset X, s.card ≤ 4 ∧ closure (s : Set X) = U := by
  classical
  set U' : Subgroup A.T := U.subgroupOf A.T with hU'
  obtain ⟨s, hs, hsU⟩ := exists_finset_closure_eq_of_card_le (U'.map A.ψlin) (k := 2) (by
    calc Nat.card (U'.map A.ψlin) ≤ Nat.card (ZMod 8)ˣ := Subgroup.card_le_card_group _
      _ = 2 ^ 2 := by rw [card_units_zmod_eight]; norm_num)
  set V : Subgroup A.T := U' ⊓ A.ψlin.ker with hV
  have hVC : V.map A.ψ ≤ C8 := by
    rintro _ ⟨g, hg, rfl⟩
    have h1 : A.ψlin g = 1 := (mem_inf.mp hg).2
    exact (lin8_eq_one_iff (A.ψH g)).mp h1
  have : IsCyclic (V.map A.ψ) := Subgroup.isCyclic_of_le hVC
  obtain ⟨s₁, hs₁, hs₁V⟩ := exists_finset_closure_eq_of_isCyclic (V.map A.ψ)
  have hKc : IsCyclic (A.K.subgroupOf A.T) :=
    (subgroupOfEquivOfLe (inf_le_left : A.K ≤ A.T)).isCyclic.mpr A.isCyclic_K
  have hle : V ⊓ A.ψ.ker ≤ A.K.subgroupOf A.T := by
    intro g hg
    exact ⟨g.2, (A.ψ_eq_one_iff g).mp (mem_inf.mp hg).2⟩
  have : IsCyclic (V ⊓ A.ψ.ker : Subgroup A.T) := Subgroup.isCyclic_of_le hle
  obtain ⟨r₁, hr₁, hr₁V⟩ := exists_finset_closure_eq_of_isCyclic (V ⊓ A.ψ.ker)
  obtain ⟨v, hv, hvV⟩ := exists_finset_closure_eq_of_map A.ψ V hs₁ hs₁V hr₁ hr₁V
  obtain ⟨u, hu, huU⟩ := exists_finset_closure_eq_of_map A.ψlin U' hs hsU hv hvV
  refine ⟨u.image A.T.subtype, Finset.card_image_le.trans hu, ?_⟩
  rw [Finset.coe_image, ← MonoidHom.map_closure, huU, hU', subgroupOf_map_subtype,
    inf_of_le_left hU]

theorem gen4_of_coe_sylow_eq (S : Sylow 2 X) (hS : (S : Subgroup X) = A.T) (P : Subgroup X)
    (hP : IsPGroup 2 P) : ∃ s : Finset X, s.card ≤ 4 ∧ closure (s : Set X) = P :=
  exists_finset_closure_eq_of_sylow S (fun _ hU => A.exists_finset_closure_eq_of_le_T (hS ▸ hU))
    P hP

structure CaseKD where
  k : X
  k_mem : k ∈ A.T
  k_sq : k ^ 2 = 1
  ψ_k : A.ψ ⟨k, k_mem⟩ = k8
  d : X
  d_mem : d ∈ A.T
  ψ_d : A.ψ ⟨d, d_mem⟩ = d8
  card_K : Nat.card A.K = 2

end SDData

end CFSG.OddStandard.SmallF3.L33.KD
