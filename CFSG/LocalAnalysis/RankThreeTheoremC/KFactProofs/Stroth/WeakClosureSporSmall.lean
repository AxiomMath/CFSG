module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosureSporLines
public import CFSG.RankThree.Asc83Table.MatGroup
public import Certificates.Certificate3084
public import Certificates.Certificate3119
public import Certificates.Certificate3167
public import Certificates.Certificate3168
public import Certificates.Certificate3169
public import Certificates.Certificate3172
public import Certificates.Certificate8000
public import Certificates.Certificate8019
public import Certificates.Certificate8024
public import Certificates.Certificate8029
public import Certificates.Certificate8018
public import Certificates.Certificate9119
public import Certificates.Certificate9211
public import Certificates.Certificate9435
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.J3Sylow
import CFSG.LocalAnalysis.SectionRank.Sporadic.HSLocal
import CFSG.LocalAnalysis.SectionRank.Sporadic.OpsF2Fast
import CFSG.LocalAnalysis.SectionRank.Sporadic.HeLocal
import CFSG.LocalAnalysis.SectionRank.Sporadic.J4Local
import CFSG.LocalAnalysis.SectionRank.Sporadic.RuLocal
import CFSG.RankThree.Asc83Table.HS
import CFSG.Sporadic.Bridge.J3Surj
import CFSG.Sporadic.HS
import CFSG.Sporadic.He.Simple
import CFSG.Sporadic.J1
import CFSG.Sporadic.J3
import CFSG.Sporadic.J4
import CFSG.Sporadic.Ru
public import CFSG.Certificates.CentralKernel
public import CFSG.Certificates.CosetTableWalkC
public import CFSG.Certificates.FusionF2
public import CFSG.Certificates.WordSubgroupHom
public import CFSG.GroupTheory.HallHigmanPiCore
public import CFSG.GroupTheory.PerfectResidualNodes
public import CFSG.LieType.Chevalley.EvenRootCommutatorF4
public import CFSG.LieType.Ree.SmallReeModelSchreier
public import CFSG.LieType.Universal.Spin.Roots
public import CFSG.LieType.Universal.SpinOmega
public import CFSG.LocalAnalysis.AGLEmbedding.JStarReducedDefs
public import CFSG.LocalAnalysis.AGLEmbedding.ResidualTools
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHermitianIsometry
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.ComponentInitial.LayerComponentOrbit
public import CFSG.LocalAnalysis.ComponentInitial.SylowPointRecovery
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.TypeB2
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.Unitary
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.RankThree.LocalRank.SelectorCases
public import CFSG.RankThree.PartOne.CTP.StrongPClassification
public import CFSG.RankThree.PartOne.CTP.StrongPSylow
public import CFSG.RankThree.PartOne.S10.ThetaContract
public import CFSG.RankThree.PartOne.S12.InputsBase
public import CFSG.RankThree.PartTwo.Sec4.Census.Interface
public import CFSG.Sporadic.Bridge.Catalogue
public import CFSG.Sporadic.Bridge.M11CheckInputs
public import CFSG.Sporadic.Presentation.Co2Base
public import CFSG.Sporadic.Presentation.Co2Cover
public import CFSG.Sporadic.Presentation.Co2Fusion
public import CFSG.Sporadic.Presentation.Co2FusionInputs
public import CFSG.Sporadic.Presentation.McLExactData
public import CFSG.Sporadic.Presentation.McLExactInputs
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Isaacs.VII.lemma_7_7
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldFixedSubfieldCard
public import CFSG.YGroups.DCE.B433Check
public import Certificates.Certificate9124
public import TauCeti.GroupTheory.SpecificGroups.CFSG.TypeC.Agreement
public import TauCeti.LinearAlgebra.CliffordAlgebra.Monomials
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.J3SylowPrim

public section

namespace CFSG.RankThree.Asc83Table

open CFSG.SectionRank CFSG.SectionRank.Native CFSG.RankThree.Asc83Table.Native

variable {M V : Type} {O : Ops M V} {p d : ℕ} (Sp : OpsSpec O p d) [Inhabited M] {sA sB : String}
  {C : MCert} (hC : mcertCheck O sA sB C = true)

theorem E9Facts.conj_exists {rx ry t₁ t₂ t₃ t₄ : ℕ} (hF : E9Facts C rx ry t₁ t₂ t₃ t₄)
    {g o pp q r s : ℕ} (hg : MFact.ord g o ∈ C.facts)
    (h₁ : MFact.conj g [(rx, 1)] [(rx, pp), (ry, r)] ∈ C.facts)
    (h₂ : MFact.conj g [(ry, 1)] [(rx, q), (ry, s)] ∈ C.facts) :
    ∃ n : (certMonoid p d sA sB)ˣ,
      n * (hF.basis Sp hC).a * n⁻¹ = (hF.basis Sp hC).a ^ pp * (hF.basis Sp hC).b ^ r ∧
      n * (hF.basis Sp hC).b * n⁻¹ = (hF.basis Sp hC).a ^ q * (hF.basis Sp hC).b ^ s :=
  ⟨regUnit Sp hC g,
    regUnit_conj' Sp hC h₁ hg (hF.hasOrd (e := 0) (by simp) rfl) (hF.hasOrd (e := 0) (by simp) rfl),
    regUnit_conj' Sp hC h₂ hg (hF.hasOrd (e := 0) (by simp) rfl) (hF.hasOrd (e := 0) (by simp) rfl)⟩

end CFSG.RankThree.Asc83Table

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosure

open CFSG.Blueprint.NativeSporadic CFSG.Open

theorem wcSporadicAt_J1 [Finite (Carrier .J1)] :
    WCSporadicAt .J1 := by
  refine wcSporadicAt_of_card .J1 (N := 175560) CFSG.Sporadic.J1.card_J1 ?_
  intro q hq hq2 hdvd
  have hpf : Nat.primeFactors 175560 = {2, 3, 5, 7, 11, 19} := by norm_num [Nat.primeFactors]
  have hmem := mem_of_sq_dvd (by norm_num) hpf hq hdvd
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd rfl hq2
  all_goals (exfalso; norm_num at hdvd)

theorem wcOn_J3_three_of_equiv
    {K : Type} [Group K] [Finite K]
    (e : K ≃* (TauCeti.CFSGIndex.sporadic .J3).Group) : WCOn 3 K := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine WCOn.of_not_isMulCommutative fun P hcomm => ?_
  obtain ⟨a, ha, b, hb, hab⟩ := (CFSG.AGLEmbedding.kFactJ3Sylow K ⟨e⟩ P).nonabelian
  exact hab (congrArg Subtype.val (hcomm.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩))

theorem wcOn_J3_three
    [Finite (Carrier .J3)] :
    WCOn 3 (Carrier .J3) := by
  obtain ⟨e⟩ : Nonempty (Carrier .J3 ≃* (TauCeti.CFSGIndex.sporadic .J3).Group) :=
    CFSG.Sporadic.Bridge.J3.nonempty_mulEquiv
  exact wcOn_J3_three_of_equiv e

theorem wcSporadicAt_J3
    [Finite (Carrier .J3)] :
    WCSporadicAt .J3 := by
  refine wcSporadicAt_of_card .J3 (N := 50232960) CFSG.Sporadic.J3.card_J3 ?_
  intro q hq hq2 hdvd
  have hpf : Nat.primeFactors 50232960 = {2, 3, 5, 17, 19} := by norm_num [Nat.primeFactors]
  have hmem := mem_of_sq_dvd (by norm_num) hpf hq hdvd
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl
  · exact absurd rfl hq2
  · exact wcOn_J3_three
  all_goals (exfalso; norm_num at hdvd)

theorem wcSporadicAt_J4
    [Finite (Carrier .J4)] : WCSporadicAt .J4 := by
  refine wcSporadicAt_of_card .J4 (N := 86775571046077562880) CFSG.Sporadic.J4.card_J4 ?_
  intro q hq hq2 hdvd
  have hpf : Nat.primeFactors 86775571046077562880 = {2, 3, 5, 7, 11, 23, 29, 31, 37, 43} := by
    norm_num [Nat.primeFactors]
  have hmem := mem_of_sq_dvd (by norm_num) hpf hq hdvd
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd rfl hq2
  · haveI : Fact (Nat.Prime 3) := ⟨hq⟩
    obtain ⟨x, y, -, hx, hy, hz, -, -, hc, -⟩ := CFSG.SectionRank.J4_sylow3_cubic_witness
    exact WCOn.of_cubic hx hy hz hc
  · exfalso; norm_num at hdvd
  · exfalso; norm_num at hdvd
  · haveI : Fact (Nat.Prime 11) := ⟨hq⟩
    obtain ⟨x, y, -, hx, hy, hz, -, -, hc, -⟩ := CFSG.SectionRank.J4_sylow11_cubic_witness
    exact WCOn.of_cubic hx hy hz hc
  all_goals (exfalso; norm_num at hdvd)

theorem wcOn_HS_three_aux
    [Finite CFSG.Blueprint.NativeSporadic.HS] : WCOn 3 CFSG.Blueprint.NativeSporadic.HS := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  open CFSG.RankThree.Asc83Table CFSG.RankThree.Asc83Table.HS CFSG.SectionRank
    CFSG.SectionRank.Native CFSG.RankThree.Asc83Table.Native in
  obtain ⟨n, hn1, hn2⟩ := facts.conj_exists (spec2fr 20) hs_check (g := 7) (o := 8) (pp := 0)
    (q := 1) (r := 1) (s := 1) (mem_facts 2 rfl) (mem_facts 9 rfl) (mem_facts 10 rfl)
  open CFSG.RankThree.Asc83Table CFSG.RankThree.Asc83Table.HS in
  exact WCOn.of_square_witness (x := E.a) (y := E.b) (h := n) E.ha E.hb E.hab.eq
    (E.card.trans (by norm_num))
    (by
      rw [CFSG.Sporadic.HS.card_HS]
      norm_num)
    (a := 0) (b := 1) (c := 1) (d := 1) hn1 hn2 (by decide +revert)

theorem wcOn_HS_three
    [Finite (Carrier .HS)] : WCOn 3 (Carrier .HS) :=
  wcOn_HS_three_aux

theorem wcSporadicAt_HS
    [Finite (Carrier .HS)] : WCSporadicAt .HS := by
  refine wcSporadicAt_of_card .HS (N := 44352000) CFSG.Sporadic.HS.card_HS ?_
  intro q hq hq2 hdvd
  have hpf : Nat.primeFactors 44352000 = {2, 3, 5, 7, 11} := by norm_num [Nat.primeFactors]
  have hmem := mem_of_sq_dvd (by norm_num) hpf hq hdvd
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl
  · exact absurd rfl hq2
  · exact wcOn_HS_three
  · haveI : Fact (Nat.Prime 5) := ⟨hq⟩
    obtain ⟨x, y, -, hx, hy, hz, -, -, hc, -⟩ := CFSG.SectionRank.HS_sylow5_cubic_witness
    exact WCOn.of_cubic hx hy hz hc
  all_goals (exfalso; norm_num at hdvd)

theorem wcOn_He_five
    [Finite (Carrier .He)] : WCOn 5 (Carrier .He) := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨x, y, h, hx, hy, hxy, hcard, hhx, hhy⟩ := CFSG.SectionRank.He_sylow5_square_witness
  exact WCOn.of_square_witness hx hy hxy hcard
    (by
      show ¬ 5 ^ 3 ∣ Nat.card CFSG.Blueprint.NativeSporadic.He
      rw [CFSG.Sporadic.He.card_He]
      norm_num)
    hhx hhy (by decide +revert)

theorem wcSporadicAt_He
    [Finite (Carrier .He)] : WCSporadicAt .He := by
  refine wcSporadicAt_of_card .He (N := 4030387200) CFSG.Sporadic.He.card_He ?_
  intro q hq hq2 hdvd
  have hpf : Nat.primeFactors 4030387200 = {2, 3, 5, 7, 17} := by norm_num [Nat.primeFactors]
  have hmem := mem_of_sq_dvd (by norm_num) hpf hq hdvd
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl
  · exact absurd rfl hq2
  · haveI : Fact (Nat.Prime 3) := ⟨hq⟩
    obtain ⟨x, y, -, hx, hy, hz, -, -, hc, -⟩ := CFSG.SectionRank.He_sylow3_cubic_witness
    exact WCOn.of_cubic hx hy hz hc
  · exact wcOn_He_five
  · haveI : Fact (Nat.Prime 7) := ⟨hq⟩
    obtain ⟨x, y, -, hx, hy, hz, -, -, hc, -⟩ := CFSG.SectionRank.He_sylow7_cubic_witness
    exact WCOn.of_cubic hx hy hz hc
  · exfalso; norm_num at hdvd

theorem wcSporadicAt_Ru
    [Finite (Carrier .Ru)] : WCSporadicAt .Ru := by
  refine wcSporadicAt_of_card .Ru (N := 145926144000) CFSG.Sporadic.Ru.card_Ru ?_
  intro q hq hq2 hdvd
  have hpf : Nat.primeFactors 145926144000 = {2, 3, 5, 7, 13, 29} := by
    norm_num [Nat.primeFactors]
  have hmem := mem_of_sq_dvd (by norm_num) hpf hq hdvd
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd rfl hq2
  · haveI : Fact (Nat.Prime 3) := ⟨hq⟩
    obtain ⟨x, y, -, hx, hy, hz, -, -, hc, -⟩ := CFSG.SectionRank.Ru_sylow3_cubic_witness
    exact WCOn.of_cubic hx hy hz hc
  · haveI : Fact (Nat.Prime 5) := ⟨hq⟩
    obtain ⟨x, y, -, hx, hy, hz, -, -, hc, -⟩ := CFSG.SectionRank.Ru_sylow5_cubic_witness
    exact WCOn.of_cubic hx hy hz hc
  all_goals (exfalso; norm_num at hdvd)

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosure
