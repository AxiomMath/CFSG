module

public import CFSG.ClassicalInvolution.RouteD.TwinYP1Layer
public import CFSG.ClassicalInvolution.Asc77.AscT7AHyp51
public import CFSG.ClassicalInvolution.Asc77.WP3FrameStar
public import CFSG.ClassicalInvolution.Asc77.WP3FrameLieE
public import CFSG.ClassicalInvolution.SmallCases.ConnectedA2DatumTwin
public import CFSG.ClassicalInvolution.RouteD.TwinSL4BridgeBase
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate80
public import Certificates.Certificate81
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate115
public import Certificates.Certificate116
public import Certificates.Certificate117
public import Certificates.Certificate120
public import Certificates.Certificate123
public import Certificates.Certificate76
public import Certificates.Certificate77
public import Certificates.Certificate78
public import Certificates.Certificate79
public import Certificates.Certificate118
public import Certificates.Certificate119
public import Certificates.Certificate121
public import Certificates.Certificate122
public import CFSG.ClassicalInvolution.Asc77.AscE184Basic
public import CFSG.ClassicalInvolution.Asc77.AscE184OddQuot
public import CFSG.ClassicalInvolution.Asc77.AscE184Sec
public import CFSG.ClassicalInvolution.Asc77.AscE186QuotOdd
public import CFSG.ClassicalInvolution.Asc77.AscSixZW
public import CFSG.ClassicalInvolution.Asc77.ThmEStatement
public import CFSG.ClassicalInvolution.Asc77.WP2Thompson
public import CFSG.ClassicalInvolution.Asc77.WP3FrameChain
public import CFSG.ClassicalInvolution.Balance.QNineFuzzyFree
public import CFSG.ClassicalInvolution.Balance.StrongLocalBalanceGlue
public import CFSG.ClassicalInvolution.Balance.Theorem5Models
public import CFSG.ClassicalInvolution.RouteD.ExoticD4FourBasic
public import CFSG.ClassicalInvolution.RouteD.TwinYSetup
public import CFSG.Goldschmidt.Statements
public import CFSG.Goldschmidt.StatementsH
public import CFSG.Goldschmidt.StatementsX
public import CFSG.LocalAnalysis.ComponentClassification.QuasisimpleNormalizerCommutator
public import CFSG.LocalAnalysis.LargeEvenClassification.CyclicCongruenceCut
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

namespace CFSG.ClassicalInvolution.RouteD.TwinY

open CFSG.Open (signalizerFunctorEk)
open CFSG.ClassicalInvolution.Disconnected
open CFSG.ClassicalInvolution.Balance.BootRank3 (omegaConnected_of_routeD)
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank
  CFSG.ClassicalInvolution.RouteD CFSG.ClassicalInvolution.RouteD.Gaps
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.ExactLayer
  CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.Bootstrap
open CFSG.ClassicalInvolution.Generic.CoreAssembly

local notation "𝒞" => CoreAssembly.conjClass

section FrameData

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {K T J : Subgroup G} {z t : G}

theorem twinFrameData_of (S : RouteDSetup p f K z) (hΩ : HypOmegaMod p f (𝒞 K))
    (e : TwinElt K T z) (hT : T ∈ 𝒞 K) (hTK : T ≠ K) (hKT : Commutes K T)
    (clsT : IsClassicalMember p f T z) (hJ : J ∈ 𝒞 K)
    (hJz : J ≤ Subgroup.centralizer ({z} : Set G)) (hJt : IsClassicalMember p f J t)
    (htz : t ≠ z) (hJK : Commutes J K) (hJT : Commutes J T) :
    TwinFrameData (𝒞 K) K T z e.u J t := by
  have hz : IsUniqueInvolution K z :=
    ConnectedA2.isUniqueInvolution_of_isClassicalMember S.odd S.five S.cls
  have hzT : IsUniqueInvolution T z :=
    ConnectedA2.isUniqueInvolution_of_isClassicalMember S.odd S.five clsT
  have hUt : IsUniqueInvolution J t :=
    ConnectedA2.isUniqueInvolution_of_isClassicalMember S.odd S.five hJt
  have hodd := odd_natCard_galoisField S.odd S.five
  have hKex := S.exact K (CoreAssembly.mem_conjClass_self K)
  refine
    { mem := CoreAssembly.mem_conjClass_self K
      hz := hz
      hK' := ⟨hT, z, hz, hzT⟩
      hne := hTK
      hu := e.u_mem_sup
      hu2 := e.u_mul_self hKT hz.sq
      hu1 := e.u_ne_one S.cls hKex hodd hKT
      huz := e.u_ne_z S.cls hKex hodd hKT
      hJ := ⟨hJ, fun M hM => ?_⟩
      ht := hUt
      htu := ?_ }
  · obtain ⟨hMΩ, w, hwK, hwM⟩ := hM
    have hwz : w = z := (hz.eq hwK).symm
    subst hwz
    have hne : J ≠ M := by
      rintro rfl
      exact htz (hUt.eq hwM)
    exact mem_omegaNbr_of_trivialOnQuot S.odd S.five hΩ hMΩ hwM hJ hne
      (mem_trivialOnQuot_of_le_centralizer hJz)
  · have h1 : t * e.a = e.a * t := hJK t hJt.mem _ e.mem_a
    have h2 : t * e.a' = e.a' * t := hJT t hJt.mem _ e.mem_a'
    unfold TwinElt.u
    calc t * (e.a * e.a') = (t * e.a) * e.a' := by group
      _ = (e.a * t) * e.a' := by rw [h1]
      _ = e.a * (t * e.a') := by group
      _ = e.a * (e.a' * t) := by rw [h2]
      _ = (e.a * e.a') * t := by group

theorem twinFrameSetting_of (S : RouteDSetup p f K z) (hΩ : HypOmegaMod p f (𝒞 K))
    (hA : ∀ M ∈ 𝒞 K, AEmpty (𝒞 K) M) (h7 : Thm7TypedBelow p f (Nat.card G)) {u : G}
    (fd : TwinFrameData (𝒞 K) K T z u J t) : TwinFrameSetting p f (𝒞 K) K T J z u t where
  odd := S.odd
  five := S.five
  hyp := hΩ
  aEmpty := hA
  trans := fun _ hM => hM
  below := S.below
  thm7 := h7
  frame := fd

theorem rankThreeBalance_of (hH : TwinFrameHyp51 p f) [IsSimpleGroup G]
    (S : RouteDSetup p f K z) (hΩ : HypOmegaMod p f (𝒞 K)) (hA : ∀ M ∈ 𝒞 K, AEmpty (𝒞 K) M)
    (h7 : Thm7TypedBelow p f (Nat.card G)) {u : G} (fd : TwinFrameData (𝒞 K) K T z u J t) :
    RankThreeBalance (Subgroup.closure ({z, u, t} : Set G)) :=
  lemma52 G _ (hH G (𝒞 K) K T J z u t (twinFrameSetting_of S hΩ hA h7 fd))

omit [Finite G] in
theorem le_centralizer_frame (e : TwinElt K T z) (hJz : J ≤ Subgroup.centralizer ({z} : Set G))
    (hJt : IsClassicalMember p f J t) (hJK : Commutes J K) (hJT : Commutes J T) :
    J ≤ Subgroup.centralizer ((Subgroup.closure ({z, e.u, t} : Set G) : Subgroup G) : Set G) := by
  rw [Subgroup.centralizer_closure]
  intro j hj
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  rcases hx with rfl | rfl | rfl
  · exact (Subgroup.mem_centralizer_singleton_iff.mp (hJz hj)).symm
  · have h1 : j * e.a = e.a * j := hJK j hj _ e.mem_a
    have h2 : j * e.a' = e.a' * j := hJT j hj _ e.mem_a'
    unfold TwinElt.u
    calc e.a * e.a' * j = e.a * (e.a' * j) := by group
      _ = e.a * (j * e.a') := by rw [h2]
      _ = (e.a * j) * e.a' := by group
      _ = (j * e.a) * e.a' := by rw [h1]
      _ = j * (e.a * e.a') := by group
  · exact (Subgroup.mem_centralizer_singleton_iff.mp
      (le_centralizer_of_isClassicalMember hJt hj)).symm

end FrameData

section Side

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {K T J : Subgroup G} {z t : G}

omit [Finite G] in
theorem le_centralizer_pair {N : Subgroup G} {x y : G}
    (hx : N ≤ Subgroup.centralizer ({x} : Set G)) (hy : N ≤ Subgroup.centralizer ({y} : Set G)) :
    N ≤ Subgroup.centralizer ((Subgroup.closure ({x, y} : Set G) : Subgroup G) : Set G) := by
  rw [Subgroup.centralizer_closure]
  intro n hn
  rw [Subgroup.mem_centralizer_iff]
  intro h hh
  rcases hh with rfl | rfl
  · exact (Subgroup.mem_centralizer_singleton_iff.mp (hx hn)).symm
  · exact (Subgroup.mem_centralizer_singleton_iff.mp (hy hn)).symm

theorem closure_pair_mem_signalizer {B : Subgroup G} {x y : G} (hxB : x ∈ B) (hyB : y ∈ B)
    (hx : x * x = 1) (hy : y * y = 1) (hx1 : x ≠ 1) (hy1 : y ≠ 1) (hxy : x ≠ y)
    (hc : x * y = y * x) : Subgroup.closure ({x, y} : Set G) ∈ signalizerFunctorEk 2 2 B := by
  refine ⟨(Subgroup.closure_le B).mpr ?_, ?_⟩
  · rintro g (rfl | rfl)
    · exact hxB
    · exact hyB
  · rw [card_closure_pair_eq_four hx hy hx1 hy1 hxy hc]
    norm_num

theorem gen_z (S : RouteDSetup p f K z) (hΩ : HypOmegaMod p f (𝒞 K)) (e : TwinElt K T z)
    (fd : TwinFrameData (𝒞 K) K T z e.u J t) (hT : T ∈ centralizingMembers (𝒞 K) {z})
    (hKiso : ∀ N ∈ centralizingMembers (𝒞 K) {z}, N ≠ K → Commutes K N)
    (hTiso : ∀ N ∈ centralizingMembers (𝒞 K) {z}, N ≠ T → Commutes T N)
    (hJK : Commutes J K) (hJT : Commutes J T) :
    CentralizerGenerationStar (𝒞 K) (Subgroup.closure ({z, e.u, t} : Set G)) z := by
  set B := Subgroup.closure ({z, e.u, t} : Set G) with hB
  have hzB : z ∈ B := Subgroup.subset_closure (by simp)
  have huB : e.u ∈ B := Subgroup.subset_closure (by simp)
  have htB : t ∈ B := Subgroup.subset_closure (by simp)
  have hz2 := fd.hz.sq
  have hu2 := fd.hu2
  have ht2 := fd.ht.sq
  have hzt := fd.comm_zt S.odd hΩ
  have hF₁ : Subgroup.closure ({z, e.u} : Set G) ∈ signalizerFunctorEk 2 2 B :=
    closure_pair_mem_signalizer hzB huB hz2 hu2 fd.hz.ne_one fd.hu1 fd.huz.symm fd.comm_zu
  have hF₂ : Subgroup.closure ({z, t} : Set G) ∈ signalizerFunctorEk 2 2 B :=
    closure_pair_mem_signalizer hzB htB hz2 ht2 fd.hz.ne_one fd.ht.ne_one fd.t_ne_z.symm hzt
  have hEL : exactLayer (𝒞 K) z = ⨆ N ∈ centMembers (𝒞 K) z, N := by
    rw [exactLayer_eq_iSup, exactFamily_eq_centMembers_of_exact S.exact S.inClass.classical]
  unfold CentralizerGenerationStar
  refine le_sup_of_le_right (hEL.le.trans ?_)
  refine iSup₂_le fun N hN => ?_
  have hNY : N ≤ exactLayer (𝒞 K) z :=
    (le_centLayer hN).trans (centLayer_le_exactLayer S.inClass.classical)
  have hNz : N ≤ Subgroup.centralizer ({z} : Set G) := hN.2
  have hKz : K ≤ Subgroup.centralizer ({z} : Set G) := le_centralizer_of_isClassicalMember S.cls
  by_cases hNKT : N = K ∨ N = T
  · have hNt : N ≤ Subgroup.centralizer ({t} : Set G) := by
      intro n hn
      rw [Subgroup.mem_centralizer_singleton_iff]
      rcases hNKT with rfl | rfl
      · exact (hJK t fd.ht.mem n hn).symm
      · exact (hJT t fd.ht.mem n hn).symm
    exact le_iSup₂_of_le _ hF₂ (le_inf (le_centralizer_pair hNz hNt) hNY)
  · push Not at hNKT
    have hNu : N ≤ Subgroup.centralizer ({e.u} : Set G) :=
      (e.mem_centralizingMembers_u hN.1 (hKiso N hN hNKT.1).symm
        (hTiso N hN hNKT.2).symm).2
    exact le_iSup₂_of_le _ hF₁ (le_inf (le_centralizer_pair hNz hNu) hNY)

end Side

section Link

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {tY : StatedLieTag} {nY : ℕ}

theorem link_core (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : InClass p f Ω) (hex : ExactMembers Ω)
    {z₀ t₀ : G} (hP1 : LocalOddCentral Ω {z₀}) (rf : TwinRowFacts p f tY nY)
    (d : ShapeDictT2 p f tY nY Ω z₀) {K₀ T₀ J₀ : Subgroup G}
    (hK : K₀ ∈ centralizingMembers Ω {z₀}) (hT : T₀ ∈ centralizingMembers Ω {z₀}) (hKT : K₀ ≠ T₀)
    (hKiso : ∀ N ∈ centralizingMembers Ω {z₀}, N ≠ K₀ → Commutes K₀ N)
    (hTiso : ∀ N ∈ centralizingMembers Ω {z₀}, N ≠ T₀ → Commutes T₀ N)
    (hJ : J₀ ∈ centralizingMembers Ω {z₀}) (hJK : J₀ ≠ K₀) (hJT : J₀ ≠ T₀)
    (hKcls : IsClassicalMember p f K₀ z₀) (hTcls : IsClassicalMember p f T₀ z₀)
    (hJcls : IsClassicalMember p f J₀ t₀) {N : Subgroup G} (hN : N ∈ centralizingMembers Ω {z₀})
    {w : G} (hw : IsClassicalMember p f N w) :
    w = z₀ ∨ ∃ y : G, y ∈ locLayer Ω z₀ ∧ w = y * t₀ * y⁻¹ := by
  have hUw := ConnectedA2.isUniqueInvolution_of_isClassicalMember hp hq hw
  by_cases hNK : N = K₀
  · subst hNK
    exact Or.inl (hUw.eq (ConnectedA2.isUniqueInvolution_of_isClassicalMember hp hq hKcls))
  by_cases hNT : N = T₀
  · subst hNT
    exact Or.inl (hUw.eq (ConnectedA2.isUniqueInvolution_of_isClassicalMember hp hq hTcls))
  obtain ⟨y, hy, hconj⟩ := link_big hΩ hex hP1 rf d hK hT hKT hKiso hTiso hJ hJK hJT hN hNK hNT
  refine Or.inr ⟨y, hy, ?_⟩
  have h1 : IsClassicalMember p f N (y * t₀ * y⁻¹) := hconj ▸ hJcls.conj y
  exact hUw.eq (ConnectedA2.isUniqueInvolution_of_isClassicalMember hp hq h1)

theorem linkStar_of_core (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : HypOmegaMod p f Ω)
    (hex : ExactMembers Ω) {A : Subgroup G} {S' : Set (Subgroup G)} {a : G} (haA : a ∈ A)
    {K₁ : Subgroup G} (hK₁ : K₁ ∈ S') (hK₁a : IsClassicalMember p f K₁ a)
    (core : ∀ N ∈ centralizingMembers Ω {a}, ∀ w : G, IsClassicalMember p f N w →
      ∃ K' ∈ S', ∃ z' ∈ A, IsClassicalMember p f K' z' ∧ ∃ h ∈ exactLayer Ω a,
        w = h * z' * h⁻¹) :
    InvolutionLinkStar p f Ω A S' a := by
  intro N hN w hw hdisj
  have key : ActsTrivOnQuot N a ∨ w = a := by
    rcases hdisj with h | ⟨L', hL', hL'a, hL'w⟩
    · exact Or.inl h
    · rcases actsTriv_or_eq hp hq hΩ hN hL' hw hL'a hL'w with h | h
      · exact Or.inr h
      · exact Or.inl h
  rcases key with htq | hwa
  · have hNtq : N ∈ tqMembers Ω a := ⟨hN, mem_trivialOnQuot_iff_actsTrivOnQuot.mpr htq⟩
    have hNc : N ∈ centMembers Ω a := by
      rw [← tqMembers_eq_centMembers_of_exact hex]
      exact hNtq
    exact core N hNc w hw
  · exact ⟨K₁, hK₁, a, haA, hK₁a, 1, one_mem _, by rw [hwa]; group⟩

end Link

section LinkZT

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {K T J : Subgroup G} {z t : G}
  {tY : StatedLieTag} {nY : ℕ}

theorem link_z (S : RouteDSetup p f K z) (hΩ : HypOmegaMod p f (𝒞 K))
    (rf : TwinRowFacts p f tY nY) (d : ShapeDictT2 p f tY nY (𝒞 K) z) (e : TwinElt K T z)
    (hT : T ∈ centralizingMembers (𝒞 K) {z})
    (hKT : K ≠ T) (hKiso : ∀ N ∈ centralizingMembers (𝒞 K) {z}, N ≠ K → Commutes K N)
    (hTiso : ∀ N ∈ centralizingMembers (𝒞 K) {z}, N ≠ T → Commutes T N)
    (clsT : IsClassicalMember p f T z) (hJ : J ∈ centralizingMembers (𝒞 K) {z}) (hJK : J ≠ K)
    (hJT : J ≠ T) (hJt : IsClassicalMember p f J t) :
    InvolutionLinkStar p f (𝒞 K) (Subgroup.closure ({z, e.u, t} : Set G))
      ({K, J} : Set (Subgroup G))
      z := by
  have hK : K ∈ centralizingMembers (𝒞 K) {z} :=
    ⟨CoreAssembly.mem_conjClass_self K, le_centralizer_of_isClassicalMember S.cls⟩
  have hzB : z ∈ Subgroup.closure ({z, e.u, t} : Set G) := Subgroup.subset_closure (by simp)
  have htB : t ∈ Subgroup.closure ({z, e.u, t} : Set G) := Subgroup.subset_closure (by simp)
  refine linkStar_of_core S.odd S.five hΩ S.exact hzB (Set.mem_insert _ _) S.cls ?_
  intro N hN w hw
  rcases link_core S.odd S.five S.inClass S.exact S.p1 rf d hK hT hKT hKiso hTiso hJ hJK hJT
      S.cls clsT hJt hN hw with hwz | ⟨y, hy, hwy⟩
  · exact ⟨K, Set.mem_insert _ _, z, hzB, S.cls, 1, one_mem _, by rw [hwz]; group⟩
  · exact ⟨J, Set.mem_insert_of_mem _ rfl, t, htB, hJt, y,
      centLayer_le_exactLayer S.inClass.classical hy, hwy⟩

theorem link_t (S : RouteDSetup p f K z) (hcen : Subgroup.center G = ⊥)
    (hΩ : HypOmegaMod p f (𝒞 K)) (hD4 : tY ≠ .trialityD4) (rf : TwinRowFacts p f tY nY)
    (hshape : LocalShapeT p f 2 tY nY (𝒞 K) z) (e : TwinElt K T z)
    (fd : TwinFrameData (𝒞 K) K T z e.u J t) (hT : T ∈ centralizingMembers (𝒞 K) {z})
    (hKT : K ≠ T) (hKiso : ∀ N ∈ centralizingMembers (𝒞 K) {z}, N ≠ K → Commutes K N)
    (hTiso : ∀ N ∈ centralizingMembers (𝒞 K) {z}, N ≠ T → Commutes T N)
    (clsT : IsClassicalMember p f T z) (hJ : J ∈ centralizingMembers (𝒞 K) {z}) (hJK : J ≠ K)
    (hJt : IsClassicalMember p f J t) :
    InvolutionLinkStar p f (𝒞 K) (Subgroup.closure ({z, e.u, t} : Set G))
      ({K, J} : Set (Subgroup G))
      t := by
  have hzB : z ∈ Subgroup.closure ({z, e.u, t} : Set G) := Subgroup.subset_closure (by simp)
  have htB : t ∈ Subgroup.closure ({z, e.u, t} : Set G) := Subgroup.subset_closure (by simp)
  have hUz := ConnectedA2.isUniqueInvolution_of_isClassicalMember S.odd S.five S.cls
  have hUt := ConnectedA2.isUniqueInvolution_of_isClassicalMember S.odd S.five hJt
  obtain ⟨g, hg0⟩ := hJ.1
  have hg : conjSub g K = J := hg0
  have hgz : t = g * z * g⁻¹ := by
    have h1 := hUz.conj g
    rw [hg] at h1
    exact hUt.eq h1
  have hΩc : centralizingMembers (𝒞 K) {t} = conjSub g '' centralizingMembers (𝒞 K) {z} := by
    rw [hgz]
    exact centralizingMembers_conj S.inClass.conjInvariant g z
  have hshape_t : LocalShapeT p f 2 tY nY (𝒞 K) t := by
    have := hshape.conj S.inClass.conjInvariant g
    rwa [← hgz] at this
  have hP1t : LocalOddCentral (𝒞 K) {t} := by
    have h1 := (S.of_mem_conjClass hJ.1 hJt).p1
    rwa [conjClass_eq_of_mem hJ.1] at h1
  obtain ⟨dt⟩ := LocalShapeT.nonempty_dictT2 hD4 rf.fsc S.inClass hJ.1 hJt hshape_t
  have hT'cls : IsClassicalMember p f (conjSub g T) t := by
    have := clsT.conj g
    rwa [← hgz] at this
  have hT'mem : conjSub g T ∈ centralizingMembers (𝒞 K) {t} := by
    rw [hΩc]
    exact ⟨T, hT, rfl⟩
  have hJT' : J ≠ conjSub g T := by
    intro h
    apply hKT
    have h1 : conjSub g K = conjSub g T := hg.trans h
    have h2 := congrArg (conjSub g⁻¹) h1
    rwa [conjSub_inv_conjSub, conjSub_inv_conjSub] at h2
  have hT'iso : ∀ N ∈ centralizingMembers (𝒞 K) {t}, N ≠ conjSub g T →
      Commutes (conjSub g T) N := by
    intro N hN hne
    rw [hΩc] at hN
    obtain ⟨N₁, hN₁, rfl⟩ := hN
    have hne' : N₁ ≠ T := fun h => hne (by rw [h])
    exact (hTiso N₁ hN₁ hne').conjSub g
  have hJiso : ∀ N ∈ centralizingMembers (𝒞 K) {t}, N ≠ J → Commutes J N :=
    fun N hN hne => (S.cp_at_member hcen hJ.1 hJt hN).resolve_right hne
  have hKt : K ∈ centralizingMembers (𝒞 K) {t} := by
    refine ⟨CoreAssembly.mem_conjClass_self K, fun k hk => ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact hKiso J hJ hJK k hk t hJt.mem
  have hKT'ne : K ≠ conjSub g T := by
    intro h
    have h2 : IsUniqueInvolution K t := by
      rw [h]
      exact ConnectedA2.isUniqueInvolution_of_isClassicalMember S.odd S.five hT'cls
    exact fd.t_ne_z (hUz.eq h2).symm
  have hKJ : K ≠ J := fun h => hJK h.symm
  have hJt' : J ∈ centralizingMembers (𝒞 K) {t} :=
    ⟨hJ.1, le_centralizer_of_isClassicalMember hJt⟩
  refine linkStar_of_core S.odd S.five hΩ S.exact htB (Set.mem_insert_of_mem _ rfl) hJt ?_
  intro N hN w hw
  rcases link_core S.odd S.five S.inClass S.exact hP1t rf dt hJt' hT'mem hJT' hJiso hT'iso hKt hKJ
      hKT'ne hJt hT'cls S.cls hN hw with hwt | ⟨y, hy, hwy⟩
  · exact ⟨J, Set.mem_insert_of_mem _ rfl, t, htB, hJt, 1, one_mem _, by rw [hwt]; group⟩
  · exact ⟨K, Set.mem_insert _ _, z, hzB, S.cls, y, centLayer_le_exactLayer S.inClass.classical hy,
      hwy⟩

theorem exists_twin_at_t (S : RouteDSetup p f K z)
    (hT : T ∈ centralizingMembers (𝒞 K) {z}) (hKT : K ≠ T)
    (hKiso : ∀ N ∈ centralizingMembers (𝒞 K) {z}, N ≠ K → Commutes K N)
    (hTiso : ∀ N ∈ centralizingMembers (𝒞 K) {z}, N ≠ T → Commutes T N)
    (clsT : IsClassicalMember p f T z) (hJ : J ∈ centralizingMembers (𝒞 K) {z}) (hJK : J ≠ K)
    (hJT : J ≠ T) (hJt : IsClassicalMember p f J t) (htz : t ≠ z) :
    ∃ J' : Subgroup G, J' ∈ 𝒞 K ∧ J' ≠ J ∧ IsClassicalMember p f J' t ∧ Commutes J J' ∧
      Commutes J' K ∧ Commutes J' T := by
  have hUz := ConnectedA2.isUniqueInvolution_of_isClassicalMember S.odd S.five S.cls
  have hUt := ConnectedA2.isUniqueInvolution_of_isClassicalMember S.odd S.five hJt
  have hUT := ConnectedA2.isUniqueInvolution_of_isClassicalMember S.odd S.five clsT
  obtain ⟨g, hg0⟩ := hJ.1
  have hg : conjSub g K = J := hg0
  have hgz : t = g * z * g⁻¹ := by
    have h1 := hUz.conj g
    rw [hg] at h1
    exact hUt.eq h1
  have hΩc : centralizingMembers (𝒞 K) {t} = conjSub g '' centralizingMembers (𝒞 K) {z} := by
    rw [hgz]
    exact centralizingMembers_conj S.inClass.conjInvariant g z
  have hT'cls : IsClassicalMember p f (conjSub g T) t := by
    have := clsT.conj g
    rwa [← hgz] at this
  have hJT' : J ≠ conjSub g T := by
    intro h
    apply hKT
    have h1 : conjSub g K = conjSub g T := hg.trans h
    have h2 := congrArg (conjSub g⁻¹) h1
    rwa [conjSub_inv_conjSub, conjSub_inv_conjSub] at h2
  have hT'iso : ∀ N ∈ centralizingMembers (𝒞 K) {t}, N ≠ conjSub g T →
      Commutes (conjSub g T) N := by
    intro N hN hne
    rw [hΩc] at hN
    obtain ⟨N₁, hN₁, rfl⟩ := hN
    have hne' : N₁ ≠ T := fun h => hne (by rw [h])
    exact (hTiso N₁ hN₁ hne').conjSub g
  have hJt' : J ∈ centralizingMembers (𝒞 K) {t} :=
    ⟨hJ.1, le_centralizer_of_isClassicalMember hJt⟩
  have hKt : K ∈ centralizingMembers (𝒞 K) {t} := by
    refine ⟨CoreAssembly.mem_conjClass_self K, fun k hk => ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact hKiso J hJ hJK k hk t hJt.mem
  have hTt : T ∈ centralizingMembers (𝒞 K) {t} := by
    refine ⟨hT.1, fun k hk => ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact hTiso J hJ hJT k hk t hJt.mem
  have hKne : K ≠ conjSub g T := by
    intro h
    have h2 : IsUniqueInvolution K t := by
      rw [h]
      exact ConnectedA2.isUniqueInvolution_of_isClassicalMember S.odd S.five hT'cls
    exact htz (hUz.eq h2).symm
  have hTne : T ≠ conjSub g T := by
    intro h
    have h2 : IsUniqueInvolution T t := by
      rw [h]
      exact ConnectedA2.isUniqueInvolution_of_isClassicalMember S.odd S.five hT'cls
    exact htz (hUT.eq h2).symm
  exact ⟨conjSub g T, S.inClass.conjInvariant g T hT.1, fun h => hJT' h.symm, hT'cls,
    (hT'iso J hJt' hJT').symm, hT'iso K hKt hKne, hT'iso T hTt hTne⟩

end LinkZT

section FrameSide

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {K T J : Subgroup G} {z t : G}
  {tY : StatedLieTag} {nY : ℕ}

theorem frameSide_of (S : RouteDSetup p f K z) (hcen : Subgroup.center G = ⊥)
    (hΩ : HypOmegaMod p f (𝒞 K)) (hD4 : tY ≠ .trialityD4) (rf : TwinRowFacts p f tY nY)
    (hshape : LocalShapeT p f 2 tY nY (𝒞 K) z) (e : TwinElt K T z)
    (fd : TwinFrameData (𝒞 K) K T z e.u J t) (hT : T ∈ centralizingMembers (𝒞 K) {z})
    (hKT : K ≠ T) (hKiso : ∀ N ∈ centralizingMembers (𝒞 K) {z}, N ≠ K → Commutes K N)
    (hTiso : ∀ N ∈ centralizingMembers (𝒞 K) {z}, N ≠ T → Commutes T N)
    (clsT : IsClassicalMember p f T z) (hJ : J ∈ centralizingMembers (𝒞 K) {z}) (hJK : J ≠ K)
    (hJT : J ≠ T) (hJt : IsClassicalMember p f J t)
    (hGenT : CentralizerGenerationStar (𝒞 K) (Subgroup.closure ({z, e.u, t} : Set G)) t) :
    FrameSideTwoStar p f (𝒞 K) (Subgroup.closure ({z, e.u, t} : Set G))
      ({K, J} : Set (Subgroup G)) := by
  have hzB : z ∈ Subgroup.closure ({z, e.u, t} : Set G) := Subgroup.subset_closure (by simp)
  have htB : t ∈ Subgroup.closure ({z, e.u, t} : Set G) := Subgroup.subset_closure (by simp)
  have hUz := ConnectedA2.isUniqueInvolution_of_isClassicalMember S.odd S.five S.cls
  have hUt := ConnectedA2.isUniqueInvolution_of_isClassicalMember S.odd S.five hJt
  have hJKc : Commutes J K := (hKiso J hJ hJK).symm
  have hJTc : Commutes J T := (hTiso J hJ hJT).symm
  obtain ⟨d⟩ := LocalShapeT.nonempty_dictT2 hD4 rf.fsc S.inClass
    (CoreAssembly.mem_conjClass_self K) S.cls hshape
  have hGz := gen_z S hΩ e fd hT hKiso hTiso hJKc hJTc
  have hLz := link_z S hΩ rf d e hT hKT hKiso hTiso clsT hJ hJK hJT hJt
  have hLt := link_t S hcen hΩ hD4 rf hshape e fd hT hKT hKiso hTiso clsT hJ hJK hJt
  exact
    { elem := twinFrame_isElemAbelian S.odd hΩ fd
      card := (twinFrame_natCard_eight S.odd S.five hΩ fd).ge
      subset := by
        rintro M (rfl | rfl)
        · exact CoreAssembly.mem_conjClass_self _
        · exact hJ.1
      nonempty := ⟨K, Set.mem_insert _ _⟩
      involution := by
        rintro M (rfl | rfl)
        · exact ⟨z, hzB, S.cls⟩
        · exact ⟨t, htB, hJt⟩
      generation := by
        rintro a - ⟨M, (rfl | rfl), hMa⟩
        · rw [(ConnectedA2.isUniqueInvolution_of_isClassicalMember S.odd S.five hMa).eq hUz]
          exact hGz
        · rw [(ConnectedA2.isUniqueInvolution_of_isClassicalMember S.odd S.five hMa).eq hUt]
          exact hGenT
      link := by
        rintro a - ⟨M, (rfl | rfl), hMa⟩
        · rw [(ConnectedA2.isUniqueInvolution_of_isClassicalMember S.odd S.five hMa).eq hUz]
          exact hLz
        · rw [(ConnectedA2.isUniqueInvolution_of_isClassicalMember S.odd S.five hMa).eq hUt]
          exact hLt }

theorem rankTwoSpan_eq_top_of {B : Subgroup G} {S' : Set (Subgroup G)}
    (S : RouteDSetup p f K z) (hframe : FrameSideTwoStar p f (𝒞 K) B S') : rankTwoSpan B = ⊤ :=
  rankTwoSpan_eq_top_of_dConnected_star S.odd S.five S.inClass hframe
    (dConnected_of_omegaConnected (omegaConnected_of_routeD S.conn))

end FrameSide

end CFSG.ClassicalInvolution.RouteD.TwinY
