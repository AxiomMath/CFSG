module

public import CFSG.ClassicalInvolution.SmallCases.NDBStmt
public import CFSG.ClassicalInvolution.SmallCases.DSplitBoot
import CFSG.ClassicalInvolution.ModelFacts.CommutingFundamentalTwAll
import CFSG.ClassicalInvolution.Balance.LayerGenerationPairFinalAll
import CFSG.ClassicalInvolution.Balance.Q27FuzzyBalance
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
public import Certificates.Certificate76
public import Certificates.Certificate77
public import Certificates.Certificate78
public import Certificates.Certificate79
public import Certificates.Certificate80
public import Certificates.Certificate81
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate115
public import Certificates.Certificate116
public import Certificates.Certificate117
public import Certificates.Certificate118
public import Certificates.Certificate119
public import Certificates.Certificate120
public import Certificates.Certificate121
public import Certificates.Certificate122
public import Certificates.Certificate123
public import Certificates.Certificate3951
public import Certificates.Certificate3952

public section

namespace CFSG.ClassicalInvolution.NDB

open CFSG.Open CFSG.Assembly.Dichotomy CFSG.ComponentClassification CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Generic.DeltaClosure
  CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.ClassicalInvolution.Balance.Q27 CFSG.ClassicalInvolution.Disconnected

local notation "𝒞" => Generic.CoreAssembly.conjClass

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] [IsSimpleGroup G]

namespace FuzzySeed

theorem frameAdj_of_fuzzySeed (hnab : ∃ x y : G, x * y ≠ y * x) (hp2 : p ≠ 2)
    (hq : 5 ≤ p ^ f) {K : Subgroup G} {z : G} (hz : IsClassicalMember p f K z)
    (hBelow : CITBelowU p f (Nat.card G)) {A₀ : Subgroup G}
    (hseed : Theorem5.FuzzyFrameOn p f (𝒞 K) A₀) {M N : Subgroup G} (hM : M ∈ 𝒞 K)
    (hN : N ∈ 𝒞 K) {zM zN : G} (hMc : IsClassicalMember p f M zM)
    (hNc : IsClassicalMember p f N zN) (hE : ActsTrivOnQuot N zM) (hne : zM ≠ zN) :
    Theorem5.FrameAdj (Theorem5.fuzzyFrames p f (𝒞 K)) (Theorem5.fuzzyVertices p f (𝒞 K))
      zM zN := by
  have hf : 0 < f := Nat.pos_of_ne_zero (by rintro rfl; simp at hq)
  have hK : 𝒞 K = canonClass p f K := (canonClass_eq_conjClass hz).symm
  rw [hK] at hM hN hseed ⊢
  have hinv := conjInvariant_canonClass (p := p) (f := f) K
  have hcan := canonClass_subset (p := p) (f := f) K
  have haN : zM ∈ trivialOnQuot N := mem_trivialOnQuot_iff_actsTrivOnQuot.mpr hE
  have hua : zN ≠ zM := hne.symm
  obtain ⟨ld⟩ := exists_linkDataFree hnab hp2 hq hBelow hinv hM hMc
  obtain ⟨z₀, hz₀⟩ := Theorem5.FuzzyFrameOn.exists_vertex hseed
  have hz₀' := hz₀
  obtain ⟨-, J₀, hJ₀𝒞, hJ₀, -⟩ := hz₀'
  obtain ⟨h, hh⟩ := exists_conj_of_mem_canonClass hp2 hf hJ₀𝒞 hJ₀ hM hMc
  have hA₁ := Theorem5.FuzzyFrameOn.map hinv hseed h
  have haA₁ := Theorem5.mem_fuzzyVertices_map hinv hz₀ h
  rw [hh] at haA₁
  obtain ⟨J, t, N₁, u₁, hb⟩ := exists_frameBasis hA₁ haA₁
  have ha2 : zM * zM = 1 := hb.sq hb.aB
  obtain ⟨cJ, hcJ⟩ := ld.sec.exists_comp ld.D hb.linkJ
  obtain ⟨c₁, hc₁⟩ := ld.sec.exists_comp ld.D hb.linkN
  obtain ⟨c₀, hc₀⟩ := ld.sec.exists_comp ld.D (triangleResidual_mem_linkFamily hN hNc haN)
  by_cases h0J : c₀ = cJ
  · obtain ⟨B, hB, haB, huB⟩ := exists_frame_of_comp_free ld hp2 hq hinv hb hN hNc haN
      (j := cJ) hcJ (by rw [← h0J]; exact hc₀)
    exact ⟨B, hB, haB, huB⟩
  by_cases h0N : c₀ = c₁
  · obtain ⟨B, hB, haB, huB⟩ := exists_frame_of_comp_free ld hp2 hq hinv hb.swap hN hNc haN
      (j := c₁) hc₁ (by rw [← h0N]; exact hc₀)
    exact ⟨B, hB, haB, huB⟩
  by_cases hcl : SameClass zM t zN
  · have hcl' : ¬ SameClass zM u₁ zN := fun h => hb.not_sameClass (hcl.trans ha2 (h.symm ha2))
    obtain ⟨B, hB, haB, huB⟩ := exists_frame_of_cross_free ld hp2 hq hinv hcan hM hMc hb.memN
      hb.clsN (hb.tqN hb.aB) hb.u_ne_a hN hNc haN hua (j₁ := c₁) (j₂ := c₀) (Ne.symm h0N) hc₁
      hc₀ hcl'
    exact ⟨B, hB, haB, huB⟩
  · obtain ⟨B, hB, haB, huB⟩ := exists_frame_of_cross_free ld hp2 hq hinv hcan hM hMc hb.memJ
      hb.clsJ (hb.tqJ hb.aB) hb.ta hN hNc haN hua (j₁ := cJ) (j₂ := c₀) (Ne.symm h0J) hcJ hc₀
      hcl
    exact ⟨B, hB, haB, huB⟩

end FuzzySeed

theorem alphaCore_eq_bot_of_fuzzySeed (hnab : ∃ x y : G, x * y ≠ y * x) (hp2 : p ≠ 2)
    (hq : 5 ≤ p ^ f) {K : Subgroup G} {z : G} (hz : IsClassicalMember p f K z)
    (hBelow : CITBelowU p f (Nat.card G)) (hD : DConnected (𝒞 K)) {A₀ : Subgroup G}
    (hseed : Theorem5.FuzzyFrameOn p f (𝒞 K) A₀) :
    ∀ A ∈ Theorem5.fuzzyFrames p f (𝒞 K), ∀ F ∈ signalizerFunctorEk 2 2 A, alphaCore F = ⊥ := by
  have hf : 0 < f := Nat.pos_of_ne_zero (by rintro rfl; simp at hq)
  have hΩ : InClass p f (𝒞 K) := inClass_conjugates hz
  have hinv : ConjInvariant (𝒞 K) := hΩ.conjInvariant
  have hmap : ∀ A ∈ Theorem5.fuzzyFrames p f (𝒞 K), ∀ g : G,
      A.map (MulAut.conj g).toMonoidHom ∈ Theorem5.fuzzyFrames p f (𝒞 K) :=
    fun A hA g => Theorem5.FuzzyFrameOn.map hinv hA g
  have hchain := tqChain_of_dConnected hp2 hq hz hD
  have hedge : ∀ M ∈ 𝒞 K, ∀ N ∈ 𝒞 K, ∀ zM zN : G,
      IsClassicalMember p f M zM → IsClassicalMember p f N zN → tqAdjSymm p f M N → zM ≠ zN →
      Theorem5.FrameAdj (Theorem5.fuzzyFrames p f (𝒞 K))
        (Theorem5.fuzzyVertices p f (𝒞 K)) zM zN := by
    intro M hM N hN zM zN hMc hNc hE hne
    rcases hE with ⟨a, ha, hNa⟩ | ⟨a, ha, hMa⟩
    · have : a = zM := hMc.eq_of_isCentralInvolution hp2 hf ha.isCentralInvolution
      subst this
      exact FuzzySeed.frameAdj_of_fuzzySeed hnab hp2 hq hz hBelow hseed hM hN hMc hNc hNa hne
    · have : a = zN := hNc.eq_of_isCentralInvolution hp2 hf ha.isCentralInvolution
      subst this
      obtain ⟨B, hB, h1, h2⟩ := FuzzySeed.frameAdj_of_fuzzySeed hnab hp2 hq hz hBelow hseed hN
        hM hNc hMc hMa hne.symm
      exact ⟨B, hB, h2, h1⟩
  have hcon := Theorem5.shareFour_connected_of_vertexGraph_modOdd
    (𝒯 := Theorem5.fuzzyFrames p f (𝒞 K)) hmap
    (fun A hA => by
      obtain ⟨J, w, -, -, hel, hcard, -⟩ := hA
      exact ⟨hel, hcard⟩)
    (Theorem5.fuzzyVertices p f (𝒞 K)) (fun A _ w hw => hw.1)
    (fun A hA => hA.exists_vertex)
    (fun A _ A' _ a ha a' ha' => by
      obtain ⟨-, J, hJ, hJa, -⟩ := ha
      obtain ⟨-, J', hJ', hJ'a, -⟩ := ha'
      exact Theorem5.reflTransGen_frameAdj_of_adj hp2 hf (fun M N => tqAdjSymm p f M N)
        hΩ.classical hchain (Theorem5.fuzzyVertices p f (𝒞 K)) hedge hJ hJ' hJa hJ'a)
    (fun a A hA A' hA' ha ha' =>
      linkMove_connected_noConn (ModelFacts.commutingFundamentalFactsFive_all hp2) hnab hp2 hq
        hz hBelow a hA hA' ha ha')
  exact Theorem5.alphaCore_eq_bot_of_connected_frames
    (componentClassificationOddCore_eq_bot_of_simple hnab) hmap
    (fun A hA => rankThreeBalance_of_fuzzyFrameOn_hybrid_free hnab hp2 hq hBelow hA
      (layerGenerationHybrid p)) hcon

theorem bootData_of_fuzzyFrameOn (hnab : ∃ x y : G, x * y ≠ y * x) (hp2 : p ≠ 2)
    (hq : 5 ≤ p ^ f) {K : Subgroup G} {z : G} (hz : IsClassicalMember p f K z)
    (hBelow : CITBelowU p f (Nat.card G)) (hD : DConnected (𝒞 K)) {A : Subgroup G}
    (hA : Theorem5.FuzzyFrameOn p f (𝒞 K) A) : CoreAssembly.BootData p f (𝒞 K) := by
  have hα := alphaCore_eq_bot_of_fuzzySeed hnab hp2 hq hz hBelow hD hA
  have hA' := hA
  obtain ⟨-, -, -, -, hel, hcard, -⟩ := hA'
  obtain ⟨J₁, J₂, J₃, z₁, z₂, z₃, hJ₁, -, -, hT, h12, h13, -, -, hax⟩ := hA.exists_axisTriangle
  have hzA : ∀ w ∈ ({z₁, z₂, z₃} : Set G), w ∈ A := fun w hw => hax ▸ Subgroup.subset_closure hw
  have hz₁A : z₁ ∈ A := hzA z₁ (by simp)
  have hc₁ := hT.cls₁.isCentralInvolution
  have hcent : ∀ {w : G}, w ∈ A → w * w = 1 → w ≠ 1 → z₁ ≠ w → z₁ * w = w * z₁ →
      w ∈ trivialOnQuot J₁ → ∀ x ∈ J₁, w * x = x * w := by
    intro w hwA hw2 hw1 hne hcomm htq
    have hF : Subgroup.closure ({z₁, w} : Set G) ∈ signalizerFunctorEk 2 2 A := by
      refine ⟨?_, ?_⟩
      · rw [Subgroup.closure_le]
        rintro _ (rfl | hy)
        · exact hz₁A
        · rw [Set.mem_singleton_iff.mp hy]
          exact hwA
      · rw [card_closure_pair_eq_four hc₁.sq hw2 hc₁.ne_one hw1 hne hcomm]
        norm_num
    exact Theorem5.mem_centralizer_of_alphaCore_eq_bot hT.cls₁ htq hw2 hc₁.ne_one
      (hα A hA _ hF)
  have hz₂ := hcent (hzA z₂ (by simp)) hT.cls₂.isCentralInvolution.sq
    hT.cls₂.isCentralInvolution.ne_one h12 hT.comm₁₂ hT.tq₁₂
  have hz₃ := hcent (hzA z₃ (by simp)) hT.cls₃.isCentralInvolution.sq
    hT.cls₃.isCentralInvolution.ne_one h13 hT.comm₁₃ hT.tq₁₃
  refine ⟨J₁, z₁, A, hJ₁, hT.cls₁, hel, hcard, hz₁A, ?_⟩
  rw [Subgroup.le_centralizer_iff, ← hax, triangleAxis, Subgroup.closure_le]
  rintro w hw
  rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
  intro x hx
  rcases hw with rfl | rfl | rfl
  · exact (Subgroup.mem_centralizer_singleton_iff.mp
      (RouteD.le_centralizer_of_isClassicalMember hT.cls₁ hx))
  · exact (hz₂ x hx).symm
  · exact (hz₃ x hx).symm

theorem fuzzyFrameExcluded : FuzzyFrameExcluded p f := by
  intro G _ _ _ K z hS A hA
  exact hS.noBoot (bootData_of_fuzzyFrameOn hS.nonabelian hS.odd hS.five hS.member hS.below
    hS.dconn hA)

end CFSG.ClassicalInvolution.NDB
