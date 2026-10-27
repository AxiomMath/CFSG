module

public import CFSG.ClassicalInvolution.Q3.Q3KCMaxFrame
public import CFSG.ClassicalInvolution.Q3.Q3KCMaxClosure
public import CFSG.ClassicalInvolution.Q3.Q3OFSplitTri
public import CFSG.ClassicalInvolution.Q3.Q3WOdd3
public import CFSG.ClassicalInvolution.Q3.Q3NHMain
public import CFSG.ClassicalInvolution.Q3.Q3OFUnique

set_option linter.unusedSectionVars false

public section

namespace CFSG.ClassicalInvolution.Q3.Q3OF

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Generic.DeltaClosure CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Balance.Bootstrap CFSG.ClassicalInvolution.Q3.Q3NL
  CFSG.ClassicalInvolution.Q3.Q3NG CFSG.ClassicalInvolution.Q3.Q3W

section Max


variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {K : Subgroup G} {z : G}
  {K₁ K₂ M : Subgroup G} {z₁ z₂ m : G}

theorem rankThreeBalance_of_edge_third (hR : RouteD3Setup K z)
    (he : IsEdge3 (conjClass3 K) K₁ K₂ z₁ z₂) (hM : M ∈ conjClass3 K)
    (hm : IsClassicalMember3 M m) (hc₁ : Commutes K₁ M) (hc₂ : Commutes K₂ M)
    (hind : m ∉ Subgroup.closure ({z₁, z₂} : Set G)) :
    RankThreeBalance (Subgroup.closure ({z₁, z₂, m} : Set G)) ∧
      Subgroup.closure ({z₁, z₂} : Set G) ∈
        signalizerFunctorEk 2 2 (Subgroup.closure ({z₁, z₂, m} : Set G)) := by
  obtain ⟨h₁, h₂, h₃⟩ := ne_of_not_mem_pair hind
  have hnab := routeD3Setup_nonabelian hR
  have T := exactTriple_of_edge he hm hc₁ hc₂ h₁ h₂
  have hfr : FuzzyFrame3 (conjClass3 K) T.group :=
    fuzzyFrame3_of_exactTriple T h₃ ⟨he.mem₁, he.cls₁⟩ ⟨he.mem₂, he.cls₂⟩ ⟨hM, hm⟩
  have hbal : RankThreeBalance T.group :=
    Asc77.lemma52 G T.group (Q3NH.hyp51_of_fuzzyFrame hR.inClass hR.below hnab hfr)
  have hpair : Subgroup.closure ({z₁, z₂} : Set G) ≤ T.group :=
    Subgroup.closure_mono (Set.insert_subset_insert
      (Set.singleton_subset_iff.mpr (Set.mem_insert z₂ {m})))
  have hcard : Nat.card (Subgroup.closure ({z₁, z₂} : Set G)) = 4 :=
    card_closure_pair_eq_four (Q3NT.mul_self_eq_one_of_orderOf_eq_two he.cls₁.orderOf_eq_two)
      (Q3NT.mul_self_eq_one_of_orderOf_eq_two he.cls₂.orderOf_eq_two) he.cls₁.ne_one
      he.cls₂.ne_one he.ne he.comm_involutions
  exact ⟨hbal, hpair, by rw [hcard]; norm_num⟩

theorem alphaCore_edge_eq_bot_of_triple_max (hR : RouteD3Setup K z)
    (he : IsEdge3 (conjClass3 K) K₁ K₂ z₁ z₂) (hM : M ∈ conjClass3 K)
    (hm : IsClassicalMember3 M m) (hc₁ : Commutes K₁ M) (hc₂ : Commutes K₂ M)
    (hind : m ∉ Subgroup.closure ({z₁, z₂} : Set G)) :
    alphaCore (Subgroup.closure ({z₁, z₂} : Set G)) = ⊥ := by
  classical
  have hΩ := hR.inClass
  have hex := hR.setup.1
  have hIH := hR.ih
  have hnab := routeD3Setup_nonabelian hR
  have hnc : ∀ b : G, b ≠ 1 → b ∉ Subgroup.center G := fun b hb1 hbc =>
    Q3W.not_subset_center_of_ne_one hnab hb1 (Set.singleton_subset_iff.mpr hbc)
  have hconn := omegaConnected_range_conjSub hR.conn
  set F : Subgroup G := Subgroup.closure ({z₁, z₂} : Set G) with hF
  have hP : ∀ {a : G} {L : Subgroup G}, L ∈ conjClass3 K → IsClassicalMember3 L a →
      LocalOddCentral (conjClass3 K) {a} ∧ LocalOddThreeFree3 (conjClass3 K) a := by
    intro a L hL ha
    have hRL : RouteD3Setup L a := Q3TC.RouteD3Setup.of_mem_conjClass3 hR hL ha
    have hcl : conjClass3 L = conjClass3 K := Q3TC.conjClass3_eq_of_mem hL
    exact ⟨hcl ▸ hRL.setup.2, hcl ▸ Q3W.oddThreeFreeInput_proved G L a hRL⟩
  have h𝒦₀ : Q3KC.CommFamily (conjClass3 K) ({K₁, K₂, M} : Set (Subgroup G)) :=
    { subset := Set.insert_subset he.mem₁ (Set.insert_subset he.mem₂
        (Set.singleton_subset_iff.mpr hM))
      comm := by
        intro L hL L' hL' hne
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hL hL'
        rcases hL with h | h | h <;> rcases hL' with h' | h' | h' <;> subst h <;> subst h'
        · exact absurd rfl hne
        · exact he.comm
        · exact hc₁
        · exact he.comm.symm
        · exact absurd rfl hne
        · exact hc₂
        · exact hc₁.symm
        · exact hc₂.symm
        · exact absurd rfl hne }
  obtain ⟨𝒦, h𝒦₀𝒦, h𝒦, hmax⟩ := Q3KC.exists_maximal_commFamily h𝒦₀
  have hK₁ : K₁ ∈ 𝒦 := h𝒦₀𝒦 (by simp)
  have hK₂ : K₂ ∈ 𝒦 := h𝒦₀𝒦 (by simp)
  have hM𝒦 : M ∈ 𝒦 := h𝒦₀𝒦 (by simp)
  set S₀ := Q3KC.frameCommFamily (conjClass3 K) 𝒦 K₁ K₂ with hS₀
  have hKS : K₁ ∈ S₀ := Q3KC.mem_frameCommFamily_of_mem hΩ h𝒦 hK₁ hK₂ hK₁
  have hMS : M ∈ S₀ := Q3KC.mem_frameCommFamily_of_mem hΩ h𝒦 hK₁ hK₂ hM𝒦
  let H : Subgroup G := ⨆ (L : Subgroup G) (_ : L ∈ S₀) (w : G) (_ : IsClassicalMember3 L w)
    (_ : w ∉ F), rankTwoSpan (Subgroup.closure ({z₁, z₂, w} : Set G))
  have hle_H : ∀ L ∈ S₀, ∀ w : G, IsClassicalMember3 L w → w ∉ F →
      rankTwoSpan (Subgroup.closure ({z₁, z₂, w} : Set G)) ≤ H := fun L hL w hw hwF =>
    le_iSup_of_le L (le_iSup_of_le hL (le_iSup_of_le w (le_iSup_of_le hw
      (le_iSup_of_le hwF le_rfl))))
  have hz₁F : z₁ ∈ F := Subgroup.subset_closure (by simp)
  have hz₂F : z₂ ∈ F := Subgroup.subset_closure (by simp)
  have hcommS : ∀ L ∈ S₀, ∀ w : G, IsClassicalMember3 L w → w ∉ F →
      Commutes K₁ L ∧ Commutes K₂ L := by
    intro L hL w hw hwF
    rcases hL.2.2 with h | h | h
    · rw [h] at hw
      rw [involution_unique3 hw he.cls₁] at hwF
      exact absurd hz₁F hwF
    · rw [h] at hw
      rw [involution_unique3 hw he.cls₂] at hwF
      exact absurd hz₂F hwF
    · exact h
  have hgenH : ∀ L ∈ S₀, ∀ w : G, IsClassicalMember3 L w → w ∉ F →
      ∀ a ∈ Subgroup.closure ({z₁, z₂, w} : Set G), a ≠ 1 →
        centralizingLayer (conjClass3 K) {a} ≤ H := by
    intro L hL w hw hwF a haT ha1
    obtain ⟨hc₁L, hc₂L⟩ := hcommS L hL w hw hwF
    obtain ⟨h₁, h₂, h₃⟩ := ne_of_not_mem_pair hwF
    have T := exactTriple_of_edge he hw hc₁L hc₂L h₁ h₂
    have hgen := Q3KC.centralizerGenerationModOTwo_of_exactTriple hIH T h₃ he.mem₁ he.mem₂ hL.1
      he.cls₁ he.cls₂ hw haT ha1 (hnc a ha1)
    exact (centralizingLayer_le_rankTwoSpan hΩ.conjInvariant T.isElemAbelian
      (T.card_eq_eight h₃).ge haT hgen).trans (hle_H L hL w hw hwF)
  have hY : ∀ a ∈ Q3KC.frameGroup 𝒦, IsFrameInvolution3 S₀ a →
      centralizingLayer (conjClass3 K) {a} ≤ H := by
    rintro a - ⟨L₀, hL₀, ha⟩
    have ha1 := ha.ne_one
    by_cases haF : a ∈ F
    · refine hgenH M hMS m hm hind a ?_ ha1
      exact Subgroup.closure_mono (Set.insert_subset_insert
        (Set.singleton_subset_iff.mpr (Set.mem_insert z₂ {m}))) haF
    · exact hgenH L₀ hL₀ a ha haF a (Subgroup.subset_closure (by simp)) ha1
  have hlink : ∀ a ∈ Q3KC.frameGroup 𝒦, IsFrameInvolution3 S₀ a →
      InvolutionLink3 (conjClass3 K) (Q3KC.frameGroup 𝒦) S₀ a := by
    intro a ha hfa
    obtain ⟨L₀, hL₀, hLa⟩ := hfa
    exact Q3KC.involutionLink_of_lieCovers3' hΩ hIH (hnc a hLa.ne_one) (fun L hL => hL.1)
      (fun L hL => hL.2.1)
      (Q3KC.lieCovers3_of_maximal hΩ hex hP h𝒦 hmax hK₁ hK₂ ha ⟨L₀, hL₀, hLa⟩)
  have hH : H = ⊤ :=
    Q3KC.eq_top_of_frame3 hΩ (fun L hL => hL.1) ⟨K₁, hKS⟩ (fun L hL => hL.2.1) hY hlink hconn
  have hbalL : ∀ L ∈ S₀, ∀ w : G, IsClassicalMember3 L w → w ∉ F →
      RankThreeBalance (Subgroup.closure ({z₁, z₂, w} : Set G)) ∧
        F ∈ signalizerFunctorEk 2 2 (Subgroup.closure ({z₁, z₂, w} : Set G)) := by
    intro L hL w hw hwF
    obtain ⟨hc₁L, hc₂L⟩ := hcommS L hL w hw hwF
    exact rankThreeBalance_of_edge_third hR he hL.1 hw hc₁L hc₂L hwF
  have hnorm : H ≤ Subgroup.normalizer (alphaCore F : Set G) := by
    refine iSup_le fun L => iSup_le fun hL => iSup_le fun w => iSup_le fun hw =>
      iSup_le fun hwF => ?_
    obtain ⟨hbal, hFmem⟩ := hbalL L hL w hw hwF
    have h1 := Theorem5.rankTwoSpan_le_normalizer_alphaFrame hbal
    rwa [Theorem5.alphaFrame_eq_alphaCore hbal hFmem] at h1
  obtain ⟨hbalM, hFM⟩ := rankThreeBalance_of_edge_third hR he hM hm hc₁ hc₂ hind
  have hodd : Odd (Nat.card (alphaCore F)) := by
    rw [← Theorem5.alphaFrame_eq_alphaCore hbalM hFM]
    exact Theorem5.odd_card_alphaFrame hbalM
  have hnormal : (alphaCore F).Normal := by
    refine ⟨fun x hx g => ?_⟩
    have hg : g ∈ Subgroup.normalizer (alphaCore F : Set G) :=
      hnorm (hH ▸ Subgroup.mem_top g)
    exact (Subgroup.mem_normalizer_iff.mp hg x).mp hx
  have hle := CFSG.ComponentClassification.OddCore.maximal G (alphaCore F) hnormal hodd
  rw [componentClassificationOddCore_eq_bot_of_simple hnab] at hle
  exact le_bot_iff.mp hle

end Max

end CFSG.ClassicalInvolution.Q3.Q3OF
