module

public import CFSG.ClassicalInvolution.SmallCases.DSplitChain
public import CFSG.ClassicalInvolution.Balance.Q27FuzzyLinkFrames
public import CFSG.ClassicalInvolution.Balance.QNineFuzzyQuasi

public section

namespace CFSG.ClassicalInvolution.Disconnected

open CFSG.Open CFSG.Assembly.Dichotomy CFSG.ComponentClassification CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Generic.DeltaClosure
  CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.ClassicalInvolution.Balance.Q27

section Edge

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] [IsSimpleGroup G]

theorem frameAdj_of_actsTrivOnQuot (hnab : ∃ x y : G, x * y ≠ y * x) (hp2 : p ≠ 2)
    (hq : 5 ≤ p ^ f) {K : Subgroup G} {z : G} (hz : IsClassicalMember p f K z)
    (hBelow : CITBelowU p f (Nat.card G))
    (hind : CoreAssembly.IndepTriple p f (CoreAssembly.conjClass K)) {M N : Subgroup G}
    (hM : M ∈ CoreAssembly.conjClass K) (hN : N ∈ CoreAssembly.conjClass K) {zM zN : G}
    (hMc : IsClassicalMember p f M zM) (hNc : IsClassicalMember p f N zN)
    (hE : ActsTrivOnQuot N zM) (hne : zM ≠ zN) :
    Theorem5.FrameAdj (Theorem5.fuzzyFrames p f (CoreAssembly.conjClass K))
      (Theorem5.fuzzyVertices p f (CoreAssembly.conjClass K)) zM zN := by
  have hf : 0 < f := Nat.pos_of_ne_zero (by rintro rfl; simp at hq)
  have hK : CoreAssembly.conjClass K = canonClass p f K := (canonClass_eq_conjClass hz).symm
  rw [hK] at hM hN ⊢
  have hinv := conjInvariant_canonClass (p := p) (f := f) K
  have hcan := canonClass_subset (p := p) (f := f) K
  have haN : zM ∈ trivialOnQuot N := mem_trivialOnQuot_iff_actsTrivOnQuot.mpr hE
  have hua : zN ≠ zM := hne.symm
  obtain ⟨ld⟩ := exists_linkDataFree hnab hp2 hq hBelow hinv hM hMc
  obtain ⟨K', z', hK', hcomm, hel, hcard⟩ := hind
  have hAex : IndepTripleOn p f (CoreAssembly.conjClass K) (Subgroup.closure (Set.range z')) :=
    ⟨K', z', hK', hcomm, rfl, hel, hcard⟩
  have hA₀ := fuzzyFrameOn_canonClass_of_indepTripleOn hAex
  obtain ⟨z₀, hz₀⟩ := Theorem5.FuzzyFrameOn.exists_vertex hA₀
  have hz₀' := hz₀
  obtain ⟨-, J₀, hJ₀𝒞, hJ₀, -⟩ := hz₀'
  obtain ⟨h, hh⟩ := exists_conj_of_mem_canonClass hp2 hf hJ₀𝒞 hJ₀ hM hMc
  have hA₁ := Theorem5.FuzzyFrameOn.map hinv hA₀ h
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

end Edge

section Link

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] [IsSimpleGroup G]

theorem linkMove_connected_noConn (hMFC : ModelFacts.CommutingFundamentalFactsFive p)
    (hnab : ∃ x y : G, x * y ≠ y * x) (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) {K : Subgroup G} {z : G}
    (hz : IsClassicalMember p f K z) (hBelow : CITBelowU p f (Nat.card G)) (a : G)
    {A A' : Subgroup G} (hA : A ∈ Theorem5.fuzzyFrames p f (CoreAssembly.conjClass K))
    (hA' : A' ∈ Theorem5.fuzzyFrames p f (CoreAssembly.conjClass K))
    (haA : a ∈ Theorem5.fuzzyVertices p f (CoreAssembly.conjClass K) A)
    (haA' : a ∈ Theorem5.fuzzyVertices p f (CoreAssembly.conjClass K) A') :
    Relation.ReflTransGen (Theorem5.LinkMove (Theorem5.fuzzyFrames p f (CoreAssembly.conjClass K))
      (Theorem5.fuzzyVertices p f (CoreAssembly.conjClass K)) a) A A' := by
  have hK : CoreAssembly.conjClass K = canonClass p f K := (canonClass_eq_conjClass hz).symm
  rw [hK] at hA hA' haA haA' ⊢
  have hinv := conjInvariant_canonClass (p := p) (f := f) K
  have hcan := canonClass_subset (p := p) (f := f) K
  have haA0 := haA
  obtain ⟨-, M, hM𝒞, hM, -⟩ := haA0
  obtain ⟨ld⟩ := exists_linkDataFree hnab hp2 hq hBelow hinv hM𝒞 hM
  obtain ⟨J, t, N, u, hb⟩ := exists_frameBasis hA haA
  obtain ⟨J', t', N', u', hb'⟩ := exists_frameBasis hA' haA'
  have ha2 : a * a = 1 := hb.sq hb.aB
  obtain ⟨cJ, hcJ⟩ := ld.sec.exists_comp ld.D hb.linkJ
  obtain ⟨cJ', hcJ'⟩ := ld.sec.exists_comp ld.D hb'.linkJ
  obtain ⟨cN', hcN'⟩ := ld.sec.exists_comp ld.D hb'.linkN
  by_cases h1 : cJ = cJ'
  · exact reflTransGen_frameLink_of_comp_free hinv hp2 hq ld.sec ld.D hMFC hb hA' haA' cJ hb.memJ
      hb.clsJ hb.tB hb.tqJ hcJ hb'.memJ hb'.clsJ hb'.tB hb'.tqJ hb'.ta
      (by rw [h1]; exact hcJ')
  by_cases h2 : cJ = cN'
  · exact reflTransGen_frameLink_of_comp_free hinv hp2 hq ld.sec ld.D hMFC hb hA' haA' cJ hb.memJ
      hb.clsJ hb.tB hb.tqJ hcJ hb'.memN hb'.clsN hb'.uB hb'.tqN hb'.u_ne_a
      (by rw [h2]; exact hcN')
  by_cases hcl : SameClass a t t'
  · have hcl' : ¬ SameClass a t u' := fun h => hb'.not_sameClass ((hcl.symm ha2).trans ha2 h)
    exact frames_link_of_cross_free ld hp2 hq hinv hcan hMFC hb hb' hb'.memN hb'.clsN hb'.uB
      hb'.tqN hb'.u_ne_a h2 hcJ hcN' hcl'
  · exact frames_link_of_cross_free ld hp2 hq hinv hcan hMFC hb hb' hb'.memJ hb'.clsJ hb'.tB
      hb'.tqJ hb'.ta h1 hcJ hcJ' hcl

end Link

section Family

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

open CFSG.ClassicalInvolution.Balance.Theorem5 in
theorem exactMembers_and_localOddCentral_of_balancedFamilyD [IsSimpleGroup G]
    (hnab : ∃ a b : G, a * b ≠ b * a) (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : InClass p f Ω)
    (hsingle : ∃ K ∈ Ω, ∀ L ∈ Ω, ∃ g : G, L = conjSub g K) (hIH : LocalLieSystems p f Ω)
    (hchain : ∀ L ∈ Ω, ∀ L' ∈ Ω, Relation.ReflTransGen
      (fun M N : Subgroup G => N ∈ Ω ∧ tqAdjSymm p f M N) L L')
    (hlay : ∀ A' : Subgroup G, IndepTripleOn p f Ω A' → ∀ a ∈ A', a ≠ 1 →
      ComponentLayersAt Ω A' a)
    {𝒯 : Set (Subgroup G)} (hbal : ∀ A ∈ 𝒯, RankThreeBalance A)
    (hinv : ∀ A ∈ 𝒯, ∀ g : G, A.map (MulAut.conj g).toMonoidHom ∈ 𝒯)
    (hcon : ∀ A ∈ 𝒯, ∀ A' ∈ 𝒯, Relation.ReflTransGen (ShareFourIn 𝒯) A A')
    {K : Fin 3 → Subgroup G} {z : Fin 3 → G}
    (hK : ∀ i, K i ∈ Ω ∧ IsClassicalMember p f (K i) (z i))
    (hcomm : ∀ i j, i ≠ j → ∀ x ∈ K i, ∀ y ∈ K j, x * y = y * x) {A : Subgroup G}
    (hAdef : A = Subgroup.closure (Set.range z)) (hel : IsElemAbelian 2 A)
    (hcard : Nat.card A = 8) (hA : A ∈ 𝒯) (hexotic : ExoticLeviBlock p f) :
    ExactMembers Ω ∧ ∀ L ∈ Ω, ∀ w : G, IsClassicalMember p f L w → LocalOddCentral Ω {w} := by
  by_cases h9 : p ^ f = 9
  · have hf : 0 < f := by
      rcases Nat.eq_zero_or_pos f with rfl | h
      · simp at hq
      · exact h
    have hO := componentClassificationOddCore_eq_bot_of_simple hnab
    have hα := alphaCore_eq_bot_of_connected_frames hO hinv hbal hcon
    have hΔ := deltaCore_eq_bot_of_connected_frames hO hinv hbal hcon
    obtain ⟨F₀, hF₀⟩ := exists_mem_signalizerFunctorEk (hbal A hA)
    have hK0A : K 0 ≤ Subgroup.centralizer (A : Set G) := by
      rw [hAdef]
      exact triple_centralizes hK hcomm 0
    have hq0 : CFSG.Open.IsQuasisimple (K 0) :=
      isQuasisimple_of_member_of_deltaCore_eq_bot hnab hp2 hq hΩ hIH (hK 0).1 (hK 0).2
        (CFSG.SignalizerFunctor.Helpers.elementary_abelian_of_le 2 hel hF₀.1)
        (hK0A.trans (Subgroup.centralizer_le hF₀.1)) (hΔ A hA F₀ hF₀)
    have hqs := isQuasisimple_of_mem_of_single_class hsingle (hK 0).1 hq0
    have hP1 : LocalOddCentral Ω {z 0} :=
      localOddCentral_of_indepTriple_pair_of_isQuasisimple hnab hp2 hq hΩ hIH hqs hlay hK hcomm
        hAdef hel hcard hF₀ (hα A hA F₀ hF₀) (i := 0) (j := 1) (by decide) (x := z 0)
        (Subgroup.subset_closure (by simp)) (hK 0).2.ne_one
    have hP1all := localOddCentral_of_classicalMember hp2 hf hΩ hsingle (hK 0).1 (hK 0).2 hP1
    have hconn := omegaConnected_of_tqChain hnab hΩ hIH hqs hP1all hchain
    exact ⟨exactMembers_of_connected_nine hnab hp2 hq h9 hΩ hsingle hIH hconn hP1all hexotic,
      hP1all⟩
  · exact exactMembers_and_localOddCentral_of_balancedFamily hnab hp2 hq h9 hΩ hsingle hIH hlay
      hbal hinv hcon hK hcomm hAdef hel hcard hA

end Family

section Boot

variable {p f : ℕ} [Fact p.Prime]

@[expose] def BootTripleD (p f : ℕ) [Fact p.Prime] : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ x y : G, x * y ≠ y * x) →
    p ≠ 2 → 5 ≤ p ^ f → ∀ (K : Subgroup G) (z : G), IsClassicalMember p f K z →
      CITBelowU p f (Nat.card G) → DConnected (CoreAssembly.conjClass K) →
      CoreAssembly.IndepTriple p f (CoreAssembly.conjClass K) →
      ExactMembers (CoreAssembly.conjClass K) ∧ LocalOddCentral (CoreAssembly.conjClass K) {z}

theorem bootTripleD (hmodel : LayerGenerationHybrid p)
    (hMFC : ModelFacts.CommutingFundamentalFactsFive p) (hexotic : ExoticLeviBlock p f) :
    BootTripleD p f := by
  intro G _ _ _ hnab hp2 hq K z hz hBelow hD hind
  have hf : 0 < f := Nat.pos_of_ne_zero (by rintro rfl; simp at hq)
  have hΩ : InClass p f (CoreAssembly.conjClass K) := inClass_conjugates hz
  have hIH := localLieSystems_of_citBelowU hΩ hBelow
  have hind' := hind
  obtain ⟨K', z', hK', hcomm, hel, hcard⟩ := hind
  have hAex : IndepTripleOn p f (CoreAssembly.conjClass K) (Subgroup.closure (Set.range z')) :=
    ⟨K', z', hK', hcomm, rfl, hel, hcard⟩
  have hinv : ConjInvariant (CoreAssembly.conjClass K) := hΩ.conjInvariant
  have hA : Subgroup.closure (Set.range z') ∈
      Theorem5.fuzzyFrames p f (CoreAssembly.conjClass K) :=
    Theorem5.fuzzyFrameOn_of_indepTripleOn hAex
  have hmap : ∀ A ∈ Theorem5.fuzzyFrames p f (CoreAssembly.conjClass K), ∀ g : G,
      A.map (MulAut.conj g).toMonoidHom ∈ Theorem5.fuzzyFrames p f (CoreAssembly.conjClass K) :=
    fun A hA g => Theorem5.FuzzyFrameOn.map hinv hA g
  have hchain := tqChain_of_dConnected hp2 hq hz hD
  have hedge : ∀ M ∈ CoreAssembly.conjClass K, ∀ N ∈ CoreAssembly.conjClass K, ∀ zM zN : G,
      IsClassicalMember p f M zM → IsClassicalMember p f N zN → tqAdjSymm p f M N → zM ≠ zN →
      Theorem5.FrameAdj (Theorem5.fuzzyFrames p f (CoreAssembly.conjClass K))
        (Theorem5.fuzzyVertices p f (CoreAssembly.conjClass K)) zM zN := by
    intro M hM N hN zM zN hMc hNc hE hne
    rcases hE with ⟨a, ha, hNa⟩ | ⟨a, ha, hMa⟩
    · have : a = zM := hMc.eq_of_isCentralInvolution hp2 hf ha.isCentralInvolution
      subst this
      exact frameAdj_of_actsTrivOnQuot hnab hp2 hq hz hBelow hind' hM hN hMc hNc hNa hne
    · have : a = zN := hNc.eq_of_isCentralInvolution hp2 hf ha.isCentralInvolution
      subst this
      obtain ⟨B, hB, h1, h2⟩ := frameAdj_of_actsTrivOnQuot hnab hp2 hq hz hBelow hind' hN hM hNc
        hMc hMa hne.symm
      exact ⟨B, hB, h2, h1⟩
  have hcon := Theorem5.shareFour_connected_of_vertexGraph_modOdd
    (𝒯 := Theorem5.fuzzyFrames p f (CoreAssembly.conjClass K)) hmap
    (fun A hA => by
      obtain ⟨J, z, -, -, hel, hcard, -⟩ := hA
      exact ⟨hel, hcard⟩)
    (Theorem5.fuzzyVertices p f (CoreAssembly.conjClass K)) (fun A _ z hz => hz.1)
    (fun A hA => hA.exists_vertex)
    (fun A _ A' _ a ha a' ha' => by
      obtain ⟨-, J, hJ, hJa, -⟩ := ha
      obtain ⟨-, J', hJ', hJ'a, -⟩ := ha'
      exact Theorem5.reflTransGen_frameAdj_of_adj hp2 hf (fun M N => tqAdjSymm p f M N)
        hΩ.classical hchain (Theorem5.fuzzyVertices p f (CoreAssembly.conjClass K)) hedge hJ hJ'
        hJa hJ'a)
    (fun a A hA A' hA' ha ha' =>
      linkMove_connected_noConn hMFC hnab hp2 hq hz hBelow a hA hA' ha ha')
  obtain ⟨hex, hP1⟩ := exactMembers_and_localOddCentral_of_balancedFamilyD hnab hp2 hq hΩ
    (CoreAssembly.exists_single_class K) hIH hchain
    (fun A' hA' a _ ha1 => componentLayersAt_of_hybrid_free hnab hp2 hq ModelFacts.modelClauseZero
      hΩ hIH (Theorem5.memberFamily_of_indepTripleOn hp2 hf hA') hA' hmodel a ‹_› ha1)
    (fun A hA => rankThreeBalance_of_fuzzyFrameOn_hybrid_free hnab hp2 hq hBelow hA hmodel)
    hmap hcon hK' hcomm rfl hel hcard hA hexotic
  exact ⟨hex, hP1 K (CoreAssembly.mem_conjClass_self K) z hz⟩

end Boot


end CFSG.ClassicalInvolution.Disconnected
