module

public import CFSG.ClassicalInvolution.RouteD.MultiStarModel

public section

namespace CFSG.ClassicalInvolution.RouteD

open CFSG.Open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Generic.CoreAssembly
  CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.RouteD.NonClassical
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G]

section MaxBlock

variable [Finite G] [IsSimpleGroup G]

theorem exists_nc_pair_in_block_nbr_ne (hnab : ∃ a b : G, a * b ≠ b * a) {K : Subgroup G} {z : G}
    (h : RouteDSetup p f K z)
    (D : LieSystemData p f (locQuot (conjClass K) z) (locFamily (conjClass K) z))
    {A₀ : Subgroup G} {i₀ i' : Fin D.card} {a₂ q c : Subgroup G}
    (hA₀ : A₀ ∈ centralizingMembers (conjClass K) {z})
    (hblock : ncBlock (conjClass K) z A₀ = Gaps.compMembers (conjClass K) z D i₀)
    (hi₀na : ¬ IsA1Comp D i₀) (hi'na : ¬ IsA1Comp D i') (hi'ne : i' ≠ i₀)
    (ha₂ : a₂ ∈ Gaps.compMembers (conjClass K) z D i')
    (hKc : ∀ B ∈ Gaps.compMembers (conjClass K) z D i₀, Commutes K B ∧ Commutes a₂ B)
    (hqΩ : q ∈ conjClass K)
    (hqcl : ∀ x ∈ conjClass K, (∀ B ∈ Gaps.compMembers (conjClass K) z D i₀, Commutes x B) →
      ¬ Commutes q x)
    (hc : c ∈ Gaps.compMembers (conjClass K) z D i₀) (hqc : Commutes q c) :
    ∃ b₁ ∈ Gaps.compMembers (conjClass K) z D i₀, ∃ b₂ ∈ Gaps.compMembers (conjClass K) z D i₀,
      b₁ ≠ b₂ ∧ Commutes c b₁ ∧ Commutes c b₂ ∧ ¬ Commutes b₁ b₂ := by
  have hΩ := h.inClass
  have hex := h.exact
  have hP1 := h.p1
  have hf : 0 < f := pos_of_five_le h.five
  have hcΩ : c ∈ conjClass K := hc.1.1
  have hKz : K ∈ centralizingMembers (conjClass K) {z} :=
    ⟨mem_conjClass_self K, le_centralizer_of_isClassicalMember h.cls⟩
  obtain ⟨g, hg⟩ := single_class K c hcΩ
  have hyc : IsClassicalMember p f c (g * z * g⁻¹) := by
    rw [hg]
    exact h.cls.conj g
  set y : G := g * z * g⁻¹ with hy
  have hP1y : LocalOddCentral (conjClass K) {y} :=
    Balance.localOddCentral_of_classicalMember h.odd hf hΩ
      ⟨K, mem_conjClass_self K, single_class K⟩ (mem_conjClass_self K) h.cls hP1 c hcΩ y hyc
  have hync : ¬ ({y} : Set G) ⊆ Subgroup.center G := by
    intro hsub
    have hyc' : y ∈ Subgroup.center G := hsub rfl
    rw [center_eq_bot hnab, Subgroup.mem_bot] at hyc'
    have h2 := hyc.orderOf_eq_two
    rw [hyc', orderOf_one] at h2
    omega
  obtain ⟨Dy⟩ := NonClassical.exists_lieSystemData h.ih hync
  have hcy : c ∈ centralizingMembers (conjClass K) {y} :=
    ⟨hcΩ, le_centralizer_of_isClassicalMember hyc⟩
  have hcp : ∀ L ∈ centralizingMembers (conjClass K) {y}, L ≠ c → Commutes c L := fun L hL hne =>
    (Gaps.commutes_or_eq_of_involution (Gaps.fundNoncentral p) hΩ hex hP1y Dy hcy hL
      hyc).resolve_right hne
  set V := Gaps.compMembers (conjClass K) z D i₀ with hV
  have hcent : ∀ x ∈ conjClass K, (∀ B ∈ V, Commutes x B) →
      x ∈ centralizingMembers (conjClass K) {y} := by
    intro x hx hxV
    refine ⟨hx, fun u hu => ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact hxV c hc u hu y hyc.mem
  have hqy : q ∈ centralizingMembers (conjClass K) {y} := by
    refine ⟨hqΩ, fun u hu => ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact hqc u hu y hyc.mem
  have hblk : ∀ x ∈ conjClass K, (∀ B ∈ V, Commutes x B) → x ∈ ncBlock (conjClass K) y q :=
    fun x hx hxV => Linked.single ⟨hqy, hcent x hx hxV, hqcl x hx hxV⟩
  have hKV : ∀ B ∈ V, Commutes K B := fun B hB => (hKc B hB).1
  have hKy : K ∈ centralizingMembers (conjClass K) {y} := hcent K (mem_conjClass_self K) hKV
  have hKblk : Linked (conjClass K) y q K := hblk K (mem_conjClass_self K) hKV
  have hout : ∀ x' ∈ centralizingMembers (conjClass K) {y}, x' ∉ ncBlock (conjClass K) y q →
      x' ∈ V := by
    intro x' hx'y hx'
    have hx'K : Commutes x' K := by
      by_contra hnc
      exact hx' (hKblk.trans (Linked.single ⟨hKy, hx'y, fun hc' =>
        hnc (Gaps.commutes_symm hc')⟩))
    have hx'z : x' ∈ centralizingMembers (conjClass K) {z} :=
      mem_centralizingMembers_of_commutes hx'y.1 h.cls.mem hx'K
    obtain ⟨j, hj, -⟩ := Gaps.exists_unique_comp hΩ hex D hx'z
    by_cases hji : j = i₀
    · rw [hji] at hj
      exact hj
    · exact absurd (hblk x' hx'y.1 fun B hB => Gaps.commutes_of_ne_comp hΩ hP1 D hji hj hB) hx'
  have hcblock : ∀ w, Linked (conjClass K) y c w → w = c := by
    intro w hw
    induction hw with
    | refl => rfl
    | @tail b d _ hbd ih =>
      rw [ih] at hbd
      by_contra hdc
      exact hbd.2.2 (hcp d hbd.2.1 hdc)
  have hsize : ∀ i : Fin D.card, ¬ IsA1Comp D i →
      1 < (Gaps.compMembers (conjClass K) z D i).ncard := by
    intro i hi
    obtain ⟨N, N', hN, hN', hne⟩ := exists_ne_of_not_isA1Comp hΩ hex hi
    exact (Set.one_lt_ncard (Set.toFinite _)).mpr ⟨N, hN, N', hN', hne⟩
  have hVcard : 1 < V.ncard := hsize i₀ hi₀na
  have hconj : ∀ A ∈ centralizingMembers (conjClass K) {z},
      conjSub g A ∈ centralizingMembers (conjClass K) {y} := by
    intro A hA
    have := centralizingMembers_conj hΩ.conjInvariant g z
    rw [hy, this]
    exact ⟨A, hA, rfl⟩
  have hA'C : conjSub g A₀ ∈ ncBlock (conjClass K) y q := by
    by_contra hA'
    have hA'y := hconj A₀ hA₀
    have hsub : ncBlock (conjClass K) y (conjSub g A₀) ⊆ V := by
      intro w hw
      have hw' : Linked (conjClass K) y (conjSub g A₀) w := hw
      have hwy := hw'.mem_centralizingMembers hA'y
      refine hout w hwy fun hwq => hA' ?_
      exact (show Linked (conjClass K) y q w from hwq).trans hw'.symm
    have hXcard : (ncBlock (conjClass K) y (conjSub g A₀)).ncard = V.ncard := by
      rw [ncard_ncBlock_conj hΩ.conjInvariant g z A₀, hblock]
    have heq : ncBlock (conjClass K) y (conjSub g A₀) = V :=
      Set.eq_of_subset_of_ncard_le hsub hXcard.ge (Set.toFinite _)
    have hcX0 : c ∈ ncBlock (conjClass K) y (conjSub g A₀) := by
      rw [heq]
      exact hc
    have hcX : Linked (conjClass K) y (conjSub g A₀) c := hcX0
    have hAc : conjSub g A₀ = c := hcblock _ hcX.symm
    have h1 : (ncBlock (conjClass K) y (conjSub g A₀)).ncard ≤ 1 := by
      rw [Set.ncard_le_one_iff (Set.toFinite _)]
      intro a b ha hb
      have ha' : Linked (conjClass K) y c a := by rw [← hAc]; exact ha
      have hb' : Linked (conjClass K) y c b := by rw [← hAc]; exact hb
      rw [hcblock a ha', hcblock b hb']
    omega
  have hXVC : ncBlock (conjClass K) y (conjSub g A₀) = ncBlock (conjClass K) y q := by
    ext w
    have h1 : Linked (conjClass K) y q (conjSub g A₀) := hA'C
    constructor
    · intro hw
      exact h1.trans hw
    · intro hw
      exact h1.symm.trans hw
  have hblock' : ncBlock (conjClass K) z a₂ = Gaps.compMembers (conjClass K) z D i' := by
    ext B
    exact linked_iff_mem_compMembers hΩ hex hP1 ha₂
  have hA''y := hconj a₂ ha₂.1
  have hA''C : conjSub g a₂ ∉ ncBlock (conjClass K) y q := by
    intro hA''
    have h2 : ncBlock (conjClass K) y (conjSub g a₂) =
        ncBlock (conjClass K) y (conjSub g A₀) := by
      rw [hXVC]
      ext w
      have h1 : Linked (conjClass K) y q (conjSub g a₂) := hA''
      constructor
      · intro hw
        exact h1.trans hw
      · intro hw
        exact h1.symm.trans hw
    rw [ncBlock_conj hΩ.conjInvariant, ncBlock_conj hΩ.conjInvariant] at h2
    have h3 : ncBlock (conjClass K) z a₂ = ncBlock (conjClass K) z A₀ :=
      Set.image_injective.mpr (conjSub_injective g) h2
    have h4 : a₂ ∈ V := by
      rw [← hblock, ← h3]
      exact Relation.ReflTransGen.refl
    exact hi'ne (Gaps.eq_of_locImg_le_range hΩ hex D ha₂.1 ha₂.2 h4.2)
  have hsubV' : ncBlock (conjClass K) y (conjSub g a₂) ⊆ V := by
    intro w hw
    have hw' : Linked (conjClass K) y (conjSub g a₂) w := hw
    have hwy := hw'.mem_centralizingMembers hA''y
    refine hout w hwy fun hwq => hA''C ?_
    exact (show Linked (conjClass K) y q w from hwq).trans hw'.symm
  have hV'card : 1 < (ncBlock (conjClass K) y (conjSub g a₂)).ncard := by
    rw [ncard_ncBlock_conj hΩ.conjInvariant g z a₂, hblock']
    exact hsize i' hi'na
  obtain ⟨B₁, hB₁, B₂, hB₂, hne⟩ := (Set.one_lt_ncard (Set.toFinite _)).mp hV'card
  obtain ⟨B, hB, hBne⟩ : ∃ B ∈ ncBlock (conjClass K) y (conjSub g a₂), B ≠ conjSub g a₂ := by
    by_cases h1 : B₁ = conjSub g a₂
    · exact ⟨B₂, hB₂, fun h2 => hne (h1.trans h2.symm)⟩
    · exact ⟨B₁, hB₁, h1⟩
  obtain ⟨b₁, hb₁, b₂, hb₂, hbne, hbnc⟩ := exists_nc_pair_of_block ⟨B, hB, hBne⟩
  have hbc : ∀ b ∈ ncBlock (conjClass K) y (conjSub g a₂), b ≠ c := by
    intro b hb hbc
    have hb' : Linked (conjClass K) y (conjSub g a₂) c := by rw [← hbc]; exact hb
    have hAc : conjSub g a₂ = c := hcblock _ hb'.symm
    have h1 : (ncBlock (conjClass K) y (conjSub g a₂)).ncard ≤ 1 := by
      rw [Set.ncard_le_one_iff (Set.toFinite _)]
      intro a b ha hb
      have ha' : Linked (conjClass K) y c a := by rw [← hAc]; exact ha
      have hb' : Linked (conjClass K) y c b := by rw [← hAc]; exact hb
      rw [hcblock a ha', hcblock b hb']
    omega
  exact ⟨b₁, hsubV' hb₁, b₂, hsubV' hb₂, hbne,
    hcp b₁ (hb₁.mem_centralizingMembers hA''y) (hbc b₁ hb₁),
    hcp b₂ (hb₂.mem_centralizingMembers hA''y) (hbc b₂ hb₂), hbnc⟩

end MaxBlock

@[expose] def ModelConnFactNe (p : ℕ) [Fact p.Prime] : Prop :=
  ∀ (t : CFSG.Assembly.LowTwoRank.StatedLieTag) (n e : ℕ), IsFundTag t →
    StatedLieAdmissible t n p e → p ≠ 2 → 5 ≤ p ^ e → t ≠ .G2 → t ≠ .trialityD4 →
    ∀ R ∈ ModelFund p t n e, ∀ R₁ ∈ ModelFund p t n e, ∀ R₂ ∈ ModelFund p t n e,
      R₁ ≠ R₂ → Commutes R R₁ → Commutes R R₂ → ¬ Commutes R₁ R₂ →
        CommFamilyConnected (ModelFund p t n e)

section Reduction

theorem multiStar_of_modelFactsNe (hconn : ModelConnFactNe p) (hstar : ModelStarFact p)
    (hno : NoG2D4 p f) : MultiStar p f := by
  intro G _ _ _ hnab K z h D hmulti
  have hΩ := h.inClass
  have hex := h.exact
  have hP1 := h.p1
  have hf : 0 < f := pos_of_five_le h.five
  have hq4 : 4 ≤ p ^ f := by have := h.five; omega
  obtain ⟨A₀, i₀, i', a₂, hA₀, hmax, hblock, hi₀na, hi'na, hi'ne, ha₂, hKV, hKc, hKa₂⟩ :=
    exists_maximal_block h D hmulti
  have hne : ∀ L ∈ conjClass K, L ≠ ⊥ := by
    intro L hL hbot
    obtain ⟨w, hw⟩ := hΩ.classical L hL
    have := hw.mem
    rw [hbot, Subgroup.mem_bot] at this
    have h2 := hw.orderOf_eq_two
    rw [this, orderOf_one] at h2
    omega
  have hconn' : ∀ X ∈ conjClass K, ∀ Y ∈ conjClass K, Relation.ReflTransGen
      (fun A B : Subgroup G => A ∈ conjClass K ∧ B ∈ conjClass K ∧ Commutes A B) X Y := by
    intro X hX Y hY
    have hreach := h.conn.preconnected ⟨X, hX⟩ ⟨Y, hY⟩
    rw [SimpleGraph.reachable_iff_reflTransGen] at hreach
    have key : ∀ v : conjClass K, Relation.ReflTransGen
        (CFSG.ClassicalInvolution.Models.commGraph (conjClass K)).Adj ⟨X, hX⟩ v →
        Relation.ReflTransGen
          (fun A B : Subgroup G => A ∈ conjClass K ∧ B ∈ conjClass K ∧ Commutes A B) X
          (v : Subgroup G) := by
      intro v hv
      induction hv with
      | refl => exact Relation.ReflTransGen.refl
      | @tail b c _ hbc ih =>
        exact ih.tail ⟨b.2, c.2, (CFSG.ClassicalInvolution.Models.commGraph_adj.mp hbc).2⟩
    exact key ⟨Y, hY⟩ hreach
  obtain ⟨q, hqΩ, hqV, ⟨a₁₀, ha₁₀V, hqa₁₀⟩, ⟨c₀, hc₀V, hqc₀⟩, hqK, hqcl⟩ :=
    exists_not_commuting_nbr_of_max hnab hΩ.conjInvariant hΩ.generated hne (mem_conjClass_self K)
      h.cls.mem (single_class K) hconn' hA₀ hmax (hblock ▸ hKV)
      (fun B hB => (hKc B (hblock ▸ hB)).1)
  rw [hblock] at ha₁₀V hc₀V hqcl
  obtain ⟨b₁, hb₁, b₂, hb₂, hb₁ne, hcb₁, hcb₂, hb₁₂⟩ :=
    exists_nc_pair_in_block_nbr_ne hnab h D hA₀ hblock hi₀na hi'na hi'ne ha₂ hKc hqΩ hqcl hc₀V hqc₀
  have hD0 := hno G hnab K z h K z (mem_conjClass_self K) h.cls D
  have hsc₀ := Gaps.fundamentalSingleClass_of_ne D i₀ (hD0 i₀).1 (hD0 i₀).2
  have hperf₀ : Gaps.FundPerfect (D.tag i₀)
      (modelUniv (D.tag i₀) (D.rank i₀) p (D.exp i₀) Fact.out).D :=
    D.fundPerfect h.odd hq4 (fun i hi => absurd hi (hD0 i).2) i₀
  have hexp₀ : D.exp i₀ = f :=
    (D.exp_eq i₀).resolve_right (fun hh => (hD0 i₀).2 hh.1)
  obtain ⟨R_c, hRc⟩ := Gaps.exists_corr_left hΩ hex D hc₀V
  obtain ⟨R_b₁, hRb₁⟩ := Gaps.exists_corr_left hΩ hex D hb₁
  obtain ⟨R_b₂, hRb₂⟩ := Gaps.exists_corr_left hΩ hex D hb₂
  have hcc : CommFamilyConnected (Gaps.compFund D i₀) :=
    hconn (D.tag i₀) (D.rank i₀) (D.exp i₀) (D.isFundTag i₀) (D.admissible i₀) h.odd
      (by rw [hexp₀]; exact h.five) (hD0 i₀).1 (hD0 i₀).2 R_c hRc.2.1 R_b₁ hRb₁.2.1 R_b₂ hRb₂.2.1
      (fun hRe => hb₁ne (Gaps.corr_unique_right hΩ hP1 hRb₁ (hRe ▸ hRb₂)))
      ((Gaps.corr_commutes hΩ hP1 hperf₀ hRc hRb₁).mp hcb₁)
      ((Gaps.corr_commutes hΩ hP1 hperf₀ hRc hRb₂).mp hcb₂)
      (fun hc => hb₁₂ ((Gaps.corr_commutes hΩ hP1 hperf₀ hRb₁ hRb₂).mpr hc))
  have hconnV := members_chain_of_commConnected hΩ hex hP1 D hsc₀ hperf₀ hcc
  obtain ⟨c, hcV, a₁, ha₁V, hca₁, hqc, hqa₁⟩ :=
    exists_commuting_pair_of_chain hconnV hc₀V hqc₀ ha₁₀V hqa₁₀
  have hcΩ : c ∈ conjClass K := hcV.1.1
  obtain ⟨y, hyc⟩ := hΩ.classical c hcΩ
  have hP1y : LocalOddCentral (conjClass K) {y} :=
    Balance.localOddCentral_of_classicalMember h.odd hf hΩ
      ⟨K, mem_conjClass_self K, single_class K⟩ (mem_conjClass_self K) h.cls hP1 c hcΩ y hyc
  have hync : ¬ ({y} : Set G) ⊆ Subgroup.center G := by
    intro hsub
    have hyc' : y ∈ Subgroup.center G := hsub rfl
    rw [center_eq_bot hnab, Subgroup.mem_bot] at hyc'
    have h2 := hyc.orderOf_eq_two
    rw [hyc', orderOf_one] at h2
    omega
  obtain ⟨Dy⟩ := NonClassical.exists_lieSystemData h.ih hync
  have hKa₁ : Commutes K a₁ := (hKc a₁ ha₁V).1
  have ha₁a₂ : Commutes a₁ a₂ := Gaps.commutes_symm (hKc a₁ ha₁V).2
  have hKy : K ∈ centralizingMembers (conjClass K) {y} :=
    mem_centralizingMembers_of_commutes (mem_conjClass_self K) hyc.mem (hKc c hcV).1
  have ha₁y : a₁ ∈ centralizingMembers (conjClass K) {y} :=
    mem_centralizingMembers_of_commutes ha₁V.1.1 hyc.mem (Gaps.commutes_symm hca₁)
  have ha₂y : a₂ ∈ centralizingMembers (conjClass K) {y} :=
    mem_centralizingMembers_of_commutes ha₂.1.1 hyc.mem (hKc c hcV).2
  have hqy : q ∈ centralizingMembers (conjClass K) {y} :=
    mem_centralizingMembers_of_commutes hqΩ hyc.mem hqc
  have hqa₂ : ¬ Commutes q a₂ := hqcl a₂ ha₂.1.1 (fun B hB => (hKc B hB).2)
  obtain ⟨iq, hq_iq, -⟩ := Gaps.exists_unique_comp hΩ hex Dy hqy
  have hsame : ∀ {N : Subgroup G}, N ∈ centralizingMembers (conjClass K) {y} → ¬ Commutes q N →
      N ∈ Gaps.compMembers (conjClass K) y Dy iq := by
    intro N hN hnc
    obtain ⟨j, hj, -⟩ := Gaps.exists_unique_comp hΩ hex Dy hN
    have := NonClassical.eq_of_not_commutes hΩ hP1y Dy hq_iq hj hnc
    rw [this]
    exact hj
  have hK_iq := hsame hKy hqK
  have ha₁_iq := hsame ha₁y hqa₁
  have ha₂_iq := hsame ha₂y hqa₂
  have hDy := hno G hnab K z h c y hcΩ hyc Dy
  have hsc := Gaps.fundamentalSingleClass_of_ne Dy iq (hDy iq).1 (hDy iq).2
  have hperf : Gaps.FundPerfect (Dy.tag iq)
      (modelUniv (Dy.tag iq) (Dy.rank iq) p (Dy.exp iq) Fact.out).D :=
    Dy.fundPerfect h.odd hq4 (fun i hi => absurd hi (hDy i).2) iq
  have hexp : Dy.exp iq = f := (Dy.exp_eq iq).resolve_right (fun hh => (hDy iq).2 hh.1)
  obtain ⟨R_K, hRK⟩ := Gaps.exists_corr_left hΩ hex Dy hK_iq
  obtain ⟨R_a₁, hRa₁⟩ := Gaps.exists_corr_left hΩ hex Dy ha₁_iq
  obtain ⟨R_a₂, hRa₂⟩ := Gaps.exists_corr_left hΩ hex Dy ha₂_iq
  obtain ⟨R_q, hRq⟩ := Gaps.exists_corr_left hΩ hex Dy hq_iq
  have hnlink : ¬ LinkedIn (Gaps.compFund Dy iq) R_K R_a₁ R_a₂ := by
    intro hlink
    have hl := linked_of_linkedIn hΩ hP1y Dy hsc hperf h.cls.mem hRK hRa₁ hRa₂ hlink
    have ha₂V : a₂ ∈ Gaps.compMembers (conjClass K) z D i₀ :=
      (linked_iff_mem_compMembers hΩ hex hP1 ha₁V).mp hl
    exact hi'ne (Gaps.eq_of_locImg_le_range hΩ hex D ha₂.1 ha₂.2 ha₂V.2)
  obtain ⟨R_β, hRβF, R₁', hR₁'F, R₂', hR₂'F, hl₁, hl₂, hp₀, hp₁, hp₂⟩ :=
    hstar (Dy.tag iq) (Dy.rank iq) (Dy.exp iq) (Dy.isFundTag iq) (Dy.admissible iq) h.odd
      (by rw [hexp]; exact h.five) (hDy iq).1 (hDy iq).2 R_K hRK.2.1 R_a₁ hRa₁.2.1 R_a₂ hRa₂.2.1
      R_q hRq.2.1 ((Gaps.corr_commutes hΩ hP1y hperf hRK hRa₁).mp hKa₁)
      ((Gaps.corr_commutes hΩ hP1y hperf hRK hRa₂).mp hKa₂)
      ((Gaps.corr_commutes hΩ hP1y hperf hRa₁ hRa₂).mp ha₁a₂) hnlink
      (fun hc => hqK ((Gaps.corr_commutes hΩ hP1y hperf hRq hRK).mpr hc))
      (fun hc => hqa₁ ((Gaps.corr_commutes hΩ hP1y hperf hRq hRa₁).mpr hc))
      (fun hc => hqa₂ ((Gaps.corr_commutes hΩ hP1y hperf hRq hRa₂).mpr hc))
  obtain ⟨β, hβ⟩ := Gaps.exists_corr_right hΩ Dy hsc hRβF
  obtain ⟨a₁', ha₁'⟩ := Gaps.exists_corr_right hΩ Dy hsc hR₁'F
  obtain ⟨a₂', ha₂'⟩ := Gaps.exists_corr_right hΩ Dy hsc hR₂'F
  have ha₁'V : a₁' ∈ Gaps.compMembers (conjClass K) z D i₀ :=
    (linked_iff_mem_compMembers hΩ hex hP1 ha₁V).mp
      (linked_of_linkedIn hΩ hP1y Dy hsc hperf h.cls.mem hRK hRa₁ ha₁' hl₁)
  have ha₂'V : a₂' ∈ Gaps.compMembers (conjClass K) z D i' :=
    (linked_iff_mem_compMembers hΩ hex hP1 ha₂).mp
      (linked_of_linkedIn hΩ hP1y Dy hsc hperf h.cls.mem hRK hRa₂ ha₂' hl₂)
  have hstd : ∀ {N : Subgroup G} {R_N : Subgroup
      (modelUniv (Dy.tag iq) (Dy.rank iq) p (Dy.exp iq) Fact.out).K},
      Gaps.Corr (conjClass K) y Dy iq N R_N →
      (∃ W, LinearBlockStandardPair (GaloisField p (Dy.exp iq)) W R_N R_β) →
      ∃ W, LinearBlockStandardPair (GaloisField p f) W N β := by
    intro N R_N hN hpair
    obtain ⟨W, hW⟩ := hpair
    exact NonClassical.linearBlockStandardPair_of_corr h.five hΩ hP1y hN hβ
      ⟨W, linearBlockStandardPair_congr_field hexp hW⟩
  exact ⟨i₀, i', a₁', a₂', β, fun e => hi'ne e.symm, hi₀na, hi'na, ha₁'V, ha₂'V, hβ.1.1,
    hstd hRK hp₀, hstd ha₁' hp₁, hstd ha₂' hp₂⟩

theorem multiPiece_of_modelFactsNe (hconn : ModelConnFactNe p) (hstar : ModelStarFact p)
    (hno : NoG2D4 p f) : MultiPiece p f :=
  multiPiece_of_multiStar (multiStar_of_modelFactsNe hconn hstar hno)

@[expose] def MultiModelFactsNe (p f : ℕ) [Fact p.Prime] : Prop :=
  ModelConnFactNe p ∧ ModelStarFact p ∧ NoG2D4 p f

theorem multiPiece_of_multiModelFactsNe (h : MultiModelFactsNe p f) : MultiPiece p f :=
  multiPiece_of_modelFactsNe h.1 h.2.1 h.2.2

end Reduction

end CFSG.ClassicalInvolution.RouteD
