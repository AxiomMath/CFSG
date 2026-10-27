module

public import CFSG.ClassicalInvolution.RouteD.MultiModelGlue
public import CFSG.ClassicalInvolution.RouteD.NoG2D4Local

public section

namespace CFSG.ClassicalInvolution.RouteD

open CFSG.Open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Generic.CoreAssembly
  CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.RouteD.NonClassical
  CFSG.ClassicalInvolution.RouteD.G2D4
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)
open scoped commutatorElement

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G]

section Star

theorem tag_ne_of_commuting_star [Finite G] [IsSimpleGroup G] (hnab : ∃ a b : G, a * b ≠ b * a)
    (hSI : G2D4SharedInvolution p) {K : Subgroup G} {z : G} (h : RouteDSetup p f K z)
    (D : LieSystemData p f (locQuot (conjClass K) z) (locFamily (conjClass K) z))
    {i : Fin D.card} {c b₁ b₂ : Subgroup G}
    (hc : c ∈ Gaps.compMembers (conjClass K) z D i)
    (hb₁ : b₁ ∈ Gaps.compMembers (conjClass K) z D i)
    (hb₂ : b₂ ∈ Gaps.compMembers (conjClass K) z D i)
    (hne : b₁ ≠ b₂) (cb₁ : Commutes c b₁) (cb₂ : Commutes c b₂) (hn : ¬ Commutes b₁ b₂) :
    D.tag i ≠ .G2 ∧ D.tag i ≠ .trialityD4 := by
  by_contra hcon
  have ht : D.tag i = .G2 ∨ D.tag i = .trialityD4 := by
    by_cases h' : D.tag i = .G2
    · exact Or.inl h'
    · refine Or.inr ?_
      by_contra h''
      exact hcon ⟨h', h''⟩
  have hΩ := h.inClass
  have hex := h.exact
  have hf : 0 < f := pos_of_five_le h.five
  obtain ⟨w₀, hw₀⟩ := hΩ.classical c hc.1.1
  obtain ⟨w₁, hw₁⟩ := hΩ.classical b₁ hb₁.1.1
  obtain ⟨w₂, hw₂⟩ := hΩ.classical b₂ hb₂.1.1
  have hw : w₁ = w₂ := eq_involution_of_commuting_in_g2d4 hSI h.odd hΩ h.p1 D ht hc hb₁ hb₂
    hw₀ hw₁ hw₂ cb₁ cb₂
  subst hw
  have hP1w : LocalOddCentral (conjClass K) {w₁} :=
    Balance.localOddCentral_of_classicalMember h.odd hf hΩ
      ⟨K, mem_conjClass_self K, single_class K⟩ (mem_conjClass_self K) h.cls h.p1 b₁ hb₁.1.1 w₁
      hw₁
  have hync : ¬ ({w₁} : Set G) ⊆ Subgroup.center G := by
    intro hsub
    have hyc' : w₁ ∈ Subgroup.center G := hsub rfl
    rw [center_eq_bot hnab, Subgroup.mem_bot] at hyc'
    have h2 := hw₁.orderOf_eq_two
    rw [hyc', orderOf_one] at h2
    omega
  obtain ⟨Dw⟩ := NonClassical.exists_lieSystemData h.ih hync
  have hb₁w : b₁ ∈ centralizingMembers (conjClass K) {w₁} :=
    ⟨hb₁.1.1, le_centralizer_of_isClassicalMember hw₁⟩
  have hb₂w : b₂ ∈ centralizingMembers (conjClass K) {w₁} :=
    ⟨hb₂.1.1, le_centralizer_of_isClassicalMember hw₂⟩
  rcases Gaps.commutes_or_eq_of_involution (Gaps.fundNoncentral p) hΩ hex hP1w Dw hb₁w hb₂w hw₁
    with h' | h'
  · exact hn h'
  · exact hne h'.symm

end Star

section Reduction

theorem multiStar_of_sharedInvolution (hconn : ModelConnFactNe p) (hstar : ModelStarFact p)
    (hSI : G2D4SharedInvolution p) : MultiStar p f := by
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
  have hD0 : D.tag i₀ ≠ .G2 ∧ D.tag i₀ ≠ .trialityD4 :=
    tag_ne_of_commuting_star hnab hSI h D hc₀V hb₁ hb₂ hb₁ne hcb₁ hcb₂ hb₁₂
  have hsc₀ := Gaps.fundamentalSingleClass_of_ne D i₀ hD0.1 hD0.2
  have hexp₀ : D.exp i₀ = f := (D.exp_eq i₀).resolve_right (fun hh => hD0.2 hh.1)
  have hperf₀ : Gaps.FundPerfect (D.tag i₀)
      (modelUniv (D.tag i₀) (D.rank i₀) p (D.exp i₀) Fact.out).D :=
    Gaps.fundPerfect_modelUniv h.odd (D.isFundTag i₀) (D.admissible i₀)
      (by rw [hexp₀]; exact hq4)
  obtain ⟨R_c, hRc⟩ := Gaps.exists_corr_left hΩ hex D hc₀V
  obtain ⟨R_b₁, hRb₁⟩ := Gaps.exists_corr_left hΩ hex D hb₁
  obtain ⟨R_b₂, hRb₂⟩ := Gaps.exists_corr_left hΩ hex D hb₂
  have hcc : CommFamilyConnected (Gaps.compFund D i₀) :=
    hconn (D.tag i₀) (D.rank i₀) (D.exp i₀) (D.isFundTag i₀) (D.admissible i₀) h.odd
      (by rw [hexp₀]; exact h.five) hD0.1 hD0.2 R_c hRc.2.1 R_b₁ hRb₁.2.1 R_b₂ hRb₂.2.1
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
  have hDy : Dy.tag iq ≠ .G2 ∧ Dy.tag iq ≠ .trialityD4 :=
    tag_ne_of_commuting_triple h.odd hΩ hex Dy hK_iq ha₁_iq ha₂_iq hKa₁ hKa₂ ha₁a₂
  have hsc := Gaps.fundamentalSingleClass_of_ne Dy iq hDy.1 hDy.2
  have hexp : Dy.exp iq = f := (Dy.exp_eq iq).resolve_right (fun hh => hDy.2 hh.1)
  have hperf : Gaps.FundPerfect (Dy.tag iq)
      (modelUniv (Dy.tag iq) (Dy.rank iq) p (Dy.exp iq) Fact.out).D :=
    Gaps.fundPerfect_modelUniv h.odd (Dy.isFundTag iq) (Dy.admissible iq)
      (by rw [hexp]; exact hq4)
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
      (by rw [hexp]; exact h.five) hDy.1 hDy.2 R_K hRK.2.1 R_a₁ hRa₁.2.1 R_a₂ hRa₂.2.1
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


theorem multiPiece_of_sharedInvolution (hconn : ModelConnFactNe p) (hstar : ModelStarFact p)
    (hSI : G2D4SharedInvolution p) : MultiPiece p f :=
  multiPiece_of_multiStar (multiStar_of_sharedInvolution hconn hstar hSI)

end Reduction

end CFSG.ClassicalInvolution.RouteD
