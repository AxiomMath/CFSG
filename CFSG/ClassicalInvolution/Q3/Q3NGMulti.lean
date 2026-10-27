module

public import CFSG.ClassicalInvolution.Q3.Q3NGStar
public import CFSG.ClassicalInvolution.Q3.Q3NGCount
public import CFSG.ClassicalInvolution.Q3.Q3WAMFinal

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3W

open CFSG.Open hiding StatedLieTag StatedLieAdmissible
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
  CFSG.Assembly.LowTwoRank CFSG.LieType.Universal
open CFSG.ClassicalInvolution.RouteD.NonClassical (Linked NCEdge)
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)


theorem multiStar3_of_sharedInvolution3 (hconn : ModelConnFactNe3) (hstar : ModelStarFact3) :
    MultiStar3 := by
  intro G _ _ _ hnab K z h hO3 ι D hmulti
  have hMFZ := RouteD.Gaps.fundNoncentral 3
  have hc : LocCtx3 K z :=
    ⟨h.inClass, (CoreAssembly.deltaConnected_iff K).mp h.conn, h.setup.1, h.setup.2, hO3, h.cls⟩
  have hΩ := hc.hΩ
  have hex := hc.hex
  have hP1 := hc.hP1
  have hK : K ∈ conjClass3 K := ⟨1, conjSub_one K⟩
  obtain ⟨A₀, i₀, i', a₂, hA₀, hmax, hblock, hi₀na, hi'na, hi'ne, ha₂, hKV, hKc, hKa₂⟩ :=
    exists_maximal_block3 hMFZ hc D hmulti
  have hne := ne_bot_of_mem3 hΩ
  have hconn' := commutes_reflTransGen_of_connected3 hc.hconn
  obtain ⟨q, hqΩ, hqV, ⟨a₁₀, ha₁₀V, hqa₁₀⟩, ⟨c₀, hc₀V, hqc₀⟩, hqK, hqcl⟩ :=
    exists_not_commuting_nbr_of_max hnab hΩ.conjInvariant hΩ.generated hne hK h.cls.mem
      (single_class3 K) hconn' hA₀ hmax (hblock ▸ hKV)
      (fun B hB => (hKc B (hblock ▸ hB)).1)
  rw [hblock] at ha₁₀V hc₀V hqcl
  obtain ⟨b₁, hb₁, b₂, hb₂, hb₁ne, hcb₁, hcb₂, hb₁₂⟩ :=
    exists_nc_pair_in_block_nbr3 hMFZ hnab h hc D hA₀ hblock hi₀na hi'na hi'ne ha₂ hKc hqΩ hqcl
      hc₀V hqc₀
  obtain ⟨t, n, hft, hadm, hk₀⟩ : ∃ (t : StatedLieTag) (n : ℕ), IsFundTag t ∧
      StatedLieAdmissible t n 3 1 ∧ D.kind i₀ = CompData.model t n := by
    rcases kind_cases_of_not_a1 D hi₀na with h' | h'
    · exact h'
    · exact absurd hcb₁ (not_commutes_of_m11_comp3 hΩ hex hP1 hc.hO3 h' hc₀V hb₁)
  obtain ⟨hG2, hD4⟩ := tag3_ne_of_commuting_star hnab h hc D hc₀V hb₁ hb₂ hb₁ne hcb₁ hcb₂ hb₁₂
    hadm hk₀
  have hsc₀ : ∀ R ∈ (D.kind i₀).fund, ∀ R' ∈ (D.kind i₀).fund, ∃ g, R' = conjSub g R := by
    have key : ∀ c : CompData, c = CompData.model t n → ∀ R ∈ c.fund, ∀ R' ∈ c.fund,
        ∃ g : c.G, R' = conjSub g R := by
      rintro c rfl
      exact ModelFacts.fundamentalSingleClass t n 3 1 Nat.prime_three (modelFacts_isFundTag hft)
        hadm hG2 hD4
    exact key _ hk₀
  have hpc₀ : PowCop3 (D.kind i₀) := hk₀ ▸ powCop3_model hft hadm hG2 hD4
  obtain ⟨R_c, hRc⟩ := exists_corr_left3 hΩ hex hP1 hc.hO3 D hc₀V
  obtain ⟨R_b₁, hRb₁⟩ := exists_corr_left3 hΩ hex hP1 hc.hO3 D hb₁
  obtain ⟨R_b₂, hRb₂⟩ := exists_corr_left3 hΩ hex hP1 hc.hO3 D hb₂
  have hcc : CommFamilyConnected (D.kind i₀).fund := by
    have key : ∀ c : CompData, c = CompData.model t n → ∀ (R_c R_b₁ R_b₂ : Subgroup c.G),
        R_c ∈ c.fund → R_b₁ ∈ c.fund → R_b₂ ∈ c.fund → R_b₁ ≠ R_b₂ → Commutes R_c R_b₁ →
        Commutes R_c R_b₂ → ¬ Commutes R_b₁ R_b₂ → CommFamilyConnected c.fund := by
      rintro c rfl R_c R_b₁ R_b₂ h1 h2 h3 h4 h5 h6 h7
      exact hconn t n hft hadm hG2 hD4 R_c h1 R_b₁ h2 R_b₂ h3 h4 h5 h6 h7
    exact key _ hk₀ R_c R_b₁ R_b₂ hRc.2.1 hRb₁.2.1 hRb₂.2.1
      (fun hRe => hb₁ne (corr_unique_right3 hΩ hex hP1 hc.hO3 hRb₁ (hRe ▸ hRb₂)))
      ((corr_commutes3 hΩ hex hP1 hc.hO3 hpc₀ hRc hRb₁).mp hcb₁)
      ((corr_commutes3 hΩ hex hP1 hc.hO3 hpc₀ hRc hRb₂).mp hcb₂)
      (fun hc' => hb₁₂ ((corr_commutes3 hΩ hex hP1 hc.hO3 hpc₀ hRb₁ hRb₂).mpr hc'))
  have hconnV := members_chain_of_commConnected3 hΩ hex hP1 hc.hO3 D hsc₀ hpc₀ hcc
  obtain ⟨c', hcV, a₁, ha₁V, hca₁, hqc, hqa₁⟩ :=
    RouteD.exists_commuting_pair_of_chain hconnV hc₀V hqc₀ ha₁₀V hqa₁₀
  have hcΩ : c' ∈ conjClass3 K := hcV.1.1
  obtain ⟨y, hyc⟩ := hΩ.classical c' hcΩ
  obtain ⟨hP1y, hO3y⟩ := local_conj3 hc hcΩ hyc
  have hync : ¬ ({y} : Set G) ⊆ Subgroup.center G := by
    intro hsub
    have hyc' : y ∈ Subgroup.center G := hsub rfl
    rw [CoreAssembly.center_eq_bot hnab, Subgroup.mem_bot] at hyc'
    have h2 := hyc.orderOf_eq_two
    rw [hyc', orderOf_one] at h2
    omega
  obtain ⟨ιy, hιy, ⟨Dy⟩⟩ := h.ih {y} hync
  have hKa₁ : Commutes K a₁ := (hKc a₁ ha₁V).1
  have ha₁a₂ : Commutes a₁ a₂ := Gaps.commutes_symm (hKc a₁ ha₁V).2
  have hKy : K ∈ centralizingMembers (conjClass3 K) {y} :=
    mem_centralizingMembers_of_commutes hK hyc.mem (hKc c' hcV).1
  have ha₁y : a₁ ∈ centralizingMembers (conjClass3 K) {y} :=
    mem_centralizingMembers_of_commutes ha₁V.1.1 hyc.mem (Gaps.commutes_symm hca₁)
  have ha₂y : a₂ ∈ centralizingMembers (conjClass3 K) {y} :=
    mem_centralizingMembers_of_commutes ha₂.1.1 hyc.mem (hKc c' hcV).2
  have hqy : q ∈ centralizingMembers (conjClass3 K) {y} :=
    mem_centralizingMembers_of_commutes hqΩ hyc.mem hqc
  have hqa₂ : ¬ Commutes q a₂ := hqcl a₂ ha₂.1.1 (fun B hB => (hKc B hB).2)
  obtain ⟨iq, hq_iq, -⟩ := exists_unique_comp3 hΩ hex hP1y hO3y Dy hqy
  have hsame : ∀ {N : Subgroup G}, N ∈ centralizingMembers (conjClass3 K) {y} →
      ¬ Commutes q N → N ∈ compMembers3 (conjClass3 K) y Dy iq := by
    intro N hN hnc
    obtain ⟨j, hj, -⟩ := exists_unique_comp3 hΩ hex hP1y hO3y Dy hN
    have := eq_of_not_commutes3 hΩ hex hP1y hO3y Dy hq_iq hj hnc
    rw [this]
    exact hj
  have hK_iq := hsame hKy hqK
  have ha₁_iq := hsame ha₁y hqa₁
  have ha₂_iq := hsame ha₂y hqa₂
  have hiqna : ¬ IsA1Comp3 Dy iq := by
    intro hA1
    have hKa : K = a₁ := eq_of_mem_compMembers_a13 hΩ hex hP1y hO3y hA1 hK_iq ha₁_iq
    exact not_commutes_self3 h.cls (hKa ▸ hKa₁)
  obtain ⟨t', n', hft', hadm', hk'⟩ : ∃ (t : StatedLieTag) (n : ℕ), IsFundTag t ∧
      StatedLieAdmissible t n 3 1 ∧ Dy.kind iq = CompData.model t n := by
    rcases kind_cases_of_not_a1 Dy hiqna with h' | h'
    · exact h'
    · exact absurd hKa₁ (not_commutes_of_m11_comp3 hΩ hex hP1y hO3y h' hK_iq ha₁_iq)
  obtain ⟨hG2', hD4'⟩ := tag3_ne_of_commuting_triple hΩ hex Dy hK_iq ha₁_iq ha₂_iq hKa₁ hKa₂
    ha₁a₂ hadm' hk'
  have hsc : ∀ R ∈ (Dy.kind iq).fund, ∀ R' ∈ (Dy.kind iq).fund, ∃ g, R' = conjSub g R := by
    have key : ∀ c : CompData, c = CompData.model t' n' → ∀ R ∈ c.fund, ∀ R' ∈ c.fund,
        ∃ g : c.G, R' = conjSub g R := by
      rintro c rfl
      exact ModelFacts.fundamentalSingleClass t' n' 3 1 Nat.prime_three
        (modelFacts_isFundTag hft') hadm' hG2' hD4'
    exact key _ hk'
  have hpc : PowCop3 (Dy.kind iq) := hk' ▸ powCop3_model hft' hadm' hG2' hD4'
  obtain ⟨R_K, hRK⟩ := exists_corr_left3 hΩ hex hP1y hO3y Dy hK_iq
  obtain ⟨R_a₁, hRa₁⟩ := exists_corr_left3 hΩ hex hP1y hO3y Dy ha₁_iq
  obtain ⟨R_a₂, hRa₂⟩ := exists_corr_left3 hΩ hex hP1y hO3y Dy ha₂_iq
  obtain ⟨R_q, hRq⟩ := exists_corr_left3 hΩ hex hP1y hO3y Dy hq_iq
  have hnlink : ¬ LinkedIn (Dy.kind iq).fund R_K R_a₁ R_a₂ := by
    intro hlink
    have hl := linked_of_linkedIn3 hΩ hex hP1y hO3y Dy hsc hpc h.cls.mem hRK hRa₁ hRa₂ hlink
    have ha₂V : a₂ ∈ compMembers3 (conjClass3 K) z D i₀ :=
      (linked_iff_mem_compMembers3 hΩ hex hP1 hc.hO3 (quasi_or_a1_3 D i₀) ha₁V).mp hl
    exact hi'ne (eq_of_locImg_le_range3 hΩ hex hP1 hc.hO3 D ha₂.1 ha₂.2 ha₂V.2)
  have hstar' : ∀ c : CompData, c = CompData.model t' n' → ∀ R ∈ c.fund, ∀ R₁ ∈ c.fund,
      ∀ R₂ ∈ c.fund, ∀ R_q ∈ c.fund, Commutes R R₁ → Commutes R R₂ → Commutes R₁ R₂ →
      ¬ LinkedIn c.fund R R₁ R₂ → ¬ Commutes R_q R → ¬ Commutes R_q R₁ → ¬ Commutes R_q R₂ →
        ∃ R_β ∈ c.fund, ∃ R₁' ∈ c.fund, ∃ R₂' ∈ c.fund, LinkedIn c.fund R R₁ R₁' ∧
          LinkedIn c.fund R R₂ R₂' ∧ (∃ W, LinearBlockStandardPair (GaloisField 3 1) W R R_β) ∧
          (∃ W, LinearBlockStandardPair (GaloisField 3 1) W R₁' R_β) ∧
          (∃ W, LinearBlockStandardPair (GaloisField 3 1) W R₂' R_β) := by
    rintro c rfl
    exact hstar t' n' hft' hadm' hG2' hD4'
  obtain ⟨R_β, hRβF, R₁', hR₁'F, R₂', hR₂'F, hl₁, hl₂, hp₀, hp₁, hp₂⟩ :=
    hstar' _ hk' R_K hRK.2.1 R_a₁ hRa₁.2.1 R_a₂ hRa₂.2.1 R_q hRq.2.1
      ((corr_commutes3 hΩ hex hP1y hO3y hpc hRK hRa₁).mp hKa₁)
      ((corr_commutes3 hΩ hex hP1y hO3y hpc hRK hRa₂).mp hKa₂)
      ((corr_commutes3 hΩ hex hP1y hO3y hpc hRa₁ hRa₂).mp ha₁a₂) hnlink
      (fun hc'' => hqK ((corr_commutes3 hΩ hex hP1y hO3y hpc hRq hRK).mpr hc''))
      (fun hc'' => hqa₁ ((corr_commutes3 hΩ hex hP1y hO3y hpc hRq hRa₁).mpr hc''))
      (fun hc'' => hqa₂ ((corr_commutes3 hΩ hex hP1y hO3y hpc hRq hRa₂).mpr hc''))
  obtain ⟨β, hβ⟩ := exists_corr_right3 hΩ Dy hsc hRβF
  obtain ⟨a₁', ha₁'⟩ := exists_corr_right3 hΩ Dy hsc hR₁'F
  obtain ⟨a₂', ha₂'⟩ := exists_corr_right3 hΩ Dy hsc hR₂'F
  have ha₁'V : a₁' ∈ compMembers3 (conjClass3 K) z D i₀ :=
    (linked_iff_mem_compMembers3 hΩ hex hP1 hc.hO3 (quasi_or_a1_3 D i₀) ha₁V).mp
      (linked_of_linkedIn3 hΩ hex hP1y hO3y Dy hsc hpc h.cls.mem hRK hRa₁ ha₁' hl₁)
  have ha₂'V : a₂' ∈ compMembers3 (conjClass3 K) z D i' :=
    (linked_iff_mem_compMembers3 hΩ hex hP1 hc.hO3 (quasi_or_a1_3 D i') ha₂).mp
      (linked_of_linkedIn3 hΩ hex hP1y hO3y Dy hsc hpc h.cls.mem hRK hRa₂ ha₂' hl₂)
  have hstd : ∀ {N : Subgroup G} {R_N : Subgroup (Dy.kind iq).G},
      Corr3 (conjClass3 K) y Dy iq N R_N →
      (∃ W, LinearBlockStandardPair (GaloisField 3 1) W R_N R_β) →
      ∃ W, LinearBlockStandardPair (GaloisField 3 1) W N β := fun hN hpair =>
    linearBlockStandardPair_of_corr3 hΩ hex hP1y hO3y hN hβ hpair
  exact ⟨i₀, i', a₁', a₂', β, fun e => hi'ne e.symm, hi₀na, hi'na, ha₁'V, ha₂'V, hβ.1.1,
    hstd hRK hp₀, hstd ha₁' hp₁, hstd ha₂' hp₂⟩

theorem multiPiece3_of_odd3 (h3 : OddThreeFreeInput) : MultiPiece3 :=
  multiPiece3_of_star h3
    (multiStar3_of_sharedInvolution3 modelConnFactNe3_proved modelStarFact3_proved)

end CFSG.ClassicalInvolution.Q3.Q3W
