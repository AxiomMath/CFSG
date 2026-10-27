module

public import CFSG.ClassicalInvolution.Q3.Generation
public import CFSG.ClassicalInvolution.Q3.Q3WAStar
public import CFSG.ClassicalInvolution.Q3.Q3WAM11Comp

public section

namespace CFSG.ClassicalInvolution.Q3.Q3W

open CFSG.Open hiding StatedLieTag StatedLieAdmissible
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
  CFSG.Assembly.LowTwoRank CFSG.LieType.Universal
open CFSG.ClassicalInvolution.RouteD.NonClassical (Linked NCEdge)
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)

section Facts


@[expose] def ModelConnFactNe3 : Prop :=
  ∀ (t : StatedLieTag) (n : ℕ), IsFundTag t → StatedLieAdmissible t n 3 1 → t ≠ .G2 →
    t ≠ .trialityD4 →
    ∀ R ∈ ModelFund 3 t n 1, ∀ R₁ ∈ ModelFund 3 t n 1, ∀ R₂ ∈ ModelFund 3 t n 1,
      R₁ ≠ R₂ → Commutes R R₁ → Commutes R R₂ → ¬ Commutes R₁ R₂ →
        CommFamilyConnected (ModelFund 3 t n 1)

@[expose] def ModelStarFact3 : Prop :=
  ∀ (t : StatedLieTag) (n : ℕ), IsFundTag t → StatedLieAdmissible t n 3 1 → t ≠ .G2 →
    t ≠ .trialityD4 →
    ∀ R ∈ ModelFund 3 t n 1, ∀ R₁ ∈ ModelFund 3 t n 1, ∀ R₂ ∈ ModelFund 3 t n 1,
      ∀ R_q ∈ ModelFund 3 t n 1, Commutes R R₁ → Commutes R R₂ → Commutes R₁ R₂ →
      ¬ LinkedIn (ModelFund 3 t n 1) R R₁ R₂ → ¬ Commutes R_q R → ¬ Commutes R_q R₁ →
      ¬ Commutes R_q R₂ →
        ∃ R_β ∈ ModelFund 3 t n 1, ∃ R₁' ∈ ModelFund 3 t n 1, ∃ R₂' ∈ ModelFund 3 t n 1,
          LinkedIn (ModelFund 3 t n 1) R R₁ R₁' ∧ LinkedIn (ModelFund 3 t n 1) R R₂ R₂' ∧
          (∃ W, LinearBlockStandardPair (GaloisField 3 1) W R R_β) ∧
          (∃ W, LinearBlockStandardPair (GaloisField 3 1) W R₁' R_β) ∧
          (∃ W, LinearBlockStandardPair (GaloisField 3 1) W R₂' R_β)

@[expose] def NoG2D43 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ x y : G, x * y ≠ y * x) →
    ∀ (K : Subgroup G) (z : G), RouteD3Setup K z →
      ∀ (L : Subgroup G) (w : G), L ∈ conjClass3 K → IsClassicalMember3 L w →
        ∀ {ι : Type} (D : LieSystemData3 ι (locQuot (conjClass3 K) w) (locFamily (conjClass3 K) w))
          (i : ι) (n : ℕ), D.kind i ≠ CompData.model .G2 n ∧ D.kind i ≠ CompData.model .trialityD4 n

end Facts

section Lift


variable {G : Type} [Group G] [Finite G] {ι : Type} {Ω : Set (Subgroup G)} {x : G}

theorem members_chain_of_commConnected3 (hΩ : InClass3 Ω) (hex : ExactMembers3 Ω)
    (hP1 : LocalOddCentral Ω {x}) (hO3 : LocalOddThreeFree3 Ω x)
    (D : LieSystemData3 ι (locQuot Ω x) (locFamily Ω x)) {i : ι}
    (hsc : ∀ R ∈ (D.kind i).fund, ∀ R' ∈ (D.kind i).fund, ∃ g, R' = conjSub g R)
    (hk : PowCop3 (D.kind i)) (hcc : CommFamilyConnected (D.kind i).fund) :
    ∀ A ∈ compMembers3 Ω x D i, ∀ B ∈ compMembers3 Ω x D i, Relation.ReflTransGen
      (fun U V : Subgroup G => U ∈ compMembers3 Ω x D i ∧ V ∈ compMembers3 Ω x D i ∧
        Commutes U V) A B := by
  intro A hA B hB
  obtain ⟨R_A, hRA⟩ := exists_corr_left3 hΩ hex hP1 hO3 D hA
  obtain ⟨R_B, hRB⟩ := exists_corr_left3 hΩ hex hP1 hO3 D hB
  have key : ∀ X, Relation.ReflTransGen
      (fun U V : Subgroup (D.kind i).G => U ∈ (D.kind i).fund ∧ V ∈ (D.kind i).fund ∧
        Commutes U V) R_A X →
      ∃ N, Corr3 Ω x D i N X ∧ Relation.ReflTransGen
        (fun U V : Subgroup G => U ∈ compMembers3 Ω x D i ∧ V ∈ compMembers3 Ω x D i ∧
          Commutes U V) A N := by
    intro X hX
    induction hX with
    | refl => exact ⟨A, hRA, Relation.ReflTransGen.refl⟩
    | @tail U V _ huv ih =>
      obtain ⟨N, hN, hlink⟩ := ih
      obtain ⟨N', hN'⟩ := exists_corr_right3 hΩ D hsc huv.2.1
      have hNm : N ∈ compMembers3 Ω x D i := ⟨hN.1, hN.2.2 ▸ Subgroup.map_le_range _ _⟩
      have hN'm : N' ∈ compMembers3 Ω x D i := ⟨hN'.1, hN'.2.2 ▸ Subgroup.map_le_range _ _⟩
      exact ⟨N', hN', hlink.tail ⟨hNm, hN'm,
        (corr_commutes3 hΩ hex hP1 hO3 hk hN hN').mpr huv.2.2⟩⟩
  obtain ⟨N, hN, hlink⟩ := key R_B (hcc R_A hRA.2.1 R_B hRB.2.1)
  have : N = B := corr_unique_right3 hΩ hex hP1 hO3 hN hRB
  rwa [this] at hlink

theorem linked_of_linkedIn3 (hΩ : InClass3 Ω) (hex : ExactMembers3 Ω)
    (hP1 : LocalOddCentral Ω {x}) (hO3 : LocalOddThreeFree3 Ω x)
    (D : LieSystemData3 ι (locQuot Ω x) (locFamily Ω x)) {i : ι}
    (hsc : ∀ R ∈ (D.kind i).fund, ∀ R' ∈ (D.kind i).fund, ∃ g, R' = conjSub g R)
    (hk : PowCop3 (D.kind i)) {K N N' : Subgroup G} {R_K R_N R_N' : Subgroup (D.kind i).G}
    {z : G} (hz : z ∈ K) (hK : Corr3 Ω x D i K R_K) (hN : Corr3 Ω x D i N R_N)
    (hN' : Corr3 Ω x D i N' R_N') (hlink : LinkedIn (D.kind i).fund R_K R_N R_N') :
    Linked Ω z N N' := by
  have key : ∀ X, LinkedIn (D.kind i).fund R_K R_N X →
      ∃ M, Corr3 Ω x D i M X ∧ Linked Ω z N M := by
    intro X hX
    induction hX with
    | refl => exact ⟨N, hN, Relation.ReflTransGen.refl⟩
    | @tail U V _ huv ih =>
      obtain ⟨M, hM, hlinkM⟩ := ih
      obtain ⟨M', hM'⟩ := exists_corr_right3 hΩ D hsc huv.2.1
      have hMK : Commutes M K := (corr_commutes3 hΩ hex hP1 hO3 hk hM hK).mpr huv.2.2.1
      have hM'K : Commutes M' K := (corr_commutes3 hΩ hex hP1 hO3 hk hM' hK).mpr huv.2.2.2.1
      have hMz : M ∈ centralizingMembers Ω {z} :=
        mem_centralizingMembers_of_commutes hM.1.1 hz hMK
      have hM'z : M' ∈ centralizingMembers Ω {z} :=
        mem_centralizingMembers_of_commutes hM'.1.1 hz hM'K
      have hnc : ¬ Commutes M M' := fun hc =>
        huv.2.2.2.2 ((corr_commutes3 hΩ hex hP1 hO3 hk hM hM').mp hc)
      exact ⟨M', hM', hlinkM.trans (Linked.single ⟨hMz, hM'z, hnc⟩)⟩
  obtain ⟨M, hM, hlinkM⟩ := key R_N' hlink
  have : M = N' := corr_unique_right3 hΩ hex hP1 hO3 hM hN'
  rwa [this] at hlinkM

end Lift

section Main


@[expose] def MultiStar3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ x y : G, x * y ≠ y * x) →
    ∀ (K : Subgroup G) (z : G), RouteD3Setup K z → LocalOddThreeFree3 (conjClass3 K) z →
      ∀ {ι : Type} (D : LieSystemData3 ι (locQuot (conjClass3 K) z) (locFamily (conjClass3 K) z)),
        (∃ i j : ι, i ≠ j ∧ ¬ IsA1Comp3 D i ∧ ¬ IsA1Comp3 D j) →
          ∃ (i₁ i₂ : ι) (a₁ a₂ β : Subgroup G), i₁ ≠ i₂ ∧ ¬ IsA1Comp3 D i₁ ∧
            ¬ IsA1Comp3 D i₂ ∧ a₁ ∈ compMembers3 (conjClass3 K) z D i₁ ∧
            a₂ ∈ compMembers3 (conjClass3 K) z D i₂ ∧ β ∈ conjClass3 K ∧
            (∃ W, LinearBlockStandardPair (GaloisField 3 1) W K β) ∧
            (∃ W, LinearBlockStandardPair (GaloisField 3 1) W a₁ β) ∧
            (∃ W, LinearBlockStandardPair (GaloisField 3 1) W a₂ β)

theorem local_conj3 {G : Type} [Group G] [Finite G] {K : Subgroup G} {z : G} (hc : LocCtx3 K z)
    {c : Subgroup G} (hcΩ : c ∈ conjClass3 K) {y : G} (hyc : IsClassicalMember3 c y) :
    LocalOddCentral (conjClass3 K) {y} ∧ LocalOddThreeFree3 (conjClass3 K) y := by
  obtain ⟨g, hg⟩ := single_class3 K c hcΩ
  have hcl : IsClassicalMember3 c (g * z * g⁻¹) := by
    rw [hg]
    exact hc.hz.conj g
  have hyeq : g * z * g⁻¹ = y := involution_unique3 hcl hyc
  rw [← hyeq]
  exact ⟨Gaps.localOddCentral_conj hc.hΩ.conjInvariant g z hc.hP1,
    localOddThreeFree3_conj hc.hΩ.conjInvariant g z hc.hO3⟩


theorem multiStar3_of_modelFacts (hconn : ModelConnFactNe3) (hstar : ModelStarFact3)
    (hno : NoG2D43) : MultiStar3 := by
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
  have hD0 := hno G hnab K z h K z hK h.cls D
  have hG2 : t ≠ .G2 := fun e => (hD0 i₀ n).1 (by rw [hk₀, e])
  have hD4 : t ≠ .trialityD4 := fun e => (hD0 i₀ n).2 (by rw [hk₀, e])
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
  have hDy := hno G hnab K z h c' y hcΩ hyc Dy
  have hG2' : t' ≠ .G2 := fun e => (hDy iq n').1 (by rw [hk', e])
  have hD4' : t' ≠ .trialityD4 := fun e => (hDy iq n').2 (by rw [hk', e])
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

end Main

end CFSG.ClassicalInvolution.Q3.Q3W
