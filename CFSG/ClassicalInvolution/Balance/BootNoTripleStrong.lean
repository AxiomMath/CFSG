module

public import CFSG.ClassicalInvolution.Balance.BootNoTriple
public import CFSG.ClassicalInvolution.Balance.StrongLocalBalancePow
import CFSG.ClassicalInvolution.ModelFacts.ClauseZero

public section

namespace CFSG.ClassicalInvolution.Balance.BootRank3

open CFSG.Assembly.Dichotomy CFSG.Assembly.LowTwoRank CFSG.ComponentClassification
  CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Generic.DeltaClosure CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.ClassicalInvolution.Generic.CoreAssembly CFSG.ClassicalInvolution.Balance.StrongBalance
open CFSG.Open (IsElemAbelian)
open scoped commutatorElement

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

section Statement

@[expose] def StrongPowOn (ord : StatedLieTag → ℕ) (Q : StatedLieTag → ℕ → ℕ → ℕ → Prop) : Prop :=
  ∀ t : StatedLieTag, StrongLocalTwoBalanceToralPowOn (ord t) t (Q t)

@[expose] def ToralComponentsAt (p : ℕ) [Fact p.Prime] (ord : StatedLieTag → ℕ)
    (Q : StatedLieTag → ℕ → ℕ → ℕ → Prop) (Ω : Set (Subgroup G)) (A : Subgroup G) (a : G) :
    Prop :=
  ∀ L : Subgroup (OddQuot a), CFSG.IsComponent L → IsOddLieComponentBig L →
    L ≤ memberJoin Ω a → ∀ F₀ : Subgroup G, IsFaithfulFourGroupAt A a L F₀ →
      ∃ (t : StatedLieTag) (n e : ℕ) (hp : p.Prime)
        (ψ : (modelUniv t n p e hp).K →* OddQuot a), Q t n p e ∧ IsFundTag t ∧
          StatedLieAdmissible t n p e ∧ 5 ≤ p ^ e ∧
          ψ.ker ≤ Subgroup.center (modelUniv t n p e hp).K ∧ ψ.range = L ∧
          ToralActionPow (ord t) ψ (modOdd a F₀)

theorem StrongPowOn.mono {ord : StatedLieTag → ℕ} {Q Q' : StatedLieTag → ℕ → ℕ → ℕ → Prop}
    (h : StrongPowOn ord Q) (hQ : ∀ t n p e, Q' t n p e → Q t n p e) : StrongPowOn ord Q' :=
  fun t => (h t).mono fun n p e => hQ t n p e

theorem StrongPowOn.mono_order {ord ord' : StatedLieTag → ℕ}
    {Q : StatedLieTag → ℕ → ℕ → ℕ → Prop} (hord : ∀ t, ord t ∣ ord' t)
    (h : StrongPowOn ord' Q) : StrongPowOn ord Q := fun t => (h t).mono_order (hord t)

omit [Finite G] in
theorem ToralComponentsAt.mono_order {ord ord' : StatedLieTag → ℕ}
    {Q : StatedLieTag → ℕ → ℕ → ℕ → Prop} (hord : ∀ t, ord t ∣ ord' t) {Ω : Set (Subgroup G)}
    {A : Subgroup G} {a : G} (h : ToralComponentsAt p ord Q Ω A a) :
    ToralComponentsAt p ord' Q Ω A a := by
  intro L hL hbig hjoin F₀ hF
  obtain ⟨t, n, e, hp, ψ, hq, hfund, hadm, h5, hker, hrange, htoral⟩ := h L hL hbig hjoin F₀ hF
  exact ⟨t, n, e, hp, ψ, hq, hfund, hadm, h5, hker, hrange, htoral.mono (hord t)⟩

theorem StrongPowOn.of_toral {ord : StatedLieTag → ℕ} {Q : StatedLieTag → ℕ → ℕ → ℕ → Prop}
    (h : ∀ t, StrongLocalTwoBalanceToralOn t (Q t)) : StrongPowOn ord Q :=
  fun t n p e hp hq hfund hadm hp2 h5 X _ _ ψ hker hnorm F hcard hF2 hfaith htoral =>
    h t n p e hp hq hfund hadm hp2 h5 X ψ hker hnorm F hcard hF2 hfaith htoral.toralAction

omit [Finite G] in
theorem ToralComponentsAt.mono {ord : StatedLieTag → ℕ}
    {Q Q' : StatedLieTag → ℕ → ℕ → ℕ → Prop}
    (hQ : ∀ t n p e, Q t n p e → Q' t n p e) {Ω : Set (Subgroup G)} {A : Subgroup G} {a : G}
    (h : ToralComponentsAt p ord Q Ω A a) : ToralComponentsAt p ord Q' Ω A a := by
  intro L hL hbig hjoin F₀ hF
  obtain ⟨t, n, e, hp, ψ, hq, hrest⟩ := h L hL hbig hjoin F₀ hF
  exact ⟨t, n, e, hp, ψ, hQ t n p e hq, hrest⟩

end Statement


section Delta

theorem twoBalancedWrt_of_member_of_delta {A : Subgroup G} (hA : IsElemAbelian 2 A)
    {L₀ : Subgroup G} {z₀ : G} (hL₀Ω : L₀ ∈ Ω) (hz₀ : IsClassicalMember p f L₀ z₀)
    (hz₀A : z₀ ∈ A) (hL₀A : L₀ ≤ Subgroup.centralizer (A : Set G))
    (htri : ∀ a ∈ A, a ≠ 1 → ∀ L : Subgroup (OddQuot a), CFSG.IsComponent L →
      OmegaFreeAt Ω a L ∨ RankOneAt Ω a L ∨ (IsOddLieComponentBig L ∧ L ≤ memberJoin Ω a))
    (hdelta : ∀ a ∈ A, a ≠ 1 → ∀ L : Subgroup (OddQuot a), CFSG.IsComponent L →
      IsOddLieComponentBig L → L ≤ memberJoin Ω a → ∀ F₀ : Subgroup G,
        IsFaithfulFourGroupAt A a L F₀ → ∀ d ∈ deltaCore (modOdd a F₀), conjSub d L = L →
          ∀ x ∈ L, d * x = x * d)
    (hfree : ∀ a ∈ A, a ≠ 1 → ∀ F₀ : Subgroup G, F₀ ≤ A → Nat.card F₀ = 4 → z₀ ∉ F₀ →
      ∀ L : Subgroup (OddQuot a), CFSG.IsComponent L → (OmegaFreeAt Ω a L ∨ RankOneAt Ω a L) →
        ∃ f ∈ modOdd a F₀, f ≠ 1 ∧ ∀ y ∈ L, f * y = y * f) :
    TwoBalancedWrt A := by
  refine twoBalancedWrt_of_quotient_deltaCore_eq_bot hA.1 ?_
  intro a ha ha1 F₀ hF₀
  obtain ⟨hF₀E, hF₀card⟩ := hF₀
  have h4 : Nat.card F₀ = 4 := by rw [hF₀card]; norm_num
  have hFC : F₀ ≤ Subgroup.centralizer ({a} : Set G) := by
    intro f hf
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact congrArg Subtype.val (hA.1.is_comm.comm (⟨f, hF₀E hf⟩ : A) ⟨a, ha⟩)
  have hF2 : ∀ f ∈ F₀, f * f = 1 := fun f hf => by
    rw [← pow_two]
    exact hA.2 f (hF₀E hf)
  have hF2bar : ∀ f ∈ modOdd a F₀, f * f = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    have hx' : (x : G) ∈ F₀ := hx
    rw [← map_mul]
    have : x * x = 1 := Subtype.ext (hF2 _ hx')
    rw [this, map_one]
  have hcentral : ∀ L : Subgroup (OddQuot a), CFSG.IsComponent L →
      (OmegaFreeAt Ω a L ∨ RankOneAt Ω a L) →
      ∃ f ∈ modOdd a F₀, f ≠ 1 ∧ ∀ y ∈ L, f * y = y * f := by
    intro L hLc hL
    by_cases hz : z₀ ∈ F₀
    · have hzC : z₀ ∈ Subgroup.centralizer ({a} : Set G) := hFC hz
      refine ⟨oddQuotMk a ⟨z₀, hzC⟩, oddQuotMk_mem_modOdd hz hzC, ?_, fun y hy =>
        oddQuotMk_centralizes_of_isCentralInvolution hL₀Ω
          (hL₀A.trans (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr ha)))
          hz₀.isCentralInvolution hzC hL y hy⟩
      intro h
      have hsq : (⟨z₀, hzC⟩ : ↥(Subgroup.centralizer ({a} : Set G))) * ⟨z₀, hzC⟩ = 1 :=
        Subtype.ext (by rw [← pow_two]; exact hA.2 z₀ hz₀A)
      exact hz₀.ne_one (congrArg Subtype.val (eq_one_of_oddQuotMk_eq_one hsq h))
    · exact hfree a ha ha1 F₀ hF₀E h4 hz L hLc hL
  show deltaCore (modOdd a F₀) = ⊥
  refine deltaCore_eq_bot_of_faithful_centralized (pPrimeCore_oddQuot_eq_bot a)
    (by rw [card_modOdd_of_exponent_two hFC hF2, h4]) hF2bar ?_
  intro L hL hFn hfaith d hd hdL x hx
  rcases htri a ha ha1 L hL with h | h | ⟨hbig, hjoin⟩
  · obtain ⟨f, hf, hf1, hfc⟩ := hcentral L hL (Or.inl h)
    exact absurd hfc (hfaith f hf hf1)
  · obtain ⟨f, hf, hf1, hfc⟩ := hcentral L hL (Or.inr h)
    exact absurd hfc (hfaith f hf hf1)
  · exact hdelta a ha ha1 L hL hbig hjoin F₀ ⟨hF₀E, h4, hFn, hfaith⟩ d hd hdL x hx

theorem delta_centralizes_of_strongPow {ord : StatedLieTag → ℕ}
    {Q : StatedLieTag → ℕ → ℕ → ℕ → Prop} (hS : StrongPowOn ord Q) (hp2 : p ≠ 2)
    {A : Subgroup G} (hA2 : ∀ x ∈ A, x * x = 1) {a : G} (ha : a ∈ A)
    (hdata : ToralComponentsAt p ord Q Ω A a) :
    ∀ L : Subgroup (OddQuot a), CFSG.IsComponent L → IsOddLieComponentBig L →
      L ≤ memberJoin Ω a → ∀ F₀ : Subgroup G, IsFaithfulFourGroupAt A a L F₀ →
        ∀ d ∈ deltaCore (modOdd a F₀), conjSub d L = L → ∀ x ∈ L, d * x = x * d := by
  intro L hL hbig hjoin F₀ hF d hd hdL x hx
  obtain ⟨t, n, e, hp, ψ, hQ, hfund, hadm, h5, hker, hrange, htoral⟩ :=
    hdata L hL hbig hjoin F₀ hF
  obtain ⟨hF₀A, h4, hFn, hfaith⟩ := hF
  have hFC : F₀ ≤ Subgroup.centralizer ({a} : Set G) := by
    intro g hg
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (comm_of_sq_eq_one hA2 ha (hF₀A hg)).symm
  have hF2 : ∀ g ∈ F₀, g * g = 1 := fun g hg => hA2 g (hF₀A hg)
  have hcard : Nat.card (modOdd a F₀) = 4 := by rw [card_modOdd_of_exponent_two hFC hF2, h4]
  have hF2bar := modOdd_sq_eq_one (a := a) hA2 hF₀A
  subst hrange
  have key := commute_of_strongLocalTwoBalanceToralPow (hS t) hp hQ hfund hadm hp2 h5 ψ hker
    hcard hF2bar hfaith hFn htoral
  exact key d hd (mem_normalizer_of_conjSub_eq hdL) x hx

end Delta

section Boot

theorem rankThreeBalance_of_bootData_strong [IsSimpleGroup G]
    (hnab : ∃ a b : G, a * b ≠ b * a) (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) (h27 : p ^ f ≠ 27)
    (hΩ : InClass p f Ω) (hIH : LocalLieSystems p f Ω) {ord : StatedLieTag → ℕ}
    {Q : StatedLieTag → ℕ → ℕ → ℕ → Prop} (hS : StrongPowOn ord Q) {A : Subgroup G}
    (hA : IsElemAbelian 2 A) (hcard : Nat.card A = 8)
    {L₀ : Subgroup G} {z₀ : G} (hL₀Ω : L₀ ∈ Ω) (hz₀ : IsClassicalMember p f L₀ z₀)
    (hz₀A : z₀ ∈ A) (hL₀A : L₀ ≤ Subgroup.centralizer (A : Set G))
    (hbad : ∀ a ∈ A, a ≠ 1 → ∀ b ∈ A, b ≠ 1 → A ≠ Subgroup.closure ({z₀, a, b} : Set G) →
      ⁅involutionOddCore a ⊓ Subgroup.centralizer {b}, A⁆ ≤ involutionOddCore b)
    (htoral : ∀ a ∈ A, a ≠ 1 → ToralComponentsAt p ord Q Ω A a)
    (hfree : ∀ b ∈ A, b ≠ 1 → ∀ L : Subgroup (OddQuot b), CFSG.IsComponent L →
      (OmegaFreeAt Ω b L ∨ RankOneAt Ω b L) → LargeCentralizerOn A b L) :
    RankThreeBalance A :=
  ⟨hA, hcard,
    weakBalanced_of_pairs hnab hp2 hq CFSG.ClassicalInvolution.ModelFacts.modelClauseZero
      fundamentalWholeA1 hΩ hIH hA hL₀Ω hz₀ hz₀A hL₀A hbad,
    twoBalancedWrt_of_member_of_delta hA hL₀Ω hz₀ hz₀A hL₀A
      (fun a _ ha1 L hL => omegaFreeAt_or_rankOneAt_or_isOddLieComponentBig hp2
        CFSG.ClassicalInvolution.ModelFacts.modelClauseZero fundamentalWholeA1 hq hΩ hIH
        (not_subset_center_of_ne_one hnab ha1) (NoComponentOverF3.of_ne_27 a hq h27) hL)
      (fun a ha ha1 => delta_centralizes_of_strongPow hS hp2
        (fun x hx => by rw [← pow_two]; exact hA.2 x hx) ha (htoral a ha ha1))
      fun a ha ha1 _ hF₀A hF₀4 _ L hL hLF =>
        exists_mem_ne_one_centralizes_of_large hA hcard (hfree a ha ha1 L hL hLF) hF₀A hF₀4⟩

theorem exactMembers_and_localOddCentral_of_good_strong [IsSimpleGroup G]
    (hnab : ∃ a b : G, a * b ≠ b * a) (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) (h27 : p ^ f ≠ 27)
    (hΩ : InClass p f Ω) (hsingle : ∃ K ∈ Ω, ∀ L ∈ Ω, ∃ g : G, L = conjSub g K)
    (hIH : LocalLieSystems p f Ω) (hconn : OmegaConnected Ω) {ord : StatedLieTag → ℕ}
    {Q : StatedLieTag → ℕ → ℕ → ℕ → Prop} (hS : StrongPowOn ord Q) {L₀ : Subgroup G} {z₀ : G}
    {A : Subgroup G} {S : Set (Subgroup G)} {a : G} (h : GoodBootData p f Ω L₀ z₀ A S a)
    (htoral : ∀ b ∈ A, b ≠ 1 → ToralComponentsAt p ord Q Ω A b) :
    ExactMembers Ω ∧ ∀ L ∈ Ω, ∀ z : G, IsClassicalMember p f L z → LocalOddCentral Ω {z} :=
  exactMembers_and_localOddCentral_of_balanced hnab hp2 hq hΩ hsingle hIH hconn
    (rankThreeBalance_of_bootData_strong hnab hp2 hq h27 hΩ hIH hS h.elem h.card h.mem h.cls
      h.z₀A h.cent h.badPairs htoral h.free)
    h.mem h.cls h.z₀A h.cent h.frame h.a1 h.aClassical h.cover h.nine

@[expose] def GoodBootDataToralExists (p f : ℕ) [Fact p.Prime] (ord : StatedLieTag → ℕ)
    (Q : StatedLieTag → ℕ → ℕ → ℕ → Prop) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ x y : G, x * y ≠ y * x) →
    p ≠ 2 → 5 ≤ p ^ f → ∀ (K : Subgroup G) (z : G), IsClassicalMember p f K z →
      CITBelowU p f (Nat.card G) →
      CFSG.ClassicalInvolution.RouteD.DeltaConnected (CoreAssembly.conjClass K) →
      BootData p f (CoreAssembly.conjClass K) → ¬ IndepTriple p f (CoreAssembly.conjClass K) →
      ∃ (L₀ : Subgroup G) (z₀ : G) (A : Subgroup G) (S : Set (Subgroup G)) (a : G),
        GoodBootData p f (CoreAssembly.conjClass K) L₀ z₀ A S a ∧
          ∀ b ∈ A, b ≠ 1 → ToralComponentsAt p ord Q (CoreAssembly.conjClass K) A b

theorem GoodBootDataToralExists.mono {ord : StatedLieTag → ℕ}
    {Q Q' : StatedLieTag → ℕ → ℕ → ℕ → Prop} (hQ : ∀ t n p e, Q t n p e → Q' t n p e)
    (h : GoodBootDataToralExists p f ord Q) : GoodBootDataToralExists p f ord Q' := by
  intro G _ _ _ hnab hp2 hq K z hz hBelow hconn hdata hT
  obtain ⟨L₀, z₀, A, S, a, hgood, htoral⟩ := h G hnab hp2 hq K z hz hBelow hconn hdata hT
  exact ⟨L₀, z₀, A, S, a, hgood, fun b hb hb1 => (htoral b hb hb1).mono hQ⟩

theorem bootNoTriple_of_goodBootData_strong (h27 : p ^ f ≠ 27) {ord : StatedLieTag → ℕ}
    {Q : StatedLieTag → ℕ → ℕ → ℕ → Prop} (hS : StrongPowOn ord Q)
    (h : GoodBootDataToralExists p f ord Q) : BootNoTriple p f := by
  intro G _ _ _ hnab hp2 hq K z hz hBelow hconn hdata hT
  obtain ⟨L₀, z₀, A, S, a, hgood, htoral⟩ := h G hnab hp2 hq K z hz hBelow hconn hdata hT
  have hΩ := inClass_conjugates hz
  have hIH := localLieSystems_of_citBelowU hΩ hBelow
  obtain ⟨hex, hP1⟩ := exactMembers_and_localOddCentral_of_good_strong hnab hp2 hq h27 hΩ
    (exists_single_class K) hIH (omegaConnected_of_routeD hconn) hS hgood htoral
  exact ⟨hex, hP1 K (mem_conjClass_self K) z hz⟩

theorem bootNoTriple_of_parts_strong {ord : StatedLieTag → ℕ}
    {Q : StatedLieTag → ℕ → ℕ → ℕ → Prop} (hS : StrongPowOn ord Q)
    (hgood : GoodBootDataToralExists p f ord Q) (h27 : p ^ f = 27 → BootNoTriple p f) :
    BootNoTriple p f := by
  by_cases h : p ^ f = 27
  · exact h27 h
  · exact bootNoTriple_of_goodBootData_strong h hS hgood

@[expose] def StrongFourAll : Prop := StrongPowOn (fun _ => 4) fun _ _ _ _ => True

theorem bootNoTriple_of_parts_all (hS : StrongFourAll)
    (hgood : GoodBootDataToralExists p f (fun _ => 4) fun _ _ _ _ => True)
    (h27 : p ^ f = 27 → BootNoTriple p f) : BootNoTriple p f :=
  bootNoTriple_of_parts_strong hS hgood h27

end Boot

end CFSG.ClassicalInvolution.Balance.BootRank3
