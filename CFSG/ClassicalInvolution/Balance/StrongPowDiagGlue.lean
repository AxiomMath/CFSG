module

public import CFSG.ClassicalInvolution.Balance.BootNoTripleStrong
public import CFSG.ClassicalInvolution.Balance.StrongPowDiagDefs
import CFSG.ClassicalInvolution.ModelFacts.ClauseZero

public section

namespace CFSG.ClassicalInvolution.Balance.BootRank3

open CFSG.Assembly.Dichotomy CFSG.Assembly.LowTwoRank CFSG.ComponentClassification
  CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Generic.DeltaClosure CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.ClassicalInvolution.Generic.CoreAssembly CFSG.ClassicalInvolution.Balance.StrongBalance
open CFSG.ClassicalInvolution.Balance.LocalBalance (subgroupOf_involutionOddCore_le)
open CFSG.Open (IsElemAbelian)
open CFSG.ClassicalInvolution.Phan (Su)
open CFSG.ComponentClassification.CatalogueBHigherLinearAction (slConjugation)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher (conjSp)
open scoped commutatorElement MatrixGroups

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

section Transfer

variable {X : Type*} [Group X] {N : Subgroup X}

theorem ToralDiagGL.subgroupOf {k n : ℕ} {F : Type} [Field F] {ψ : SL(n, F) →* X}
    {ψ' : SL(n, F) →* N} (hψ : ∀ y, (ψ' y : X) = ψ y) {F₀ : Subgroup X}
    (h : ToralDiagGL k ψ F₀) : ToralDiagGL k ψ' (F₀.subgroupOf N) := by
  obtain ⟨P, hP, hact⟩ := h
  refine ⟨P, hP, fun f hf => ?_⟩
  obtain ⟨x, hxP, hxk, hxa⟩ := hact f.1 hf
  refine ⟨x, hxP, hxk, fun y => Subtype.ext ?_⟩
  have h := hxa y
  rw [← hψ y, ← hψ (slConjugation n F x y)] at h
  exact h

theorem ToralDiagGU.subgroupOf {k : ℕ} {K : Type} [Field K] [Finite K] {p' f₀ : ℕ}
    [Fact p'.Prime] [CharP K p'] {n : ℕ} {ψ : Su K p' f₀ n →* X} {ψ' : Su K p' f₀ n →* N}
    (hψ : ∀ y, (ψ' y : X) = ψ y) {F₀ : Subgroup X} (h : ToralDiagGU k ψ F₀) :
    ToralDiagGU k ψ' (F₀.subgroupOf N) := by
  obtain ⟨P, hP, hact⟩ := h
  refine ⟨P, hP, fun f hf => ?_⟩
  obtain ⟨x, hxP, hxk, hxa⟩ := hact f.1 hf
  refine ⟨x, hxP, hxk, fun y => Subtype.ext ?_⟩
  have h := hxa y
  rw [← hψ y,
    ← hψ (conjSUid (CFSG.LieType.BorelTits.unitaryInvolution K p' f₀) n x y)] at h
  exact h

theorem ToralDiagGSp.subgroupOf {k n : ℕ} {F : Type} [Field F] {ψ : StatedSp n F →* X}
    {ψ' : StatedSp n F →* N} (hψ : ∀ y, (ψ' y : X) = ψ y) {F₀ : Subgroup X}
    (h : ToralDiagGSp k ψ F₀) : ToralDiagGSp k ψ' (F₀.subgroupOf N) := by
  obtain ⟨P, hP, hact⟩ := h
  refine ⟨P, hP, fun f hf => ?_⟩
  obtain ⟨x, hxP, hxk, hxa⟩ := hact f.1 hf
  refine ⟨x, hxP, hxk, fun y => Subtype.ext ?_⟩
  have h := hxa y
  rw [← hψ y, ← hψ (conjSp n F x y)] at h
  exact h

theorem ToralDiagOrth.subgroupOf {k : ℕ} {F V : Type} [Field F] [AddCommGroup V] [Module F V]
    {Q : QuadraticForm F V} {ψ : spinGroup Q →* X} {ψ' : spinGroup Q →* N}
    (hψ : ∀ y, (ψ' y : X) = ψ y) {F₀ : Subgroup X} (h : ToralDiagOrth k ψ F₀) :
    ToralDiagOrth k ψ' (F₀.subgroupOf N) := by
  obtain ⟨P, hP, hO, hact⟩ := h
  refine ⟨P, hP, hO, fun f hf => ?_⟩
  obtain ⟨s, hsP, hsk, α, hα, hαa⟩ := hact f.1 hf
  refine ⟨s, hsP, hsk, α, hα, fun y => Subtype.ext ?_⟩
  have h := hαa y
  rw [← hψ y, ← hψ (α y)] at h
  exact h

theorem ToralActionDiag.subgroupOf {k : ℕ} {t : StatedLieTag} {n p' e : ℕ} {hp : p'.Prime}
    {X' : Type} [Group X'] {N' : Subgroup X'} {ψ : (modelUniv t n p' e hp).K →* X'}
    {ψ' : (modelUniv t n p' e hp).K →* N'} (hψ : ∀ y, (ψ' y : X') = ψ y) {F₀ : Subgroup X'}
    (h : ToralActionDiag k t n p' e hp ψ F₀) :
    ToralActionDiag k t n p' e hp ψ' (F₀.subgroupOf N') := by
  have : Fact p'.Prime := ⟨hp⟩
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
  refine ⟨fun ht => ?_, fun ht => ?_, fun ht => ?_, fun ht => ?_, fun ht => ?_, fun ht => ?_,
    fun h1 h2 h3 h4 h5 h6 => ?_⟩
  · obtain ⟨ε, hε⟩ := h1 ht
    exact ⟨ε, ToralDiagGL.subgroupOf (fun y => hψ _) hε⟩
  · obtain ⟨ε, hε⟩ := h2 ht
    exact ⟨ε, ToralDiagGU.subgroupOf (fun y => hψ _) hε⟩
  · obtain ⟨ε, hε⟩ := h3 ht
    exact ⟨ε, ToralDiagGSp.subgroupOf (fun y => hψ _) hε⟩
  · obtain ⟨ε, hε⟩ := h4 ht
    exact ⟨ε, ToralDiagOrth.subgroupOf (fun y => hψ _) hε⟩
  · obtain ⟨ε, hε⟩ := h5 ht
    exact ⟨ε, ToralDiagOrth.subgroupOf (fun y => hψ _) hε⟩
  · obtain ⟨ε, hε⟩ := h6 ht
    exact ⟨ε, ToralDiagOrth.subgroupOf (fun y => hψ _) hε⟩
  · obtain ⟨P, hP, hact⟩ := h7 h1 h2 h3 h4 h5 h6
    refine ⟨P, hP, fun f hf => ?_⟩
    obtain ⟨x, hxP, hxk, hxa⟩ := hact f.1 hf
    refine ⟨x, hxP, hxk, fun y => Subtype.ext ?_⟩
    have h := hxa y
    rw [← hψ y, ← hψ (x * y * x⁻¹)] at h
    exact h

end Transfer

section Statement

@[expose] def DeltaDiagOn (k : ℕ) (t : StatedLieTag) (Q : ℕ → ℕ → ℕ → Prop) : Prop :=
  ∀ (n p e : ℕ) (hp : p.Prime), Q n p e → IsFundTag t → StatedLieAdmissible t n p e →
    p ≠ 2 → 5 ≤ p ^ e →
    ∀ (X : Type) [Group X] [Finite X] (ψ : (modelUniv t n p e hp).K →* X),
      ψ.ker ≤ Subgroup.center (modelUniv t n p e hp).K → ψ.range.Normal →
      ∀ F : Subgroup X, Nat.card F = 4 → (∀ f ∈ F, f * f = 1) →
        (∀ f ∈ F, f ≠ 1 → ¬ ∀ x ∈ ψ.range, f * x = x * f) →
        ToralActionDiag k t n p e hp ψ F → ∀ d ∈ deltaCore F, ∀ x ∈ ψ.range, d * x = x * d

@[expose] def DeltaDiagAll (ord : StatedLieTag → ℕ)
    (Q : StatedLieTag → ℕ → ℕ → ℕ → Prop) : Prop :=
  ∀ t : StatedLieTag, DeltaDiagOn (ord t) t (Q t)

theorem DeltaDiagOn.mono {k : ℕ} {t : StatedLieTag} {Q Q' : ℕ → ℕ → ℕ → Prop}
    (h : DeltaDiagOn k t Q) (hQ : ∀ n p e, Q' n p e → Q n p e) : DeltaDiagOn k t Q' :=
  fun n p e hp hq => h n p e hp (hQ n p e hq)

theorem DeltaDiagAll.mono {ord : StatedLieTag → ℕ} {Q Q' : StatedLieTag → ℕ → ℕ → ℕ → Prop}
    (h : DeltaDiagAll ord Q) (hQ : ∀ t n p e, Q' t n p e → Q t n p e) : DeltaDiagAll ord Q' :=
  fun t => (h t).mono fun n p e => hQ t n p e

@[expose] def ToralComponentsDiagAt (p : ℕ) [Fact p.Prime] (ord : StatedLieTag → ℕ)
    (Q : StatedLieTag → ℕ → ℕ → ℕ → Prop) (Ω : Set (Subgroup G)) (A : Subgroup G) (a : G) :
    Prop :=
  ∀ L : Subgroup (OddQuot a), CFSG.IsComponent L → IsOddLieComponentBig L →
    L ≤ memberJoin Ω a → ∀ F₀ : Subgroup G, IsFaithfulFourGroupAt A a L F₀ →
      ∃ (t : StatedLieTag) (n e : ℕ) (hp : p.Prime)
        (ψ : (modelUniv t n p e hp).K →* OddQuot a), Q t n p e ∧ IsFundTag t ∧
          StatedLieAdmissible t n p e ∧ 5 ≤ p ^ e ∧
          ψ.ker ≤ Subgroup.center (modelUniv t n p e hp).K ∧ ψ.range = L ∧
          ToralActionDiag (ord t) t n p e hp ψ (modOdd a F₀)

end Statement

theorem commute_of_deltaDiag {k : ℕ} {t : StatedLieTag} {Q : ℕ → ℕ → ℕ → Prop}
    (hSB : DeltaDiagOn k t Q) {n p e : ℕ} (hp : p.Prime) (hq : Q n p e) (hfund : IsFundTag t)
    (hadm : StatedLieAdmissible t n p e) (hp2 : p ≠ 2) (h5 : 5 ≤ p ^ e) {X : Type} [Group X]
    [Finite X] (ψ : (modelUniv t n p e hp).K →* X)
    (hker : ψ.ker ≤ Subgroup.center (modelUniv t n p e hp).K) {F : Subgroup X}
    (hcard : Nat.card F = 4) (hF2 : ∀ f ∈ F, f * f = 1)
    (hfaith : ∀ f ∈ F, f ≠ 1 → ¬ ∀ x ∈ ψ.range, f * x = x * f)
    (hFN : F ≤ Subgroup.normalizer (ψ.range : Set X)) (htoral : ToralActionDiag k t n p e hp ψ F) :
    ∀ d ∈ deltaCore F, d ∈ Subgroup.normalizer (ψ.range : Set X) →
      ∀ x ∈ ψ.range, d * x = x * d := by
  set N : Subgroup X := Subgroup.normalizer (ψ.range : Set X) with hN
  have hrN : ψ.range ≤ N := Subgroup.le_normalizer
  set ψ' : (modelUniv t n p e hp).K →* ↥N := ψ.codRestrict N fun k => hrN ⟨k, rfl⟩ with hψ'
  have hker' : ψ'.ker ≤ Subgroup.center (modelUniv t n p e hp).K := fun y hy =>
    hker (MonoidHom.mem_ker.mpr (congrArg Subtype.val (MonoidHom.mem_ker.mp hy)))
  have hrange : ψ'.range = ψ.range.subgroupOf N := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨x, rfl⟩
    · rintro ⟨x, hx⟩
      exact ⟨x, Subtype.ext hx⟩
  have hnorm' : ψ'.range.Normal := by
    rw [hrange, Subgroup.normal_subgroupOf_iff_le_normalizer hrN]
  set F' : Subgroup ↥N := F.subgroupOf N with hF'
  have hF'4 : Nat.card F' = 4 := by
    rw [← hcard]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hFN).toEquiv
  have hF'2 : ∀ f ∈ F', f * f = 1 := fun f hf => Subtype.ext (hF2 f.1 hf)
  have hfaith' : ∀ f ∈ F', f ≠ 1 → ¬ ∀ x ∈ ψ'.range, f * x = x * f := by
    intro f hf hf1 hc
    refine hfaith f.1 hf (fun h => hf1 (Subtype.ext h)) fun x hx => ?_
    have hx' : (⟨x, hrN hx⟩ : ↥N) ∈ ψ'.range := by
      rw [hrange]
      exact hx
    exact congrArg Subtype.val (hc _ hx')
  have htoral' : ToralActionDiag k t n p e hp ψ' F' :=
    ToralActionDiag.subgroupOf (fun y => rfl) htoral
  have hSC := hSB n p e hp hq hfund hadm hp2 h5 ↥N ψ' hker' hnorm' F' hF'4 hF'2 hfaith' htoral'
  have hxmem : ∀ x (hx : x ∈ ψ.range), (⟨x, hrN hx⟩ : ↥N) ∈ ψ'.range := fun x hx => by
    rw [hrange]
    exact hx
  intro d hd hdN x hx
  have hd' : (⟨d, hdN⟩ : ↥N) ∈ deltaCore F' := by
    rw [mem_deltaCore_iff]
    intro f' hf' hf'1
    have hf1 : (f' : X) ≠ 1 := fun h => hf'1 (Subtype.ext h)
    exact subgroupOf_involutionOddCore_le f' (Subgroup.mem_subgroupOf.mpr
      (mem_deltaCore_iff.mp hd (f' : X) hf' hf1))
  exact congrArg Subtype.val (hSC _ hd' _ (hxmem x hx))

section Delta

theorem delta_centralizes_of_deltaDiag {ord : StatedLieTag → ℕ}
    {Q : StatedLieTag → ℕ → ℕ → ℕ → Prop} (hS : DeltaDiagAll ord Q) (hp2 : p ≠ 2)
    {A : Subgroup G} (hA2 : ∀ x ∈ A, x * x = 1) {a : G} (ha : a ∈ A)
    (hdata : ToralComponentsDiagAt p ord Q Ω A a) :
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
  have key := commute_of_deltaDiag (hS t) hp hQ hfund hadm hp2 h5 ψ hker hcard hF2bar hfaith hFn
    htoral
  exact key d hd (mem_normalizer_of_conjSub_eq hdL) x hx

end Delta

section Boot

theorem rankThreeBalance_of_bootData_diag [IsSimpleGroup G]
    (hnab : ∃ a b : G, a * b ≠ b * a) (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) (h27 : p ^ f ≠ 27)
    (hΩ : InClass p f Ω) (hIH : LocalLieSystems p f Ω) {ord : StatedLieTag → ℕ}
    {Q : StatedLieTag → ℕ → ℕ → ℕ → Prop} (hS : DeltaDiagAll ord Q) {A : Subgroup G}
    (hA : IsElemAbelian 2 A) (hcard : Nat.card A = 8)
    {L₀ : Subgroup G} {z₀ : G} (hL₀Ω : L₀ ∈ Ω) (hz₀ : IsClassicalMember p f L₀ z₀)
    (hz₀A : z₀ ∈ A) (hL₀A : L₀ ≤ Subgroup.centralizer (A : Set G))
    (hbad : ∀ a ∈ A, a ≠ 1 → ∀ b ∈ A, b ≠ 1 → A ≠ Subgroup.closure ({z₀, a, b} : Set G) →
      ⁅involutionOddCore a ⊓ Subgroup.centralizer {b}, A⁆ ≤ involutionOddCore b)
    (htoral : ∀ a ∈ A, a ≠ 1 → ToralComponentsDiagAt p ord Q Ω A a)
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
      (fun a ha ha1 => delta_centralizes_of_deltaDiag hS hp2
        (fun x hx => by rw [← pow_two]; exact hA.2 x hx) ha (htoral a ha ha1))
      fun a ha ha1 _ hF₀A hF₀4 _ L hL hLF =>
        exists_mem_ne_one_centralizes_of_large hA hcard (hfree a ha ha1 L hL hLF) hF₀A hF₀4⟩

theorem exactMembers_and_localOddCentral_of_good_diag [IsSimpleGroup G]
    (hnab : ∃ a b : G, a * b ≠ b * a) (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) (h27 : p ^ f ≠ 27)
    (hΩ : InClass p f Ω) (hsingle : ∃ K ∈ Ω, ∀ L ∈ Ω, ∃ g : G, L = conjSub g K)
    (hIH : LocalLieSystems p f Ω) (hconn : OmegaConnected Ω) {ord : StatedLieTag → ℕ}
    {Q : StatedLieTag → ℕ → ℕ → ℕ → Prop} (hS : DeltaDiagAll ord Q) {L₀ : Subgroup G} {z₀ : G}
    {A : Subgroup G} {S : Set (Subgroup G)} {a : G} (h : GoodBootData p f Ω L₀ z₀ A S a)
    (htoral : ∀ b ∈ A, b ≠ 1 → ToralComponentsDiagAt p ord Q Ω A b) :
    ExactMembers Ω ∧ ∀ L ∈ Ω, ∀ z : G, IsClassicalMember p f L z → LocalOddCentral Ω {z} :=
  exactMembers_and_localOddCentral_of_balanced hnab hp2 hq hΩ hsingle hIH hconn
    (rankThreeBalance_of_bootData_diag hnab hp2 hq h27 hΩ hIH hS h.elem h.card h.mem h.cls
      h.z₀A h.cent h.badPairs htoral h.free)
    h.mem h.cls h.z₀A h.cent h.frame h.a1 h.aClassical h.cover h.nine

@[expose] def GoodBootDataDiagExists (p f : ℕ) [Fact p.Prime] (ord : StatedLieTag → ℕ)
    (Q : StatedLieTag → ℕ → ℕ → ℕ → Prop) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ x y : G, x * y ≠ y * x) →
    p ≠ 2 → 5 ≤ p ^ f → ∀ (K : Subgroup G) (z : G), IsClassicalMember p f K z →
      CITBelowU p f (Nat.card G) →
      CFSG.ClassicalInvolution.RouteD.DeltaConnected (CoreAssembly.conjClass K) →
      BootData p f (CoreAssembly.conjClass K) → ¬ IndepTriple p f (CoreAssembly.conjClass K) →
      ∃ (L₀ : Subgroup G) (z₀ : G) (A : Subgroup G) (S : Set (Subgroup G)) (a : G),
        GoodBootData p f (CoreAssembly.conjClass K) L₀ z₀ A S a ∧
          ∀ b ∈ A, b ≠ 1 → ToralComponentsDiagAt p ord Q (CoreAssembly.conjClass K) A b

theorem GoodBootDataDiagExists.mono {ord : StatedLieTag → ℕ}
    {Q Q' : StatedLieTag → ℕ → ℕ → ℕ → Prop} (hQ : ∀ t n p e, Q t n p e → Q' t n p e)
    (h : GoodBootDataDiagExists p f ord Q) : GoodBootDataDiagExists p f ord Q' := by
  intro G _ _ _ hnab hp2 hq K z hz hBelow hconn hdata hT
  obtain ⟨L₀, z₀, A, S, a, hgood, htoral⟩ := h G hnab hp2 hq K z hz hBelow hconn hdata hT
  refine ⟨L₀, z₀, A, S, a, hgood, fun b hb hb1 => ?_⟩
  intro L hL hbig hjoin F₀ hF
  obtain ⟨t, n, e, hp, ψ, hq', rest⟩ := htoral b hb hb1 L hL hbig hjoin F₀ hF
  exact ⟨t, n, e, hp, ψ, hQ t n p e hq', rest⟩

theorem bootNoTriple_of_goodBootData_diag (h27 : p ^ f ≠ 27) {ord : StatedLieTag → ℕ}
    {Q : StatedLieTag → ℕ → ℕ → ℕ → Prop} (hS : DeltaDiagAll ord Q)
    (h : GoodBootDataDiagExists p f ord Q) : BootNoTriple p f := by
  intro G _ _ _ hnab hp2 hq K z hz hBelow hconn hdata hT
  obtain ⟨L₀, z₀, A, S, a, hgood, htoral⟩ := h G hnab hp2 hq K z hz hBelow hconn hdata hT
  have hΩ := inClass_conjugates hz
  have hIH := localLieSystems_of_citBelowU hΩ hBelow
  obtain ⟨hex, hP1⟩ := exactMembers_and_localOddCentral_of_good_diag hnab hp2 hq h27 hΩ
    (exists_single_class K) hIH (omegaConnected_of_routeD hconn) hS hgood htoral
  exact ⟨hex, hP1 K (mem_conjClass_self K) z hz⟩

theorem bootNoTriple_of_parts_diag {ord : StatedLieTag → ℕ}
    {Q : StatedLieTag → ℕ → ℕ → ℕ → Prop} (hS : DeltaDiagAll ord Q)
    (hgood : GoodBootDataDiagExists p f ord Q) (h27 : p ^ f = 27 → BootNoTriple p f) :
    BootNoTriple p f := by
  by_cases h : p ^ f = 27
  · exact h27 h
  · exact bootNoTriple_of_goodBootData_diag h hS hgood

end Boot

end CFSG.ClassicalInvolution.Balance.BootRank3
