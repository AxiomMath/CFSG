module

public import CFSG.ClassicalInvolution.Balance.BootNoTriple
public import CFSG.ClassicalInvolution.Balance.BootNoTripleDFrame

public section

namespace CFSG.ClassicalInvolution.Disconnected

open CFSG.Open CFSG.Assembly.Dichotomy CFSG.ComponentClassification CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Generic.DeltaClosure
  CFSG.ClassicalInvolution.Balance.Bootstrap CFSG.ClassicalInvolution.Generic.CoreAssembly
  CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.BootRank3
open scoped commutatorElement

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem stage2_of_balanced_bootDataD [IsSimpleGroup G] (hnab : ∃ a b : G, a * b ≠ b * a)
    (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : InClass p f Ω) (hIH : LocalLieSystems p f Ω)
    {A : Subgroup G} (hA : RankThreeBalance A) {L₀ : Subgroup G} {z₀ : G} (hL₀Ω : L₀ ∈ Ω)
    (hz₀ : IsClassicalMember p f L₀ z₀) (hz₀A : z₀ ∈ A)
    (hL₀A : L₀ ≤ Subgroup.centralizer (A : Set G)) {S : Set (Subgroup G)}
    (hF : FrameSideTwoD p f Ω A S) (hconn : DConnected Ω) :
    (∀ F ∈ signalizerFunctorEk 2 2 A, deltaCore F = ⊥) ∧
      ∀ x : G, x ≠ 1 → (∀ K ∈ centMembers Ω x, ∃ g : G, x ∈ conjSub g A ∧
        InCommonComponent x K (conjSub g L₀)) → LocalOddCentral Ω {x} := by
  have hgen : (⨆ F ∈ signalizerFunctorEk 2 2 A, Subgroup.centralizer (F : Set G)) = ⊤ :=
    rankTwoSpan_eq_top_of_dConnected hp2 hq hΩ hF hconn
  have hΔ := deltaCore_eq_bot_of_rankThreeBalance hA
    (componentClassificationOddCore_eq_bot_of_simple hnab) hgen
  exact ⟨hΔ, fun x hx1 hcov => localOddCentral_of_conj_data hnab hp2 hq
    CFSG.ClassicalInvolution.ModelFacts.modelClauseZero fundamentalWholeA1 hΩ hIH hA.elem hA.card
    hΔ hL₀Ω hz₀ hz₀A hL₀A hx1 hcov⟩

theorem exactMembers_and_localOddCentral_of_balancedD [IsSimpleGroup G]
    (hnab : ∃ a b : G, a * b ≠ b * a) (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : InClass p f Ω)
    (hsingle : ∃ K ∈ Ω, ∀ L ∈ Ω, ∃ g : G, L = conjSub g K) (hIH : LocalLieSystems p f Ω)
    (hconn : DConnected Ω) {A : Subgroup G} (hA : RankThreeBalance A) {L₀ : Subgroup G}
    {z₀ : G} (hL₀Ω : L₀ ∈ Ω) (hz₀ : IsClassicalMember p f L₀ z₀) (hz₀A : z₀ ∈ A)
    (hL₀A : L₀ ≤ Subgroup.centralizer (A : Set G)) {S : Set (Subgroup G)}
    (hF : FrameSideTwoD p f Ω A S) {a : G} (ha1 : a ≠ 1)
    (haClassical : ∃ M ∈ Ω, IsClassicalMember p f M a)
    (hcover : ∀ K ∈ centMembers Ω a, ¬ IsClassicalMember p f K a →
      ∃ g : G, a ∈ conjSub g A ∧ InCommonComponent a K (conjSub g L₀))
    (hnine : p ^ f = 9 → ∃ x ∈ A, x ≠ 1 ∧ (∀ K ∈ centMembers Ω x, ∃ g : G, x ∈ conjSub g A ∧
      InCommonComponent x K (conjSub g L₀)) ∧ LocalLeviComponent p f Ω x) :
    ExactMembers Ω ∧ ∀ L ∈ Ω, ∀ z : G, IsClassicalMember p f L z → LocalOddCentral Ω {z} := by
  have hf : 0 < f := pos_of_five_le hq
  obtain ⟨hΔ, hP1⟩ := stage2_of_balanced_bootDataD hnab hp2 hq hΩ hIH hA hL₀Ω hz₀ hz₀A hL₀A hF
    hconn
  have hP1a : LocalOddCentral Ω {a} := by
    refine hP1 a ha1 fun K hK => ?_
    by_cases hKa : IsClassicalMember p f K a
    · exact cover_of_involution hnab hp2 hq hΩ hsingle hIH hL₀Ω hz₀ hz₀A ha1 hK hKa
    · exact hcover K hK hKa
  refine ⟨?_, ?_⟩
  · by_cases h9 : p ^ f = 9
    · obtain ⟨x, -, hx1, hcov, hlevi⟩ := hnine h9
      exact exactMembers_of_localLeviComponent hp2 hq hΩ hsingle (hP1 x hx1 hcov) hlevi
    · obtain ⟨F₀, hF₀⟩ := CFSG.SignalizerFunctor.Helpers.signalizerFunctorEk_nonempty 2 2
        Nat.prime_two A hA.elem (by rw [hA.card]; norm_num)
      exact exactMembers_of_deltaCore_eq_bot hnab hp2 hq h9
        CFSG.ClassicalInvolution.ModelFacts.modelClauseZero fundamentalWholeA1 hΩ hsingle hIH
        hL₀Ω hz₀ (CFSG.SignalizerFunctor.Helpers.elementary_abelian_of_le 2 hA.elem hF₀.1)
        (hL₀A.trans (Subgroup.centralizer_le hF₀.1)) (hΔ F₀ hF₀)
  · obtain ⟨M, hMΩ, hM⟩ := haClassical
    exact localOddCentral_of_classicalMember hp2 hf hΩ hsingle hMΩ hM hP1a

structure GoodBootDataD (p f : ℕ) [Fact p.Prime] {G : Type} [Group G] [Finite G]
    (Ω : Set (Subgroup G)) (L₀ : Subgroup G) (z₀ : G) (A : Subgroup G) (S : Set (Subgroup G))
    (a : G) : Prop where
  mem : L₀ ∈ Ω
  cls : IsClassicalMember p f L₀ z₀
  elem : IsElemAbelian 2 A
  card : Nat.card A = 8
  z₀A : z₀ ∈ A
  cent : L₀ ≤ Subgroup.centralizer (A : Set G)
  badPairs : ∀ b ∈ A, b ≠ 1 → ∀ c ∈ A, c ≠ 1 → A ≠ Subgroup.closure ({z₀, b, c} : Set G) →
    ⁅involutionOddCore b ⊓ Subgroup.centralizer {c}, A⁆ ≤ involutionOddCore c
  frame : FrameSideTwoD p f Ω A S
  free : ∀ b ∈ A, b ≠ 1 → ∀ L : Subgroup (OddQuot b), CFSG.IsComponent L →
    (OmegaFreeAt Ω b L ∨ RankOneAt Ω b L) → LargeCentralizerOn A b L
  aA : a ∈ A
  a1 : a ≠ 1
  aClassical : ∃ M ∈ Ω, IsClassicalMember p f M a
  cover : ∀ K ∈ centMembers Ω a, ¬ IsClassicalMember p f K a →
    ∃ g : G, a ∈ conjSub g A ∧ InCommonComponent a K (conjSub g L₀)
  nine : p ^ f = 9 → ∃ x ∈ A, x ≠ 1 ∧ (∀ K ∈ centMembers Ω x, ∃ g : G, x ∈ conjSub g A ∧
    InCommonComponent x K (conjSub g L₀)) ∧ LocalLeviComponent p f Ω x

theorem exactMembers_and_localOddCentral_of_goodD [IsSimpleGroup G]
    (hnab : ∃ a b : G, a * b ≠ b * a) (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : InClass p f Ω)
    (hsingle : ∃ K ∈ Ω, ∀ L ∈ Ω, ∃ g : G, L = conjSub g K) (hIH : LocalLieSystems p f Ω)
    (hconn : DConnected Ω) {L₀ : Subgroup G} {z₀ : G} {A : Subgroup G}
    {S : Set (Subgroup G)} {a : G} (h : GoodBootDataD p f Ω L₀ z₀ A S a)
    (hloc : ∀ b ∈ A, b ≠ 1 → ComponentLayersAt Ω A b) :
    ExactMembers Ω ∧ ∀ L ∈ Ω, ∀ z : G, IsClassicalMember p f L z → LocalOddCentral Ω {z} :=
  exactMembers_and_localOddCentral_of_balancedD hnab hp2 hq hΩ hsingle hIH hconn
    (rankThreeBalance_of_bootData hnab hp2 hq hΩ hIH h.elem h.card h.mem h.cls h.z₀A h.cent
      h.badPairs hloc h.free)
    h.mem h.cls h.z₀A h.cent h.frame h.a1 h.aClassical h.cover h.nine

end CFSG.ClassicalInvolution.Disconnected
