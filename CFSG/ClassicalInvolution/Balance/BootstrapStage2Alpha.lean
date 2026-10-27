module

public import CFSG.ClassicalInvolution.Balance.BootstrapAlphaDelta
public import CFSG.ClassicalInvolution.Balance.BootstrapStage2
public import CFSG.ClassicalInvolution.Balance.BootstrapWeakBalance

public section

namespace CFSG.ClassicalInvolution.Balance.Bootstrap

open CFSG.Open CFSG.Assembly.Dichotomy CFSG.ComponentClassification CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Generic.DeltaClosure

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem weakBalanced_of_exactTriple [IsSimpleGroup G] (hnab : ∃ a b : G, a * b ≠ b * a)
    (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) (h0 : ModelClauseZero) (hA1 : FundamentalWholeA1)
    (hΩ : InClass p f Ω) (hIH : LocalLieSystems p f Ω) {K₁ K₂ K₃ : Subgroup G} {z₁ z₂ z₃ : G}
    (T : ExactTriple K₁ K₂ K₃ z₁ z₂ z₃) (hΩ₁ : K₁ ∈ Ω) (hΩ₂ : K₂ ∈ Ω) (hΩ₃ : K₃ ∈ Ω)
    (hz₁ : IsClassicalMember p f K₁ z₁) (hz₂ : IsClassicalMember p f K₂ z₂)
    (hz₃ : IsClassicalMember p f K₃ z₃) : WeakBalanced T.group := by
  refine weakBalanced_of_members hnab hp2 hq h0 hA1 hΩ hIH (S := {z₁, z₂, z₃}) T.isElemAbelian
    rfl ?_
  intro z hz
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
  rcases hz with rfl | rfl | rfl
  exacts [⟨K₁, hΩ₁, hz₁, T.le_centralizer₁⟩, ⟨K₂, hΩ₂, hz₂, T.le_centralizer₂⟩,
    ⟨K₃, hΩ₃, hz₃, T.le_centralizer₃⟩]

theorem stage2_of_exactTriple_wb [IsSimpleGroup G] (hnab : ∃ a b : G, a * b ≠ b * a)
    (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) (h9 : p ^ f ≠ 9) (h0 : ModelClauseZero)
    (hA1 : FundamentalWholeA1) (hΩ : InClass p f Ω)
    (hsingle : ∃ K ∈ Ω, ∀ L ∈ Ω, ∃ g : G, L = conjSub g K) (hIH : LocalLieSystems p f Ω)
    {K₁ K₂ K₃ : Subgroup G} {z₁ z₂ z₃ : G} (T : ExactTriple K₁ K₂ K₃ z₁ z₂ z₃)
    (hind : z₁ * z₂ ≠ z₃) (hΩ₁ : K₁ ∈ Ω) (hΩ₂ : K₂ ∈ Ω) (hΩ₃ : K₃ ∈ Ω)
    (hz₁ : IsClassicalMember p f K₁ z₁) (hz₂ : IsClassicalMember p f K₂ z₂)
    (hz₃ : IsClassicalMember p f K₃ z₃) (h2 : TwoBalancedWrt T.group)
    (hgen : (⨆ F ∈ signalizerFunctorEk 2 2 T.group, Subgroup.centralizer (F : Set G)) = ⊤) :
    (∀ F ∈ signalizerFunctorEk 2 2 T.group, deltaCore F = ⊥) ∧
      Stage2 Ω {x | x ∈ T.group ∧ x ≠ 1 ∧ TripleMeetsAt Ω K₁ K₂ K₃ x} := by
  have hWB := weakBalanced_of_exactTriple hnab hp2 hq h0 hA1 hΩ hIH T hΩ₁ hΩ₂ hΩ₃ hz₁ hz₂ hz₃
  have hRB : RankThreeBalance T.group := ⟨T.isElemAbelian, T.card_eq_eight hind, hWB, h2⟩
  exact stage2_of_exactTriple hnab hp2 hq h9 h0 hA1 hΩ hsingle hIH T hind hΩ₁ hΩ₂ hΩ₃ hz₁ hz₂
    hz₃ (centralizedDelta_of_rankThreeBalance hRB
      (componentClassificationOddCore_eq_bot_of_simple hnab) hgen) h2 hgen

theorem generation_of_exactTriple_of_closure (hΩ : InClass p f Ω)
    {K₁ K₂ K₃ : Subgroup G} {z₁ z₂ z₃ : G} (T : ExactTriple K₁ K₂ K₃ z₁ z₂ z₃)
    (hind : z₁ * z₂ ≠ z₃) (hΩ₁ : K₁ ∈ Ω) (hΩ₂ : K₂ ∈ Ω) (hΩ₃ : K₃ ∈ Ω)
    (hz₁ : IsClassicalMember p f K₁ z₁) (hz₂ : IsClassicalMember p f K₂ z₂)
    (hz₃ : IsClassicalMember p f K₃ z₃) (hconn : OmegaConnected Ω)
    (hgenModO : ∀ a ∈ T.group, IsFrameInvolution p f ({K₁, K₂, K₃} : Set (Subgroup G)) a →
      CentralizerGenerationModOTwo Ω T.group a)
    (hlink : ∀ a ∈ T.group, IsFrameInvolution p f ({K₁, K₂, K₃} : Set (Subgroup G)) a →
      InvolutionLink p f Ω T.group ({K₁, K₂, K₃} : Set (Subgroup G)) a) :
    (⨆ F ∈ signalizerFunctorEk 2 2 T.group, Subgroup.centralizer (F : Set G)) = ⊤ := by
  have hz₁A : z₁ ∈ T.group := Subgroup.subset_closure (by simp)
  have hz₂A : z₂ ∈ T.group := Subgroup.subset_closure (by simp)
  have hz₃A : z₃ ∈ T.group := Subgroup.subset_closure (by simp)
  have hF : FrameSideTwo p f Ω T.group ({K₁, K₂, K₃} : Set (Subgroup G)) :=
    { elem := T.isElemAbelian
      card := (T.card_eq_eight hind).ge
      subset := by
        intro K hK
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hK
        rcases hK with rfl | rfl | rfl <;> assumption
      nonempty := ⟨K₁, by simp⟩
      involution := by
        intro K hK
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hK
        rcases hK with rfl | rfl | rfl
        exacts [⟨z₁, hz₁A, hz₁⟩, ⟨z₂, hz₂A, hz₂⟩, ⟨z₃, hz₃A, hz₃⟩]
      generation := hgenModO
      link := hlink }
  exact rankTwoSpan_eq_top hΩ hF hconn

theorem stage2_of_exactTriple_of_closure_wb [IsSimpleGroup G] (hnab : ∃ a b : G, a * b ≠ b * a)
    (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) (h9 : p ^ f ≠ 9) (h0 : ModelClauseZero)
    (hA1 : FundamentalWholeA1) (hΩ : InClass p f Ω)
    (hsingle : ∃ K ∈ Ω, ∀ L ∈ Ω, ∃ g : G, L = conjSub g K) (hIH : LocalLieSystems p f Ω)
    {K₁ K₂ K₃ : Subgroup G} {z₁ z₂ z₃ : G} (T : ExactTriple K₁ K₂ K₃ z₁ z₂ z₃)
    (hind : z₁ * z₂ ≠ z₃) (hΩ₁ : K₁ ∈ Ω) (hΩ₂ : K₂ ∈ Ω) (hΩ₃ : K₃ ∈ Ω)
    (hz₁ : IsClassicalMember p f K₁ z₁) (hz₂ : IsClassicalMember p f K₂ z₂)
    (hz₃ : IsClassicalMember p f K₃ z₃) (h2 : TwoBalancedWrt T.group)
    (hconn : OmegaConnected Ω)
    (hgenModO : ∀ a ∈ T.group, IsFrameInvolution p f ({K₁, K₂, K₃} : Set (Subgroup G)) a →
      CentralizerGenerationModOTwo Ω T.group a)
    (hlink : ∀ a ∈ T.group, IsFrameInvolution p f ({K₁, K₂, K₃} : Set (Subgroup G)) a →
      InvolutionLink p f Ω T.group ({K₁, K₂, K₃} : Set (Subgroup G)) a) :
    (∀ F ∈ signalizerFunctorEk 2 2 T.group, deltaCore F = ⊥) ∧
      Stage2 Ω {x | x ∈ T.group ∧ x ≠ 1 ∧ TripleMeetsAt Ω K₁ K₂ K₃ x} :=
  stage2_of_exactTriple_wb hnab hp2 hq h9 h0 hA1 hΩ hsingle hIH T hind hΩ₁ hΩ₂ hΩ₃ hz₁ hz₂ hz₃ h2
    (generation_of_exactTriple_of_closure hΩ T hind hΩ₁ hΩ₂ hΩ₃ hz₁ hz₂ hz₃ hconn hgenModO
      hlink)

theorem stage2_of_exactTriple_of_layers_wb [IsSimpleGroup G] (hnab : ∃ a b : G, a * b ≠ b * a)
    (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) (h9 : p ^ f ≠ 9) (h0 : ModelClauseZero)
    (hA1 : FundamentalWholeA1) (hΩ : InClass p f Ω)
    (hsingle : ∃ K ∈ Ω, ∀ L ∈ Ω, ∃ g : G, L = conjSub g K) (hIH : LocalLieSystems p f Ω)
    {K₁ K₂ K₃ : Subgroup G} {z₁ z₂ z₃ : G} (T : ExactTriple K₁ K₂ K₃ z₁ z₂ z₃)
    (hind : z₁ * z₂ ≠ z₃) (hΩ₁ : K₁ ∈ Ω) (hΩ₂ : K₂ ∈ Ω) (hΩ₃ : K₃ ∈ Ω)
    (hz₁ : IsClassicalMember p f K₁ z₁) (hz₂ : IsClassicalMember p f K₂ z₂)
    (hz₃ : IsClassicalMember p f K₃ z₃)
    (hloc : ∀ a ∈ T.group, a ≠ 1 → ComponentLayersAt Ω T.group a) (hconn : OmegaConnected Ω)
    (hgenModO : ∀ a ∈ T.group, IsFrameInvolution p f ({K₁, K₂, K₃} : Set (Subgroup G)) a →
      CentralizerGenerationModOTwo Ω T.group a)
    (hlink : ∀ a ∈ T.group, IsFrameInvolution p f ({K₁, K₂, K₃} : Set (Subgroup G)) a →
      InvolutionLink p f Ω T.group ({K₁, K₂, K₃} : Set (Subgroup G)) a) :
    (∀ F ∈ signalizerFunctorEk 2 2 T.group, deltaCore F = ⊥) ∧
      Stage2 Ω {x | x ∈ T.group ∧ x ≠ 1 ∧ TripleMeetsAt Ω K₁ K₂ K₃ x} :=
  stage2_of_exactTriple_of_closure_wb hnab hp2 hq h9 h0 hA1 hΩ hsingle hIH T hind hΩ₁ hΩ₂ hΩ₃ hz₁
    hz₂ hz₃ (twoBalancedWrt_of_exactTriple_of_layers T hΩ₁ hΩ₂ hΩ₃ hloc) hconn hgenModO hlink

theorem exactMembers_and_localOddCentral_of_exactTriple_wb [IsSimpleGroup G]
    (hnab : ∃ a b : G, a * b ≠ b * a) (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) (h9 : p ^ f ≠ 9)
    (h0 : ModelClauseZero) (hA1 : FundamentalWholeA1) (hΩ : InClass p f Ω)
    (hsingle : ∃ K ∈ Ω, ∀ L ∈ Ω, ∃ g : G, L = conjSub g K) (hIH : LocalLieSystems p f Ω)
    {K₁ K₂ K₃ : Subgroup G} {z₁ z₂ z₃ : G} (T : ExactTriple K₁ K₂ K₃ z₁ z₂ z₃)
    (hind : z₁ * z₂ ≠ z₃) (hΩ₁ : K₁ ∈ Ω) (hΩ₂ : K₂ ∈ Ω) (hΩ₃ : K₃ ∈ Ω)
    (hz₁ : IsClassicalMember p f K₁ z₁) (hz₂ : IsClassicalMember p f K₂ z₂)
    (hz₃ : IsClassicalMember p f K₃ z₃)
    (hloc : ∀ a ∈ T.group, a ≠ 1 → ComponentLayersAt Ω T.group a) (hconn : OmegaConnected Ω)
    (hgenModO : ∀ a ∈ T.group, IsFrameInvolution p f ({K₁, K₂, K₃} : Set (Subgroup G)) a →
      CentralizerGenerationModOTwo Ω T.group a)
    (hlink : ∀ a ∈ T.group, IsFrameInvolution p f ({K₁, K₂, K₃} : Set (Subgroup G)) a →
      InvolutionLink p f Ω T.group ({K₁, K₂, K₃} : Set (Subgroup G)) a)
    (hmeet : TripleMeetsAt Ω K₁ K₂ K₃ z₁) :
    ExactMembers Ω ∧ ∀ L ∈ Ω, ∀ z : G, IsClassicalMember p f L z → LocalOddCentral Ω {z} := by
  have hf : 0 < f := by
    rcases Nat.eq_zero_or_pos f with rfl | h
    · simp at hq
    · exact h
  obtain ⟨-, hex, hP1⟩ := stage2_of_exactTriple_of_layers_wb hnab hp2 hq h9 h0 hA1 hΩ hsingle hIH
    T hind hΩ₁ hΩ₂ hΩ₃ hz₁ hz₂ hz₃ hloc hconn hgenModO hlink
  have hz₁A : z₁ ∈ T.group := Subgroup.subset_closure (by simp)
  exact ⟨hex, localOddCentral_of_classicalMember hp2 hf hΩ hsingle hΩ₁ hz₁
    (hP1 z₁ ⟨hz₁A, T.ne_one₁, hmeet⟩)⟩

end CFSG.ClassicalInvolution.Balance.Bootstrap
