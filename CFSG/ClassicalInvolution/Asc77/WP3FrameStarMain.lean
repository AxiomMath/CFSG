module

public import CFSG.ClassicalInvolution.Asc77.WP3FrameStar

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.Assembly.Dichotomy CFSG.ComponentClassification CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Generic.DeltaClosure
  CFSG.ClassicalInvolution.Generic.CoreAssembly CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Balance.Bootstrap CFSG.ClassicalInvolution.Balance.BootRank3
  CFSG.ClassicalInvolution.Disconnected

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem stage2_of_balanced_gen [IsSimpleGroup G] (hnab : ∃ a b : G, a * b ≠ b * a)
    (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : InClass p f Ω) (hIH : LocalLieSystems p f Ω)
    {A : Subgroup G} (hA : RankThreeBalance A) {L₀ : Subgroup G} {z₀ : G} (hL₀Ω : L₀ ∈ Ω)
    (hz₀ : IsClassicalMember p f L₀ z₀) (hz₀A : z₀ ∈ A)
    (hL₀A : L₀ ≤ Subgroup.centralizer (A : Set G)) (hgen : rankTwoSpan A = ⊤) :
    (∀ F ∈ signalizerFunctorEk 2 2 A, deltaCore F = ⊥) ∧
      ∀ x : G, x ≠ 1 → (∀ K ∈ centMembers Ω x, ∃ g : G, x ∈ conjSub g A ∧
        InCommonComponent x K (conjSub g L₀)) → LocalOddCentral Ω {x} := by
  have hΔ := deltaCore_eq_bot_of_rankThreeBalance hA
    (componentClassificationOddCore_eq_bot_of_simple hnab) hgen
  exact ⟨hΔ, fun x hx1 hcov => localOddCentral_of_conj_data hnab hp2 hq
    CFSG.ClassicalInvolution.ModelFacts.modelClauseZero fundamentalWholeA1 hΩ hIH hA.elem hA.card
    hΔ hL₀Ω hz₀ hz₀A hL₀A hx1 hcov⟩

theorem exactMembers_and_localOddCentral_of_balanced_gen [IsSimpleGroup G]
    (hnab : ∃ a b : G, a * b ≠ b * a) (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : InClass p f Ω)
    (hsingle : ∃ K ∈ Ω, ∀ L ∈ Ω, ∃ g : G, L = conjSub g K) (hIH : LocalLieSystems p f Ω)
    {A : Subgroup G} (hA : RankThreeBalance A) {L₀ : Subgroup G} {z₀ : G} (hL₀Ω : L₀ ∈ Ω)
    (hz₀ : IsClassicalMember p f L₀ z₀) (hz₀A : z₀ ∈ A)
    (hL₀A : L₀ ≤ Subgroup.centralizer (A : Set G)) (hgen : rankTwoSpan A = ⊤) {a : G}
    (ha1 : a ≠ 1) (haClassical : ∃ M ∈ Ω, IsClassicalMember p f M a)
    (hcover : ∀ K ∈ centMembers Ω a, ¬ IsClassicalMember p f K a →
      ∃ g : G, a ∈ conjSub g A ∧ InCommonComponent a K (conjSub g L₀))
    (hnine : p ^ f = 9 → ∃ x ∈ A, x ≠ 1 ∧ (∀ K ∈ centMembers Ω x, ∃ g : G, x ∈ conjSub g A ∧
      InCommonComponent x K (conjSub g L₀)) ∧ LocalLeviComponent p f Ω x) :
    ExactMembers Ω ∧ ∀ L ∈ Ω, ∀ z : G, IsClassicalMember p f L z → LocalOddCentral Ω {z} := by
  have hf : 0 < f := pos_of_five_le hq
  obtain ⟨hΔ, hP1⟩ := stage2_of_balanced_gen hnab hp2 hq hΩ hIH hA hL₀Ω hz₀ hz₀A hL₀A hgen
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

namespace FuzzyFrameDataStar

variable {L₀ : Subgroup G} {z₀ : G} {A : Subgroup G} {S : Set (Subgroup G)} {a : G}

theorem cent [IsSimpleGroup G] (hnab : ∃ x y : G, x * y ≠ y * x) (hp2 : p ≠ 2)
    (hq : 5 ≤ p ^ f) (hΩ : InClass p f Ω) (hconn : DConnected Ω)
    (h : FuzzyFrameDataStar p f Ω L₀ z₀ A S a) (hbal : RankThreeBalance A) :
    L₀ ≤ Subgroup.centralizer (A : Set G) := by
  have hO := componentClassificationOddCore_eq_bot_of_simple hnab
  have hgen : rankTwoSpan A = ⊤ := rankTwoSpan_eq_top_of_dConnected_star hp2 hq hΩ h.frame hconn
  have hc := h.cls.isCentralInvolution
  have hz2 : z₀ * z₀ = 1 := hbal.mul_self h.z₀A
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro g hg
  by_cases hg1 : g = 1
  · rw [hg1, one_mul, mul_one]
  by_cases hgz : g = z₀
  · rw [hgz]
    exact hc.central x hx
  have hg2 : g * g = 1 := hbal.mul_self hg
  have hcomm : z₀ * g = g * z₀ := hbal.comm h.z₀A hg
  have hFA : Subgroup.closure ({z₀, g} : Set G) ≤ A := by
    rw [Subgroup.closure_le]
    rintro y (rfl | hy)
    · exact h.z₀A
    · rw [Set.mem_singleton_iff.mp hy]
      exact hg
  have hcard : Nat.card (Subgroup.closure ({z₀, g} : Set G)) = 4 :=
    card_closure_pair_eq_four hz2 hg2 hc.ne_one hg1 (fun e => hgz e.symm) hcomm
  have hF : Subgroup.closure ({z₀, g} : Set G) ∈ signalizerFunctorEk 2 2 A :=
    ⟨hFA, by rw [hcard]; norm_num⟩
  have hα : alphaCore (Subgroup.closure ({z₀, g} : Set G)) = ⊥ :=
    TypeCSetup.alphaCore_eq_bot_of_rankTwoSpan_eq_top hO hbal hgen hF
  exact Theorem5.mem_centralizer_of_alphaCore_eq_bot h.cls (h.tq hg) hg2 hc.ne_one hα x hx

end FuzzyFrameDataStar

theorem exactMembers_and_localOddCentral_of_fuzzyFrameStar [IsSimpleGroup G]
    (hnab : ∃ x y : G, x * y ≠ y * x) (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : InClass p f Ω)
    (hsingle : ∃ K ∈ Ω, ∀ L ∈ Ω, ∃ g : G, L = conjSub g K) (hIH : LocalLieSystems p f Ω)
    (hconn : DConnected Ω) {L₀ : Subgroup G} {z₀ : G} {A : Subgroup G} {S : Set (Subgroup G)}
    {a : G} (h : FuzzyFrameDataStar p f Ω L₀ z₀ A S a) (hbal : RankThreeBalance A) :
    ExactMembers Ω ∧ ∀ L ∈ Ω, ∀ z : G, IsClassicalMember p f L z → LocalOddCentral Ω {z} :=
  exactMembers_and_localOddCentral_of_balanced_gen hnab hp2 hq hΩ hsingle hIH hbal h.mem h.cls
    h.z₀A (h.cent hnab hp2 hq hΩ hconn hbal)
    (rankTwoSpan_eq_top_of_dConnected_star hp2 hq hΩ h.frame hconn) h.a1 h.aClassical h.cover
    h.nine

theorem bootNoTripleD_of_frameExistsStar (h52 : Lemma52) (h : FrameExistsStar p f) :
    BootNoTripleD p f := by
  intro G _ _ _ hnab hp2 hq K z hz hBelow hconn _ _
  obtain ⟨L₀, z₀, A, S, a, hfr, hA⟩ := h G hnab hp2 hq K z hz hBelow hconn trivial
  have hΩ := inClass_conjugates hz
  have hIH := localLieSystems_of_citBelowU hΩ hBelow
  obtain ⟨hex, hP1⟩ := exactMembers_and_localOddCentral_of_fuzzyFrameStar hnab hp2 hq hΩ
    (exists_single_class K) hIH hconn hfr (h52 G A hA)
  exact ⟨hex, hP1 K (mem_conjClass_self K) z hz⟩

theorem exactP1D_of_frameExistsStar (h52 : Lemma52) (h : FrameExistsStar p f) :
    ExactP1D p f := by
  intro G _ _ _ hnab hp2 hq hBelow K z hz _ _ hD
  obtain ⟨L₀, z₀, A, S, a, hfr, hA⟩ := h G hnab hp2 hq K z hz hBelow hD trivial
  have hΩ := inClass_conjugates hz
  have hIH := localLieSystems_of_citBelowU hΩ hBelow
  obtain ⟨hex, hP1⟩ := exactMembers_and_localOddCentral_of_fuzzyFrameStar hnab hp2 hq hΩ
    (exists_single_class K) hIH hD hfr (h52 G A hA)
  exact ⟨hex, hP1 K (mem_conjClass_self K) z hz⟩

theorem FrameExistsOn.mono {P Q : ShapePred}
    (hPQ : ∀ (G : Type) [Group G] [Finite G] (K : Subgroup G) (z : G), Q G K z → P G K z)
    (h : FrameExistsOn p f P) : FrameExistsOn p f Q :=
  fun G _ _ _ hnab hp2 hq K z hz hB hD hQ => h G hnab hp2 hq K z hz hB hD (hPQ G K z hQ)

theorem FrameExistsOn.or {P Q : ShapePred} (hP : FrameExistsOn p f P)
    (hQ : FrameExistsOn p f Q) :
    FrameExistsOn p f fun (G : Type) [Group G] [Finite G] (K : Subgroup G) (z : G) =>
      P G K z ∨ Q G K z :=
  fun G _ _ _ hnab hp2 hq K z hz hB hD hPQ => hPQ.elim (hP G hnab hp2 hq K z hz hB hD)
    (hQ G hnab hp2 hq K z hz hB hD)

theorem frameExistsStar_of_cover {P : ShapePred} (hP : FrameExistsOn p f P)
    (hcover : ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ x y : G, x * y ≠ y * x) →
      ∀ (K : Subgroup G) (z : G), IsClassicalMember p f K z → CITBelowU p f (Nat.card G) →
        DConnected (CoreAssembly.conjClass K) → P G K z) :
    FrameExistsStar p f :=
  fun G _ _ _ hnab hp2 hq K z hz hB hD _ => hP G hnab hp2 hq K z hz hB hD
    (hcover G hnab K z hz hB hD)

end CFSG.ClassicalInvolution.Asc77
