module

public import CFSG.ClassicalInvolution.Asc77.WP3FrameStarMain

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.Assembly.Dichotomy CFSG.ComponentClassification CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Generic.DeltaClosure
  CFSG.ClassicalInvolution.Generic.CoreAssembly CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Balance.Bootstrap CFSG.ClassicalInvolution.Balance.BootRank3
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.ExactLayer

section Data

variable (p f : ℕ) [Fact p.Prime] {G : Type} [Group G] [Finite G]

structure FuzzyFrameDataStarE (Ω : Set (Subgroup G)) (L₀ : Subgroup G) (z₀ : G) (A : Subgroup G)
    (S : Set (Subgroup G)) (a : G) : Prop where
  mem : L₀ ∈ Ω
  cls : IsClassicalMember p f L₀ z₀
  z₀A : z₀ ∈ A
  tq : A ≤ trivialOnQuot L₀
  frame : FrameSideTwoStar p f Ω A S
  aA : a ∈ A
  a1 : a ≠ 1
  aClassical : ∃ M ∈ Ω, IsClassicalMember p f M a
  cover : ∀ K ∈ centMembers Ω a, ¬ IsClassicalMember p f K a →
    ∃ g : G, a ∈ conjSub g A ∧ InCommonComponent a K (exactCore a (conjSub g L₀))
  nine : p ^ f = 9 → ∃ x ∈ A, x ≠ 1 ∧ (∀ K ∈ centMembers Ω x, ∃ g : G, x ∈ conjSub g A ∧
    InCommonComponent x K (exactCore x (conjSub g L₀))) ∧ LocalLeviComponent p f Ω x

variable {p f}

omit [Finite G] in
theorem inCommonComponent_exactCore {x : G} {K L : Subgroup G}
    (h : InCommonComponent x K L) : InCommonComponent x K (exactCore x L) := by
  obtain ⟨Q, hQ, hK, hL⟩ := h
  refine ⟨Q, hQ, hK, le_trans ?_ hL⟩
  rintro _ ⟨k, hk, rfl⟩
  exact ⟨k, exactCore_le_left x L hk, rfl⟩

theorem FuzzyFrameDataStar.toE {Ω : Set (Subgroup G)} {L₀ : Subgroup G} {z₀ : G}
    {A : Subgroup G} {S : Set (Subgroup G)} {a : G} (h : FuzzyFrameDataStar p f Ω L₀ z₀ A S a) :
    FuzzyFrameDataStarE p f Ω L₀ z₀ A S a where
  mem := h.mem
  cls := h.cls
  z₀A := h.z₀A
  tq := h.tq
  frame := h.frame
  aA := h.aA
  a1 := h.a1
  aClassical := h.aClassical
  cover K hK hKa := by
    obtain ⟨g, hg, hcc⟩ := h.cover K hK hKa
    exact ⟨g, hg, inCommonComponent_exactCore hcc⟩
  nine h9 := by
    obtain ⟨x, hxA, hx1, hcov, hlevi⟩ := h.nine h9
    refine ⟨x, hxA, hx1, fun K hK => ?_, hlevi⟩
    obtain ⟨g, hg, hcc⟩ := hcov K hK
    exact ⟨g, hg, inCommonComponent_exactCore hcc⟩

end Data

section Main

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

namespace FuzzyFrameDataStarE

variable {L₀ : Subgroup G} {z₀ : G} {A : Subgroup G} {S : Set (Subgroup G)} {a : G}

theorem cent [IsSimpleGroup G] (hnab : ∃ x y : G, x * y ≠ y * x) (hp2 : p ≠ 2)
    (hq : 5 ≤ p ^ f) (hΩ : InClass p f Ω) (hconn : DConnected Ω)
    (h : FuzzyFrameDataStarE p f Ω L₀ z₀ A S a) (hbal : RankThreeBalance A) :
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

theorem exactCore_conj_eq (h : FuzzyFrameDataStarE p f Ω L₀ z₀ A S a)
    (hcent : L₀ ≤ Subgroup.centralizer (A : Set G)) {g x : G} (hx : x ∈ conjSub g A) :
    exactCore x (conjSub g L₀) = conjSub g L₀ := by
  have hperf : Group.IsPerfect ↥(conjSub g L₀) := (h.cls.conj g).perfect
  refine exactCore_eq_self hperf fun y hy => ?_
  rw [Subgroup.mem_centralizer_singleton_iff]
  have hy' : g⁻¹ * y * g ∈ L₀ := mem_conjSub_iff.mp hy
  have hx' : g⁻¹ * x * g ∈ A := mem_conjSub_iff.mp hx
  have hc := Subgroup.mem_centralizer_iff.mp (hcent hy') (g⁻¹ * x * g) hx'
  have e1 : y * x = g * ((g⁻¹ * y * g) * (g⁻¹ * x * g)) * g⁻¹ := by group
  have e2 : x * y = g * ((g⁻¹ * x * g) * (g⁻¹ * y * g)) * g⁻¹ := by group
  rw [e1, e2, hc]

end FuzzyFrameDataStarE

theorem exactMembers_and_localOddCentral_of_fuzzyFrameStarE [IsSimpleGroup G]
    (hnab : ∃ x y : G, x * y ≠ y * x) (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : InClass p f Ω)
    (hsingle : ∃ K ∈ Ω, ∀ L ∈ Ω, ∃ g : G, L = conjSub g K) (hIH : LocalLieSystems p f Ω)
    (hconn : DConnected Ω) {L₀ : Subgroup G} {z₀ : G} {A : Subgroup G} {S : Set (Subgroup G)}
    {a : G} (h : FuzzyFrameDataStarE p f Ω L₀ z₀ A S a) (hbal : RankThreeBalance A) :
    ExactMembers Ω ∧ ∀ L ∈ Ω, ∀ z : G, IsClassicalMember p f L z → LocalOddCentral Ω {z} := by
  have hcent := h.cent hnab hp2 hq hΩ hconn hbal
  have hcov : ∀ (x : G) (K : Subgroup G), (∃ g : G, x ∈ conjSub g A ∧
      InCommonComponent x K (exactCore x (conjSub g L₀))) →
      ∃ g : G, x ∈ conjSub g A ∧ InCommonComponent x K (conjSub g L₀) := by
    rintro x K ⟨g, hg, hcc⟩
    refine ⟨g, hg, ?_⟩
    rwa [h.exactCore_conj_eq hcent hg] at hcc
  exact exactMembers_and_localOddCentral_of_balanced_gen hnab hp2 hq hΩ hsingle hIH hbal h.mem
    h.cls h.z₀A hcent (rankTwoSpan_eq_top_of_dConnected_star hp2 hq hΩ h.frame hconn) h.a1
    h.aClassical (fun K hK hKa => hcov a K (h.cover K hK hKa))
    (fun h9 => by
      obtain ⟨x, hxA, hx1, hcover, hlevi⟩ := h.nine h9
      exact ⟨x, hxA, hx1, fun K hK => hcov x K (hcover K hK), hlevi⟩)

end Main

section Exists

variable (p f : ℕ) [Fact p.Prime]

@[expose] def FrameExistsOnE (P : ShapePred) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ x y : G, x * y ≠ y * x) →
    p ≠ 2 → 5 ≤ p ^ f → ∀ (K : Subgroup G) (z : G), IsClassicalMember p f K z →
      CITBelowU p f (Nat.card G) → DConnected (CoreAssembly.conjClass K) → P G K z →
      ∃ (L₀ : Subgroup G) (z₀ : G) (A : Subgroup G) (S : Set (Subgroup G)) (a : G),
        FuzzyFrameDataStarE p f (CoreAssembly.conjClass K) L₀ z₀ A S a ∧ Hyp51 A

@[expose] def FrameExistsStarE : Prop :=
  FrameExistsOnE p f fun _ _ _ _ _ => True

variable {p f}

theorem FrameExistsOn.toE {P : ShapePred} (h : FrameExistsOn p f P) : FrameExistsOnE p f P :=
  fun G _ _ _ hnab hp2 hq K z hz hB hD hP => by
    obtain ⟨L₀, z₀, A, S, a, hfr, hA⟩ := h G hnab hp2 hq K z hz hB hD hP
    exact ⟨L₀, z₀, A, S, a, hfr.toE, hA⟩

theorem FrameExistsOnE.mono {P Q : ShapePred}
    (hPQ : ∀ (G : Type) [Group G] [Finite G] (K : Subgroup G) (z : G), Q G K z → P G K z)
    (h : FrameExistsOnE p f P) : FrameExistsOnE p f Q :=
  fun G _ _ _ hnab hp2 hq K z hz hB hD hQ => h G hnab hp2 hq K z hz hB hD (hPQ G K z hQ)

theorem FrameExistsOnE.or {P Q : ShapePred} (hP : FrameExistsOnE p f P)
    (hQ : FrameExistsOnE p f Q) :
    FrameExistsOnE p f fun (G : Type) [Group G] [Finite G] (K : Subgroup G) (z : G) =>
      P G K z ∨ Q G K z :=
  fun G _ _ _ hnab hp2 hq K z hz hB hD hPQ => hPQ.elim (hP G hnab hp2 hq K z hz hB hD)
    (hQ G hnab hp2 hq K z hz hB hD)

theorem frameExistsStarE_of_cover {P : ShapePred} (hP : FrameExistsOnE p f P)
    (hcover : ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ x y : G, x * y ≠ y * x) →
      ∀ (K : Subgroup G) (z : G), IsClassicalMember p f K z → CITBelowU p f (Nat.card G) →
        DConnected (CoreAssembly.conjClass K) → P G K z) :
    FrameExistsStarE p f :=
  fun G _ _ _ hnab hp2 hq K z hz hB hD _ => hP G hnab hp2 hq K z hz hB hD
    (hcover G hnab K z hz hB hD)

theorem bootNoTripleD_of_frameExistsStarE (h52 : Lemma52) (h : FrameExistsStarE p f) :
    BootNoTripleD p f := by
  intro G _ _ _ hnab hp2 hq K z hz hBelow hconn _ _
  obtain ⟨L₀, z₀, A, S, a, hfr, hA⟩ := h G hnab hp2 hq K z hz hBelow hconn trivial
  have hΩ := inClass_conjugates hz
  have hIH := localLieSystems_of_citBelowU hΩ hBelow
  obtain ⟨hex, hP1⟩ := exactMembers_and_localOddCentral_of_fuzzyFrameStarE hnab hp2 hq hΩ
    (exists_single_class K) hIH hconn hfr (h52 G A hA)
  exact ⟨hex, hP1 K (mem_conjClass_self K) z hz⟩

theorem exactP1D_of_frameExistsStarE (h52 : Lemma52) (h : FrameExistsStarE p f) :
    ExactP1D p f := by
  intro G _ _ _ hnab hp2 hq hBelow K z hz _ _ hD
  obtain ⟨L₀, z₀, A, S, a, hfr, hA⟩ := h G hnab hp2 hq K z hz hBelow hD trivial
  have hΩ := inClass_conjugates hz
  have hIH := localLieSystems_of_citBelowU hΩ hBelow
  obtain ⟨hex, hP1⟩ := exactMembers_and_localOddCentral_of_fuzzyFrameStarE hnab hp2 hq hΩ
    (exists_single_class K) hIH hD hfr (h52 G A hA)
  exact ⟨hex, hP1 K (mem_conjClass_self K) z hz⟩

end Exists

end CFSG.ClassicalInvolution.Asc77
