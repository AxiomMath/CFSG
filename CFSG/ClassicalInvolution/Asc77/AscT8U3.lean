module

public import CFSG.ClassicalInvolution.Asc77.AscT8U2
public import CFSG.ClassicalInvolution.Asc77.AscE187Img
public import CFSG.ClassicalInvolution.Asc77.WP3LayerSec

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ComponentClassification CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Generic.DeltaClosure
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.Thompson
  CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.ClassicalInvolution.Asc77.ExactLayer
open CFSG.Assembly.Dichotomy (involutionOddCore)
open CFSG.ClassicalInvolution.Balance.Theorem5
  (FuzzyFrameOn fuzzyFrames fuzzyVertices LinkMove)
open CFSG.ClassicalInvolution.Balance.Q27
  (exists_linkDataFree exists_frame_of_cross_free exists_frame_of_comp_free)

namespace T8U

section Frames

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}


theorem mem_trivialOnQuot_of_omegaNbr (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : HypOmegaMod p f Ω)
    {K J : Subgroup G} {z : G} (hz : IsUniqueInvolution K z) (hJ : J ∈ omegaNbr Ω K) :
    z ∈ trivialOnQuot J := by
  have hc2 : IsPGroup 2 (Subgroup.zpowers z) := ExactLayer.isPGroup_zpowers_of_sq_eq_one hz.sq
  obtain ⟨hJΩ, -, T, hT, hTJ, hTN⟩ := hJ
  have hTsyl : IsSylow2In T J := hΩ.isSylow2In_of_mem_RSet_of_le hp hJΩ hT hTJ
  exact (mem_trivialOnQuot_iff_exists_sylow hp hq hΩ hc2 hJΩ).mpr
    ⟨T, hTsyl, T3.le_centralizer_of_le_normalizer' hz hTN⟩

theorem exists_fuzzyFrame_of_trivialOnQuot [IsSimpleGroup G] (hnab : ∃ x y : G, x * y ≠ y * x)
    (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) (K : Subgroup G) (hBelow : CITBelowU p f (Nat.card G))
    {A₀ : Subgroup G} (hA₀ : A₀ ∈ fuzzyFrames p f (canonClass p f K)) {M N : Subgroup G}
    (hM𝒞 : M ∈ canonClass p f K) (hN𝒞 : N ∈ canonClass p f K) {zM zN : G}
    (hM : IsClassicalMember p f M zM) (hN : IsClassicalMember p f N zN)
    (haN : zM ∈ trivialOnQuot N) (hne : zM ≠ zN) :
    ∃ B ∈ fuzzyFrames p f (canonClass p f K), zM ∈ fuzzyVertices p f (canonClass p f K) B ∧
      zN ∈ fuzzyVertices p f (canonClass p f K) B := by
  have hf : 0 < f := Nat.pos_of_ne_zero (by rintro rfl; simp at hq)
  have hinv := conjInvariant_canonClass (p := p) (f := f) K
  have hcan := canonClass_subset (p := p) (f := f) K
  have hua : zN ≠ zM := hne.symm
  obtain ⟨ld⟩ := exists_linkDataFree hnab hp2 hq hBelow hinv hM𝒞 hM
  obtain ⟨z₀, hz₀⟩ := Theorem5.FuzzyFrameOn.exists_vertex hA₀
  have hz₀' := hz₀
  obtain ⟨-, J₀, hJ₀𝒞, hJ₀, -⟩ := hz₀'
  obtain ⟨h, hh⟩ := exists_conj_of_mem_canonClass hp2 hf hJ₀𝒞 hJ₀ hM𝒞 hM
  have hA₁ := Theorem5.FuzzyFrameOn.map hinv hA₀ h
  have haA₁ := Theorem5.mem_fuzzyVertices_map hinv hz₀ h
  rw [hh] at haA₁
  obtain ⟨J, t, N₁, u₁, hb⟩ := exists_frameBasis hA₁ haA₁
  have ha2 : zM * zM = 1 := hb.sq hb.aB
  obtain ⟨cJ, hcJ⟩ := ld.sec.exists_comp ld.D hb.linkJ
  obtain ⟨c₁, hc₁⟩ := ld.sec.exists_comp ld.D hb.linkN
  obtain ⟨c₀, hc₀⟩ := ld.sec.exists_comp ld.D (triangleResidual_mem_linkFamily hN𝒞 hN haN)
  by_cases h0J : c₀ = cJ
  · obtain ⟨B, hB, haB, huB⟩ := exists_frame_of_comp_free ld hp2 hq hinv hb hN𝒞 hN haN
      (j := cJ) hcJ (by rw [← h0J]; exact hc₀)
    exact ⟨B, hB, haB, huB⟩
  by_cases h0N : c₀ = c₁
  · obtain ⟨B, hB, haB, huB⟩ := exists_frame_of_comp_free ld hp2 hq hinv hb.swap hN𝒞 hN haN
      (j := c₁) hc₁ (by rw [← h0N]; exact hc₀)
    exact ⟨B, hB, haB, huB⟩
  by_cases hcl : SameClass zM t zN
  · have hcl' : ¬ SameClass zM u₁ zN := fun h => hb.not_sameClass (hcl.trans ha2 (h.symm ha2))
    obtain ⟨B, hB, haB, huB⟩ := exists_frame_of_cross_free ld hp2 hq hinv hcan hM𝒞 hM hb.memN
      hb.clsN (hb.tqN hb.aB) hb.u_ne_a hN𝒞 hN haN hua (j₁ := c₁) (j₂ := c₀) (Ne.symm h0N) hc₁
      hc₀ hcl'
    exact ⟨B, hB, haB, huB⟩
  · obtain ⟨B, hB, haB, huB⟩ := exists_frame_of_cross_free ld hp2 hq hinv hcan hM𝒞 hM hb.memJ
      hb.clsJ (hb.tqJ hb.aB) hb.ta hN𝒞 hN haN hua (j₁ := cJ) (j₂ := c₀) (Ne.symm h0J) hcJ hc₀
      hcl
    exact ⟨B, hB, haB, huB⟩

omit [Finite G] in
theorem omega_eq_conjClass {K : Subgroup G} (hΩ : HypOmegaMod p f Ω) (hK : K ∈ Ω)
    (htrans : ∀ J ∈ Ω, ∃ g : G, conjSub g K = J) : Ω = CoreAssembly.conjClass K := by
  ext J
  constructor
  · intro hJ
    exact htrans J hJ
  · rintro ⟨g, rfl⟩
    exact hΩ.conjInvariant g K hK

theorem exists_noncomm_of_mem [IsSimpleGroup G] (hΩ : HypOmegaMod p f Ω) {K : Subgroup G}
    (hK : K ∈ Ω) {z : G} (hz : IsUniqueInvolution K z) : ∃ a b : G, a * b ≠ b * a := by
  have hKs := CFSG.StronglyEmbedded.UniqueCoset.not_isSolvable_of_mem hΩ hK hz
  by_contra hcon
  push Not at hcon
  have : Group.IsSolvable G := IsSimpleGroup.comm_iff_isSolvable.mp hcon
  exact hKs inferInstance

theorem fuzzyFrameOn_of_triFrame {M : Fin 3 → Subgroup G} {x : Fin 3 → G} {R : Fin 3 → Subgroup G}
    (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : HypOmegaMod p f Ω)
    (hnt : ∀ K ∈ Ω, ∀ K' ∈ twinSet Ω K, K' = K) (hF : T8T.TriFrame Ω M x R)
    (hind : x 2 ∉ Subgroup.closure ({x 0, x 1} : Set G)) :
    FuzzyFrameOn p f Ω (Subgroup.closure ({x 0, x 1, x 2} : Set G)) := by
  have hrange : Set.range x = ({x 0, x 1, x 2} : Set G) := by
    ext y
    simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨i, rfl⟩
      fin_cases i <;> simp
    · rintro (rfl | rfl | rfl)
      exacts [⟨0, rfl⟩, ⟨1, rfl⟩, ⟨2, rfl⟩]
  have hc01 := hF.comm hp hΩ 0 1
  have hc02 := hF.comm hp hΩ 0 2
  have hc12 := hF.comm hp hΩ 1 2
  refine ⟨M, x, fun i => ⟨hF.mem i, isClassicalMember_of_twin hΩ (hF.mem i) (hF.inv i)⟩, ?_,
    T8T.isElemAbelian_closure_three (hF.sq 0) (hF.sq 1) (hF.sq 2) hc01 hc02 hc12,
    T8T.natCard_closure_three (hF.sq 0) (hF.sq 1) (hF.sq 2) hc01 hc02 hc12 (hF.ne_one 0)
      (hF.ne_one 1) (hF.x_ne hnt (i := 0) (j := 1) (by decide)) (hF.ne_one 2) hind,
    fun i => hF.le_trivialOnQuot hp hq hΩ hnt i⟩
  rw [hrange]

theorem alphaOf_eq_of_omegaNbr_frame [IsSimpleGroup G] {K : Subgroup G}
    (hst : AscStand p f Ω K) (hnt : ∀ K' ∈ twinSet Ω K, K' = K)
    (hframe : ∃ A₀, FuzzyFrameOn p f Ω A₀) {z : G} (hz : IsUniqueInvolution K z)
    {J₁ J₂ : Subgroup G} {t₁ t₂ : G} (h1 : IsUniqueInvolution J₁ t₁)
    (h2 : IsUniqueInvolution J₂ t₂) (hJ₁ : J₁ ∈ omegaNbr Ω K) (hJ₂ : J₂ ∈ omegaNbr Ω K) :
    alphaOf (Subgroup.closure ({t₂, z} : Set G)) =
      alphaOf (Subgroup.closure ({t₁, z} : Set G)) := by
  have hp : p ≠ 2 := hst.odd
  have hq : 5 ≤ p ^ f := hst.five
  have hΩ : HypOmegaMod p f Ω := hst.hyp
  have hBelow : CITBelowU p f (Nat.card G) := hst.below f hq
  have hK : K ∈ Ω := hst.mem
  have hnab := exists_noncomm_of_mem hΩ hK hz
  have hzc : IsClassicalMember p f K z := isClassicalMember_of_twin hΩ hK hz
  have hΩeq : Ω = CoreAssembly.conjClass K := omega_eq_conjClass hΩ hK hst.trans
  have hcanon : canonClass p f K = Ω := (canonClass_eq_conjClass hzc).trans hΩeq.symm
  have key : ∀ {J : Subgroup G} {t : G}, IsUniqueInvolution J t → J ∈ omegaNbr Ω K →
      ∃ B : Subgroup G, FuzzyFrameOn p f Ω B ∧ z ∈ fuzzyVertices p f Ω B ∧
        t ∈ fuzzyVertices p f Ω B := by
    intro J t ht hJ
    obtain ⟨A₀, hA₀⟩ := hframe
    have hne : z ≠ t := T8.ne_of_mem_omegaNbr hnt hJ hz ht
    have hK𝒞 : K ∈ canonClass p f K := hcanon ▸ hK
    have hJ𝒞 : J ∈ canonClass p f K := hcanon ▸ hJ.1
    have hA₀' : A₀ ∈ fuzzyFrames p f (canonClass p f K) := hcanon ▸ hA₀
    obtain ⟨B, hB, hzB, htB⟩ := exists_fuzzyFrame_of_trivialOnQuot hnab hp hq K hBelow hA₀' hK𝒞 hJ𝒞
      hzc (isClassicalMember_of_twin hΩ hJ.1 ht) (mem_trivialOnQuot_of_omegaNbr hp hq hΩ hz hJ)
      hne
    rw [hcanon] at hB hzB htB
    exact ⟨B, hB, hzB, htB⟩
  obtain ⟨B₁, hB₁, hz₁, ht₁⟩ := key h1 hJ₁
  obtain ⟨B₂, hB₂, hz₂, ht₂⟩ := key h2 hJ₂
  have four : ∀ {J : Subgroup G} {t : G} {B : Subgroup G}, IsUniqueInvolution J t →
      J ∈ omegaNbr Ω K → z ∈ B → t ∈ B →
        Subgroup.closure ({t, z} : Set G) ≤ B ∧
          Nat.card ↥(Subgroup.closure ({t, z} : Set G)) = 4 := by
    intro J t B ht hJ hzB htB
    have hzt : z * t = t * z := T8.mul_comm_of_mem_omegaNbr hp hΩ hz hJ ht
    have hne : t ≠ z := (T8.ne_of_mem_omegaNbr hnt hJ hz ht).symm
    refine ⟨?_, ?_⟩
    · rw [Subgroup.closure_le]
      intro y hy
      rcases hy with rfl | rfl
      · exact htB
      · exact hzB
    · have := (T7A.isElemAbelian2_closure_pair ht.sq hz.sq ht.ne_one hz.ne_one hne hzt.symm).1
      rw [this]
      norm_num
  obtain ⟨hF₁, hF₁4⟩ := four h1 hJ₁ hz₁.1 ht₁.1
  obtain ⟨hF₂, hF₂4⟩ := four h2 hJ₂ hz₂.1 ht₂.1
  rw [hΩeq] at hB₁ hB₂ hz₁ hz₂
  exact alphaOf_eq_of_fuzzyFrames hnab hp hq hzc hBelow z hB₂ hB₁ hz₂ hz₁ hF₂ hF₂4 hF₁ hF₁4

end Frames

end T8U

end CFSG.ClassicalInvolution.Asc77
