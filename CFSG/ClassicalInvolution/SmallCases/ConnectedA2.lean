module

public import CFSG.ClassicalInvolution.SmallCases.ConnectedA2Inputs
public import CFSG.ClassicalInvolution.SmallCases.ConnectedA2Frame

public section

namespace CFSG.ClassicalInvolution.ConnectedA2

open scoped IsMulCommutative MatrixGroups
open CFSG.Open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Generic.DeltaClosure
  CFSG.ClassicalInvolution.Generic.CoreAssembly CFSG.ClassicalInvolution.Balance

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] [IsSimpleGroup G]

omit [Finite G] [IsSimpleGroup G] in
theorem frame_involutions {K : Subgroup G} {z : G} (hz : IsClassicalMember p f K z) {F : Type}
    [Field F] {A : Subgroup G} {S : Set (Subgroup G)} (Fr : RankFrame F (conjClass K) A S) :
    ∀ K' ∈ S, ∃ z' ∈ A, IsClassicalMember p f K' z' := by
  intro K' hK'
  obtain ⟨w, hw⟩ := Fr.exists_isUniqueInvolution hK'
  exact ⟨w, Fr.mem_of_isUniqueInvolution hK' hw,
    isClassicalMember_of_isUniqueInvolution hz (Fr.subset hK') hw⟩

theorem localHypotheses_of_frame {K : Subgroup G} {z : G} (hb : Branch p f K z) {F : Type}
    [Field F] {A : Subgroup G} {S : Set (Subgroup G)}
    (hfacts : RankThreeFrameFacts p f F (conjClass K) A S) : LocalHypotheses p f (conjClass K) A :=
  ⟨inClass_conjugates hb.member, hb.odd, hb.five,
    fun a _ ha1 hmem => ha1 (by
      rw [center_eq_bot hb.nonabelian, Subgroup.mem_bot] at hmem
      exact hmem),
    localLieSystems_of_citBelowU (inClass_conjugates hb.member) hb.below, hfacts.single⟩

theorem frameLayerSpan_eq_top_of_branch {K : Subgroup G} {z : G} (hb : Branch p f K z) {F : Type}
    [Field F] {A : Subgroup G} {S : Set (Subgroup G)} (Fr : RankFrame F (conjClass K) A S)
    (hfacts : RankThreeFrameFacts p f F (conjClass K) A S) (hne : S.Nonempty)
    (hcover : ∀ a ∈ A, IsFrameInvolution p f S a → FrameCoversModO (conjClass K) S a) :
    frameLayerSpan p f (conjClass K) A S = ⊤ :=
  frameLayerSpan_eq_top_of_lie (localHypotheses_of_frame hb hfacts) Fr.subset hne
    (frame_involutions hb.member Fr) hcover (omegaConnected_range_conjSub hb.connected)

theorem oddLieType_of_frame {K : Subgroup G} {z : G} (hb : Branch p f K z)
    (hD : HasDatum p f K) (hP1 : A2P1 p f)
    (hFrame : A2FrameFacts p f) (hOrth : A2OrthEndpoint p f) {F : Type} [Field F]
    (hF : Nat.card F = p ^ f)
    {A : Subgroup G} {S : Set (Subgroup G)} (Fr : RankFrame F (conjClass K) A S)
    {K₁ K₂ : Subgroup G} (h₁ : K₁ ∈ S) (h₂ : K₂ ∈ S) (hne : K₁ ≠ K₂) (hnc : ¬ Commutes K₁ K₂) :
    CFSG.Blueprint.OddLieType G ∨ CFSG.Blueprint.NativeSporadic.IsSporadic G .M11 := by
  have hp2 := hb.odd
  have hq := hb.five
  have hz := hb.member
  have hf : 0 < f := pos_of_five_le hq
  have hZ : Subgroup.center G = ⊥ := center_eq_bot hb.nonabelian
  have hcard8 : Nat.card A = 8 :=
    le_antisymm (card_le_eight_of_not_bootData hz Fr rfl ⟨K₁, h₁⟩ hb.noBoot) Fr.card
  have hnc' : ∃ K' ∈ S, ∃ L' ∈ S, K' ≠ L' ∧ ¬ Commutes K' L' := ⟨K₁, h₁, K₂, h₂, hne, hnc⟩
  have hP1A : FrameP1 (conjClass K) A := hP1 G K z hb hD F hF A S Fr hcard8 hnc'
  have hfacts := hFrame G K z hb hD F hF A S Fr hcard8 hnc' hP1A
  by_cases hgen : ∀ a ∈ A, IsFrameInvolution p f S a → FrameGenerationModO (conjClass K) S a
  · refine Or.inl ?_
    have : IsMulCommutative ↥A := Fr.isMulCommutative
    have hS : S ⊆ conjClass K := Fr.subset
    have hne' : S.Nonempty := ⟨K₁, h₁⟩
    have hnt : ∀ K' ∈ S, K' ≠ ⊥ := by
      intro K' hK' hbot
      obtain ⟨w, hw⟩ := Fr.exists_isUniqueInvolution hK'
      have hmem := hw.mem
      rw [hbot, Subgroup.mem_bot] at hmem
      exact hw.ne_one hmem
    have hP1all : ∀ a ∈ A, IsFrameInvolution p f S a → LocalOddCentral (conjClass K) {a} := by
      rintro a haA ⟨K', hK', ha⟩
      exact hP1A a haA ha.ne_one
    have hspan : frameSpan S = ⊤ :=
      frameSpan_eq_top_of_lie (localHypotheses_of_frame hb hfacts) hS hne'
        (frame_involutions hz Fr) hgen hP1all (omegaConnected_range_conjSub hb.connected)
    have hconn : NonCommConnected S := nonCommConnected_of_frameSpan_eq_top hZ hne' hnt hspan
    rcases hfacts.pairs with hlin | ⟨K₀, _, _, _, hK₀, hlinU⟩
    · have hA2 : A2Dichotomy A S := a2Dichotomy_of_rankFrame_linear Fr hlin
      obtain ⟨hd6, -⟩ := dataFinset_card_six Fr hcard8 hne' hA2 hfacts.fibre hconn hZ hspan
        h₁ h₂ hne hnc
      exact oddLieType_of_frame_linear hp2 hf (by omega) hZ Fr hF hcard8 hne' hfacts.fibre hconn
        hd6 hlin (datumInjective_of_axis Fr hfacts.injective) hspan
    · have hA2 : A2Dichotomy A S := a2Dichotomy_of_rankFrame_unitary Fr hK₀ hlinU
      obtain ⟨hd6, -⟩ := dataFinset_card_six Fr hcard8 hne' hA2 hfacts.fibre hconn hZ hspan
        h₁ h₂ hne hnc
      exact oddLieType_of_frame_unitary hK₀ hp2 hq hb.nonabelian Fr hcard8 hne' hfacts.fibre hconn
        hd6 hlinU (datumInjective_of_axis Fr hfacts.injective) hspan
  · exact hOrth G K z hb hD F hF A S Fr hcard8 hnc' hP1A hfacts hgen

theorem smallConnectedA2_of_inputs (h : ConnectedA2Inputs p f) : SmallConnectedA2 p f := by
  rw [smallConnectedA2_iff]
  intro G _ _ _ K z hb
  have hf : 0 < f := pos_of_five_le hb.five
  have hD := h.datum G K z hb
  obtain ⟨L₁, L₂, t, h₁, h₂, hLD⟩ := id hD
  have hΩ : InClass p f (conjClass K) := inClass_conjugates hb.member
  rcases hLD with hLD | hLD
  · have hF : Nat.card (GaloisField p f) = p ^ f := GaloisField.card p f hf.ne'
    obtain ⟨A, Fr, hs₁, hs₂, hne, hnc, -⟩ := hLD.exists_rankFrame
      (CFSG.ClassicalInvolution.Generic.DeltaClosure.odd_card_galoisField hb.odd hb.five)
      (by rw [hF]; exact hb.five) hΩ.conjInvariant h₁ h₂
    exact oddLieType_of_frame hb hD h.p1 h.frame h.orth hF Fr hs₁ hs₂ hne hnc
  · have hK : Nat.card (GaloisField p (2 * f)) = (p ^ f) ^ 2 := by
      rw [GaloisField.card p (2 * f) (by omega), pow_mul']
    obtain ⟨A, Fr, hs₁, hs₂, hne, hnc, -⟩ :=
      hLD.exists_rankFrame hK hb.odd hb.five hΩ.conjInvariant h₁ h₂
    have hF := CFSG.LieType.Steinberg.card_fixedSubfield hK
    exact oddLieType_of_frame hb hD h.p1 h.frame h.orth hF Fr hs₁ hs₂ hne hnc

end CFSG.ClassicalInvolution.ConnectedA2
