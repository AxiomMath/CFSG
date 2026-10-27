module

public import CFSG.ClassicalInvolution.Balance.PassTwoStep
public import CFSG.ClassicalInvolution.Balance.OddCentralizerFreeLayer

public section

namespace CFSG.ClassicalInvolution.Balance

open CFSG.Open CFSG.ComponentClassification CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic

section Hypotheses

variable {G : Type} [Group G] [Finite G]

theorem componentClassificationOddCore_eq_bot_of_simple [IsSimpleGroup G]
    (hnab : ∃ a b : G, a * b ≠ b * a) :
    componentClassificationOddCore G = ⊥ := by
  rcases (inferInstance : (componentClassificationOddCore G).Normal).eq_bot_or_eq_top with h | h
  · exact h
  · exfalso
    have hodd : Odd (Nat.card G) := by
      have := OddCore.odd_card G
      rw [h] at this
      simpa using this
    have hsolv := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd
    obtain ⟨a, b, hab⟩ := hnab
    exact hab ((IsSimpleGroup.comm_iff_isSolvable (G := G)).mpr hsolv a b)

omit [Finite G] in
theorem not_subset_center_of_ne_one [IsSimpleGroup G] (hnab : ∃ a b : G, a * b ≠ b * a) {x : G}
    (hx : x ≠ 1) : ¬ ({x} : Set G) ⊆ Subgroup.center G := by
  intro hsub
  have hcenter : Subgroup.center G = ⊥ := by
    rcases (inferInstance : (Subgroup.center G).Normal).eq_bot_or_eq_top with h | h
    · exact h
    · exfalso
      obtain ⟨a, b, hab⟩ := hnab
      have : a ∈ Subgroup.center G := by rw [h]; trivial
      exact hab ((Subgroup.mem_center_iff.mp this b).symm)
  have := hsub (Set.mem_singleton x)
  rw [SetLike.mem_coe, hcenter, Subgroup.mem_bot] at this
  exact hx this

end Hypotheses

section Chain

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {E : Subgroup G}

theorem componentLayersAt_of_localLieSystems (hp2 : p ≠ 2) (h0 : ModelClauseZero)
    (hA1 : FundamentalWholeA1) (hΩ : InClass p f Ω) (hIH : LocalLieSystems p f Ω) {a : G}
    (ha : ¬ ({a} : Set G) ⊆ Subgroup.center G) (hlay : LayerGenerationAt E a) :
    ComponentLayersAt Ω E a := by
  intro L hL
  rcases omegaFreeAt_or_rankOneAt_or_isOddLieComponent hp2 h0 hA1 hΩ hIH ha hL with h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr fun F₀ hF₀E h4 hFn hfaith => hlay L hL h F₀ hF₀E h4 hFn hfaith)

theorem deltaCore_eq_bot_of_localLieSystems [IsSimpleGroup G] (hnab : ∃ a b : G, a * b ≠ b * a)
    (hp2 : p ≠ 2) (h0 : ModelClauseZero) (hA1 : FundamentalWholeA1) (hΩ : InClass p f Ω)
    (hIH : LocalLieSystems p f Ω) {F : Type*} [Field F] {S : Set (Subgroup G)}
    (Fr : WeakToralFrame F Ω E S) (h16 : 16 ≤ Nat.card E) (hGen : FusionGenerated E)
    (hlay : ∀ a ∈ E, a ≠ 1 → LayerGenerationAt E a) :
    ∀ Φ ∈ signalizerFunctorEk 2 2 E, deltaCore Φ = ⊥ :=
  deltaCore_eq_bot_of_weakFrame_of_layers Fr h16
    (fun a ha ha1 => componentLayersAt_of_localLieSystems hp2 h0 hA1 hΩ hIH
      (not_subset_center_of_ne_one hnab ha1) (hlay a ha ha1))
    (componentClassificationOddCore_eq_bot_of_simple hnab) hGen

theorem isQuasisimple_of_localLieSystems [IsSimpleGroup G] (hnab : ∃ a b : G, a * b ≠ b * a)
    (hp2 : p ≠ 2) (h0 : ModelClauseZero) (hA1 : FundamentalWholeA1) (hΩ : InClass p f Ω)
    (hIH : LocalLieSystems p f Ω) {F : Type*} [Field F] {S : Set (Subgroup G)}
    (Fr : WeakToralFrame F Ω E S) (h16 : 16 ≤ Nat.card E) (hGen : FusionGenerated E)
    (hlay : ∀ a ∈ E, a ≠ 1 → LayerGenerationAt E a) {L₀ : Subgroup G} (hL₀ : L₀ ∈ S) :
    CFSG.Open.IsQuasisimple L₀ := by
  obtain ⟨z₀, hz₀E, hz₀⟩ := Fr.toWeakPreFrame.exists_weakMember hL₀
  have hc := hz₀.isCentralInvolution
  have hΔ := deltaCore_eq_bot_of_localLieSystems hnab hp2 h0 hA1 hΩ hIH Fr h16 hGen hlay
  refine isQuasisimple_of_weakFrame_central Fr.toWeakPreFrame h16 hΔ hL₀ hz₀ ?_
  intro f₀ hf₀ hf₀1 M hM
  obtain ⟨hf₀E, hf₀c⟩ := mem_axisSub_iff.mp hf₀
  exact hB_of_localLieSystems hp2 h0 hA1 hΩ hIH (Fr.subset hL₀) hc
    (not_subset_center_of_ne_one hnab hf₀1)
    (fun l hl => Subgroup.mem_centralizer_singleton_iff.mpr (hf₀c l hl))
    (Fr.comm hz₀E hf₀E) M hM

theorem exactMembers_of_localLieSystems [IsSimpleGroup G] (hnab : ∃ a b : G, a * b ≠ b * a)
    (hp2 : p ≠ 2) (hf : 0 < f) (h9 : p ^ f ≠ 9) (h0 : ModelClauseZero)
    (hA1 : FundamentalWholeA1) (hΩ : InClass p f Ω)
    (hsingle : ∃ K ∈ Ω, ∀ L ∈ Ω, ∃ g : G, L = conjSub g K) (hIH : LocalLieSystems p f Ω)
    {F : Type*} [Field F] {S : Set (Subgroup G)} (Fr : WeakToralFrame F Ω E S)
    (h16 : 16 ≤ Nat.card E) (hGen : FusionGenerated E)
    (hlay : ∀ a ∈ E, a ≠ 1 → LayerGenerationAt E a) : ExactMembers Ω := by
  obtain ⟨L₀, hL₀, -⟩ := Fr.toWeakPreFrame.exists_ne
  exact exactMembers_of_weakFrame Fr.toWeakPreFrame hp2 hf h9 hΩ hsingle hL₀
    (isQuasisimple_of_localLieSystems hnab hp2 h0 hA1 hΩ hIH Fr h16 hGen hlay hL₀)

end Chain

end CFSG.ClassicalInvolution.Balance
