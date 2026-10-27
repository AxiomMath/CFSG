module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.CaseOne
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.SquareCase
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.JOneRoute
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.NonSquare
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.RankBound
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.TheoremC.TheoremC

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37

open CFSG.Open CFSG.ProperTwoGeneratedCore.Assembly CFSG.ProperTwoGeneratedCore.TheoremC
open CFSG.ShultStronglyClosedTI

@[expose] def CanonicalStatement (G : Type) [Group G] [Finite G] : Prop :=
  IsSimpleGroup G → (∃ a b : G, a * b ≠ b * a) → ∀ S : Sylow 2 G,
    3 ≤ CFSG.Open.pRank 2 (S : Subgroup G) → properTwoGenCoreGamma (S : Subgroup G) 2 ≠ ⊤ →
      properTwoGenCoreGamma (S : Subgroup G) 1 ≠ ⊤ ∨ Nonempty (G ≃* properTwoGenCoreJ1)

@[expose] def CanonicalBelow (n : ℕ) : Prop :=
  ∀ (K : Type) [Group K] [Finite K], Nat.card K < n → CanonicalStatement K

theorem canonicalStatement_of_below
    (h : ∀ (G : Type) [Group G] [Finite G], CanonicalBelow (Nat.card G) → CanonicalStatement G)
    (G : Type) [Group G] [Finite G] : CanonicalStatement G := by
  suffices hn : ∀ n : ℕ, ∀ (G : Type) [Group G] [Finite G], Nat.card G = n →
      CanonicalStatement G from hn _ G rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro G _ _ hn
    exact h G fun K _ _ hK => ih _ (hn ▸ hK) K rfl

@[expose] def SquareCaseQuasisimpleImpossibleBelow : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (S : Sylow 2 G) (H : Subgroup G) (z : G),
    CanonicalBelow (Nat.card G) → SquareCaseSetting G S H z →
    ∀ J : Subgroup (EscapingQuotient z), CFSG.IsComponent J → ¬ J ≤ escapingImage H z →
      (∃ x ∈ J, orderOf x = 2 ∧ x ≠ escapingBar z) →
      ((∀ k ∈ escapingSylowImage S z, k ∈ Subgroup.centralizer (J : Set (EscapingQuotient z)) →
        k = 1 ∨ k = escapingBar z) ∨
       (∃ c ∈ Subgroup.center J, (c : EscapingQuotient z) ≠ 1 ∧
        (c : EscapingQuotient z) ≠ escapingBar z)) → False

variable {G : Type} [Group G] [Finite G]

theorem exists_component_not_mem_of_second_central_involution
    {S : Sylow 2 G} {H : Subgroup G}
    {z : G} (hset : CoreSetting G S H) (hz : IsCentralInvolution (S : Subgroup G) z)
    (hesc : ¬ Subgroup.centralizer ({z} : Set G) ≤ H) {z' : G}
    (hz' : IsCentralInvolution (S : Subgroup G) z') (hne : z' ≠ z) :
    ∃ J : Subgroup (EscapingQuotient z), CFSG.IsComponent J ∧ escapingBar z ∉ J := by
  have hq : EscapingQuotientData H z := escapingQuotientData hset (hset.sylow_le hz.1) hz.2.1 hesc
  have hsyl : ∀ P : Subgroup G, P ≤ Subgroup.centralizer ({z} : Set G) → IsPGroup 2 P →
      Nat.card P ≤ Nat.card ((S : Subgroup G) ⊓ Subgroup.centralizer ({z} : Set G) :
        Subgroup G) := by
    intro P _ hP
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hSle : (S : Subgroup G) ≤ Subgroup.centralizer ({z} : Set G) := fun s hs =>
      Subgroup.mem_centralizer_singleton_iff.mpr (hz.2.2 s hs)
    rw [inf_eq_left.mpr hSle]
    obtain ⟨Q, hPQ⟩ := hP.exists_le_sylow
    refine (Subgroup.card_le_of_le hPQ).trans (le_of_eq ?_)
    rw [Sylow.card_eq_multiplicity Q, Sylow.card_eq_multiplicity S]
  obtain ⟨T, hT⟩ := exists_sylow_eq_escapingSylowImage hsyl
  have hz'M : z' ∈ Subgroup.centralizer ({z} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr (hz.2.2 z' hz'.1)
  have hTH : (T : Subgroup (EscapingQuotient z)) ≤ escapingImage H z :=
    hT ▸ escapingSylowImage_le_image hset.sylow_le
  have hcore : properTwoGenCoreGamma (T : Subgroup (EscapingQuotient z)) 2 ≤
      escapingImage H z :=
    iSup_le fun Q => iSup_le fun hQT => iSup_le fun hQ => hq.normalizer_le Q (hQT.trans hTH) hQ
  have hw2 : orderOf (escapingMk z ⟨z', hz'M⟩) = 2 :=
    escaping_orderOf_mk z (by rw [← Subgroup.orderOf_coe]; exact hz'.2.1)
  have hwT : escapingMk z ⟨z', hz'M⟩ ∈ escapingSylowImage S z := ⟨⟨z', hz'M⟩, hz'.1, rfl⟩
  have hwC := mk_mem_centralizer_escapingSylowImage (S := S) (u := z) (w := ⟨z', hz'M⟩)
    fun s hs => hz'.2.2 s hs
  have hwne : escapingMk z ⟨z', hz'M⟩ ≠ escapingBar z := by
    intro h
    exact hne (escaping_eq_of_mk_eq_bar (mul_self_eq_one_of_orderOf_eq_two hz.2.1)
      (mul_self_eq_one_of_orderOf_eq_two (by rw [Subgroup.orderOf_mk]; exact hz'.2.1)) h)
  have hc : CoreConfig (escapingImage H z) (escapingBar z) (escapingMk z ⟨z', hz'M⟩) := by
    refine coreConfig_escaping hq hTH hcore (hT ▸ hwT) (fun p hp => ?_) hw2 hwne
    have hp' : p ∈ escapingSylowImage S z := hT ▸ hp
    exact Subgroup.mem_centralizer_iff.mp hwC p hp'
  exact theoremC _ _ _ _ hc

theorem centralCentralizer_at
    (h1 : SquareCaseRankOneImpossible)
    (hK : SquareCaseHighRankCentralizerImpossible) (hQ : SquareCaseQuasisimpleImpossibleBelow)
    (hJ1 : JankoConfigurationJOne) (IH : CanonicalBelow (Nat.card G)) {S : Sylow 2 G}
    {H : Subgroup G} {z : G} (hset : CoreSetting G S H)
    (hz : IsCentralInvolution (S : Subgroup G) z) :
    Subgroup.centralizer ({z} : Set G) ≤ H ∨ Nonempty (G ≃* properTwoGenCoreJ1) := by
  by_cases hesc : Subgroup.centralizer ({z} : Set G) ≤ H
  · exact Or.inl hesc
  refine Or.inr (hJ1 G S H z hset hz hesc (caseIJankoConfiguration G S H z hset hz hesc ?_))
  by_contra hII
  push Not at hII
  by_cases hcyc : ∀ z' : G, IsCentralInvolution (S : Subgroup G) z' → z' = z
  swap
  · push Not at hcyc
    obtain ⟨z', hz', hne⟩ := hcyc
    obtain ⟨J, hJ, hzJ⟩ := exists_component_not_mem_of_second_central_involution hset hz hesc hz' hne
    exact hzJ (hII J hJ)
  by_cases hsq : ∃ v ∈ (S : Subgroup G), v ^ 2 = z
  swap
  · push Not at hsq
    obtain ⟨J, hJ, hzJ⟩ := coreSetting_exists_component_not_mem_of_not_sq hset hz hesc hsq
    exact hzJ (hII J hJ)
  have hS : SquareCaseSetting G S H z := ⟨hset, hz, hesc, hcyc, hsq, hII⟩
  obtain ⟨J, hJ, hJH⟩ :=
    coreSetting_exists_component_not_le_image generalizedFittingUniqueInvolutionRankBound hset hz
      hesc
  by_cases hrank : ∃ x ∈ J, orderOf x = 2 ∧ x ≠ escapingBar z
  swap
  · push Not at hrank
    exact h1 G S H z hS J hJ hJH hrank
  by_cases hZ : ∃ c ∈ Subgroup.center J, (c : EscapingQuotient z) ≠ 1 ∧
      (c : EscapingQuotient z) ≠ escapingBar z
  · exact hQ G S H z IH hS J hJ hJH hrank (Or.inr hZ)
  push Not at hZ
  have hZ' : ∀ c ∈ Subgroup.center J, (c : EscapingQuotient z) = 1 ∨
      (c : EscapingQuotient z) = escapingBar z := fun c hc => by
    by_cases h1 : (c : EscapingQuotient z) = 1
    · exact Or.inl h1
    · exact Or.inr (hZ c hc h1)
  by_cases hk : ∃ k ∈ escapingSylowImage S z,
      k ∈ Subgroup.centralizer (J : Set (EscapingQuotient z)) ∧ k ≠ 1 ∧ k ≠ escapingBar z
  · exact hK G S H z hS J hJ hJH hrank hZ' hk
  push Not at hk
  refine hQ G S H z IH hS J hJ hJH hrank (Or.inl fun k hkS hkC => ?_)
  by_contra hne
  push Not at hne
  exact hne.2 (hk k hkS hkC hne.1)

theorem canonicalStatement_of_parts
    (h1 : SquareCaseRankOneImpossible)
    (hK : SquareCaseHighRankCentralizerImpossible) (hQ : SquareCaseQuasisimpleImpossibleBelow)
    (hJ1 : JankoConfigurationJOne) (IH : CanonicalBelow (Nat.card G)) :
    CanonicalStatement G := by
  intro _ hnonab S hrank hcore
  set H := properTwoGenCoreGamma (S : Subgroup G) 2 with hHdef
  have hset : CoreSetting G S H :=
    ⟨inferInstance, hnonab, hrank, hcore, sylow_le_gamma S (by omega), le_rfl⟩
  obtain ⟨z, hz⟩ := exists_centralInvolution S (by omega)
  rcases centralCentralizer_at h1 hK hQ hJ1 IH hset hz with hzC | hJ
  · left
    have hloc := localEmbedding_of_steps (escapingCentralizerStep_of_highRank highRankEscapingStep)
      S H z hset hz hzC
    have hstrong := theoremTwo G H z hloc (centralSylow_of_isCentralInvolution S hz)
    have hz1 : z ≠ 1 := by
      intro h
      have := hz.2.1
      rw [h, orderOf_one] at this
      norm_num at this
    rw [involutionPointHull_eq_top hz1] at hstrong
    have hH := fusionStronglyEmbedded_of_subgroupOf_top hstrong
    intro hΓ
    apply hset.proper
    exact top_unique (hΓ ▸ gamma_one_le_of_stronglyEmbedded S hset.sylow_le hH)
  · exact Or.inr hJ

theorem aschbacher_proper_two_generated_core_of_below
    (h1 : SquareCaseRankOneImpossible)
    (hK : SquareCaseHighRankCentralizerImpossible) (hQ : SquareCaseQuasisimpleImpossibleBelow)
    (hJ1 : JankoConfigurationJOne)
    (G : Type) [Group G] [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (S : Sylow 2 G) (hrank : 3 ≤ CFSG.Open.pRank 2 (S : Subgroup G))
    (hcore : properTwoGenCoreGamma (S : Subgroup G) 2 ≠ ⊤) :
    properTwoGenCoreGamma (S : Subgroup G) 1 ≠ ⊤ ∨ Nonempty (G ≃* properTwoGenCoreJ1) :=
  canonicalStatement_of_below (fun _ _ _ IH => canonicalStatement_of_parts h1 hK hQ hJ1 IH) G
    inferInstance hnonab S hrank hcore

end CFSG.ProperTwoGeneratedCore.Lemma37
