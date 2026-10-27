module

public import CFSG.LocalAnalysis.ComponentClassification.Sol76T13BalancedProps
public import CFSG.LocalAnalysis.ComponentClassification.Sol76T13L32Close

public section

namespace CFSG.ComponentClassification.Sol76T13

open CFSG Subgroup CFSG.ComponentClassification.FooteLit CFSG.ComponentClassification.Sol76

@[expose] def Lemma32FullFor (𝒜 : Thm13Ambient) : Prop :=
  ∀ (G : Type) [Group G] [Finite G], 𝒜 G → ∀ N : Subgroup G, IsSolomonChoice N →
    ∀ K ∈ kStarComponents N, ∀ K' ∈ kStarComponents N, K ≠ K' →
    ∀ b ∈ K, orderOf b = 2 →
      conjClosure (twoLayerIn (K' ⊓ centralizer ({b} : Set G)))
          (twoLayerIn (centralizer ({b} : Set G))) ≤
        oddCoreIn (twoLayerIn (centralizer ({b} : Set G))) ⊔
          twoLayerIn (K' ⊓ centralizer ({b} : Set G))

theorem lemma32InputFor_of_full {𝒜 : Thm13Ambient} (h : Lemma32FullFor 𝒜) :
    Lemma32InputFor 𝒜 :=
  fun G _ _ hG N hN K hK K' hK' hne b hbK hb2 _ => h G hG N hN K hK K' hK' hne b hbK hb2

theorem lemma32FullFor_of_twoPart {𝒜 : Thm13Ambient} (hq : QuasisimpleTwoPartInput)
    (h𝒜 : ∀ (G : Type) [Group G] [Finite G], 𝒜 G → KStarKProper G)
    (hR1 : Lemma32ConditionTwoInputFor 𝒜)
    (hv : ∀ (G : Type) [Group G] [Finite G], 𝒜 G → ∀ N' : Subgroup G, IsKBalanced N' →
      ¬ solomonKStarOf N' ≤ solomonKStarOf (⊤ : Subgroup G)) :
    Lemma32FullFor 𝒜 := by
  intro G _ _ hG N hN K hK K' hK' hne b hbK hb2
  have hbQ := mem_coreActionKernel_of_ne hK hK' hne hbK
  obtain ⟨M, hM⟩ := pumpSet_nonempty hK' hbQ hb2
  have h1 : (pumpSet K' (centralizer ({b} : Set G))).ncard = 1 := by
    have hle : (pumpSet K' (centralizer ({b} : Set G))).ncard ≤ 1 := by
      by_contra h
      exact false_of_two_le_ncard_pumpSet hq (h𝒜 G hG) hR1 hG (hv G hG) hN hK hK' hne hbK hb2
        (by omega)
    have hpos := (Set.ncard_pos (Set.toFinite _)).mpr ⟨M, hM⟩
    omega
  obtain ⟨M', hM'⟩ := Set.ncard_eq_one.mp h1
  exact conjClosure_le_of_pumpSet_eq hK' hbQ hb2 hM'

theorem lemma32FullFor_simple_of_twoPart (hq : QuasisimpleTwoPartInput)
    (hR1 : Lemma32ConditionTwoInputFor simpleAmbient) : Lemma32FullFor simpleAmbient :=
  lemma32FullFor_of_twoPart hq (fun _ _ _ hG => kStarKProper_of_simpleAmbient hG) hR1
    fun _ _ _ hG _ hN' => not_le_solomonKStarOf_top_of_simple hG hN'

end CFSG.ComponentClassification.Sol76T13
