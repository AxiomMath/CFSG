module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Junction.Fs79.ThmU.Block
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Junction.Fs79.ThmU.Step4

public section

namespace CFSG.EvenSporadicStandard.Induction

open Subgroup CFSG.EvenSporadicStandard.Solomon78 CFSG.ComponentClassification.AschbacherToolkit
  CFSG.LocalAnalysis.ComponentInitial
open scoped commutatorElement

theorem assembly_isQuasisimple_of_inLF {H : Type} [Group H] {K : Subgroup H} (hK : InLF K) :
    CFSG.Assembly.IsQuasisimple K := by
  obtain ⟨t, ht2, hcomp⟩ := hK
  exact (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native ↥K).2
    hcomp.isQuasisimple

theorem even_card_centralizer_of_inLF {H : Type} [Group H] [Finite H] {K : Subgroup H}
    (hK : InLF K) : Even (Nat.card (centralizer (K : Set H))) := by
  obtain ⟨t, ht2, hcomp⟩ := hK
  have ht : t ∈ centralizer (K : Set H) := by
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    exact Subgroup.mem_centralizer_singleton_iff.1 (hcomp.1 hk)
  have h2 : 2 ∣ Nat.card (centralizer (K : Set H)) := by
    have h3 := orderOf_dvd_natCard (⟨t, ht⟩ : centralizer (K : Set H))
    have e : orderOf (⟨t, ht⟩ : centralizer (K : Set H)) = 2 := by
      rw [Subgroup.orderOf_mk, ht2]
    rwa [e] at h3
  exact even_iff_two_dvd.2 h2

theorem isUniversalComponent_of_universalF {H : Type} [Group H] [Finite H] {K : Subgroup H}
    (hu : ThmU.UniversalF K) : IsUniversalComponent K := by
  intro t ht ht2
  have hKt : K ≤ centralizer ({t} : Set H) := by
    intro k hk
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (Subgroup.mem_centralizer_iff.1 ht) k hk
  exact (CFSG.LocalAnalysis.ComponentInitial.isComponentOf_iff_isComponent_subgroupOf hKt).2
    (ThmU.universalF_iff.1 hu t ht2 hKt).2

theorem starHyp_of_fStarSimple
    {H : Type} [Group H] [Finite H] {N : Subgroup H} (hN : FStarSimple N)
    (hperf : ∀ P : Subgroup H, ⁅P, P⁆ = P → P ≤ N) : ThmU.StarHyp H := by
  intro J hJ hJu hJrank g hcomm
  obtain ⟨t, ht2, hcomp⟩ := hJ.1
  have hq : CFSG.Assembly.IsQuasisimple J := assembly_isQuasisimple_of_inLF hJ.1
  have hrank : 2 ≤ CFSG.Assembly.pRank 2 J := hJrank
  have hCeven := even_card_centralizer_of_inLF hJ.1
  have hU := isUniversalComponent_of_universalF hJu
  have heven : Even (Nat.card J) :=
    CFSG.LocalAnalysis.ComponentInitial.even_card_of_two_le_pRank hrank
  have hJN : J ≤ N := hperf J (ThmU.IsCompIn.perfect hcomp)
  have hH := ThmU.normalizer_blockGroup_ne_top_of_fStarSimple hN hq hU heven hJN hCeven
  have hg : ⁅J, conjSub g J⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro j hj
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    exact (hcomm j hj b hb).symm
  exact ThmU.universal_rank_two_component_eq_of_commutator_eq_bot_of_ne_top
    hq hrank hU hH g hg

end CFSG.EvenSporadicStandard.Induction
