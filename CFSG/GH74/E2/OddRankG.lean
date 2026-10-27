module

public import CFSG.GH74.E2.OddRank
public import CFSG.GH74.E2.LocalComp
public import CFSG.GH74.E2.Shapes
import CFSG.GroupTheory.LocalCores.Layer
public import CFSG.GH74.SectionalRank

public section

namespace CFSG.GH74.E2

open Subgroup

theorem exists_isCompCen_of_layer_ne_bot {G : Type} [Group G] [Finite G] {t : G}
    (hl : CFSG.layer ↥(Cen t) ≠ ⊥) : ∃ K : Subgroup G, IsCompCen t K := by
  by_contra hcon
  push Not at hcon
  apply hl
  apply CFSG.LocalCores.layer_eq_bot_of_forall
  intro K' hK'
  apply hcon (K'.map (Cen t).subtype)
  refine ⟨?_, ?_⟩
  · rintro _ ⟨x, -, rfl⟩
    exact x.2
  · have h : (K'.map (Cen t).subtype).subgroupOf (Cen t) = K' :=
      Subgroup.comap_map_eq_self_of_injective (Cen t).subtype_injective K'
    rw [h]
    exact hK'

theorem noOddRankFive_of (hComp : ComponentList) (hD : K0Data) : NoOddRankFive := by
  intro G _ _ hH t ht p hp h5 B hBC hB
  have hgenC : Gen4 ↥(Cen t) := Gen4.subgroup (Cen t) hH.gen4
  have hB'ab : ElemAb p (B.subgroupOf (Cen t)) :=
    ⟨fun a ha b hb => Subtype.ext (hB.1 a ha b hb), fun a ha => Subtype.ext (hB.2 a ha)⟩
  have hcardB : Nat.card (B.subgroupOf (Cen t)) = Nat.card B :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBC).toEquiv
  rw [← hcardB]
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcore := hH.pPrimeCore_cen_bot ht
  by_cases hl : CFSG.layer ↥(Cen t) = ⊥
  · have hchar :=
      CFSG.isCharacteristicP_of_pPrimeCore_eq_bot_of_layer_eq_bot (↥(Cen t)) 2 hcore hl
    exact card_le_of_noComponent hgenC CFSG.pCore_isPGroup CFSG.pCore_normal
      (fun c hc => hchar (mem_centralizer_iff.2 (fun q hq => (hc q hq).symm))) hp h5 hB'ab
  · obtain ⟨K, hK⟩ := exists_isCompCen_of_layer_ne_bot hl
    obtain ⟨hshape, huniq⟩ := hComp G hH t ht K hK
    have hL := localK_of_component hH ht (fun K₁ K₂ h₁ h₂ => (huniq K₁ h₁).trans (huniq K₂ h₂).symm)
      hK
    have hKle : K ≤ Cen t := hK.1
    have hshape' : K0Shape ↥(K.subgroupOf (Cen t)) :=
      K0Shape.of_mulEquiv (Subgroup.subgroupOfEquivOfLe hKle).symm hshape
    exact card_le_of_localK hgenC hL (hD.center_card _ hshape')
      (fun hc => hD.sylow_rank_simple _ hshape' hc)
      (fun hc => hD.sylow_rank_cover _ hshape' hc) hp h5
      (hD.autRank_ge5 _ hshape' p hp h5) hB'ab

end CFSG.GH74.E2
