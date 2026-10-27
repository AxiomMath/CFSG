module

public import CFSG.LocalAnalysis.ComponentInitial.EscapingBlockCharTwo
public import CFSG.Sporadic.ThSchreier.NodeInnerInvolution

public section

namespace CFSG.LocalAnalysis.ComponentInitial

open Subgroup

theorem commuting_block_thompson_overgroup_exclusion {G : Type} [Group G] [Finite G]
    {J : Subgroup G} (hq : CFSG.Assembly.IsQuasisimple J) (heven : Even (Nat.card J))
    (hJ : IsUniversalComponent J) (hΔ : (block J).Nontrivial) {L : Subgroup G}
    (hL : CFSG.Assembly.IsQuasisimple L) (hML : blockGroup J ≤ L)
    (hLH : ¬ L ≤ normalizer (blockGroup J : Set G)) :
    ¬ Nonempty (L ⧸ center L ≃* CFSG.Blueprint.NativeSporadic.Th) := by
  intro he
  obtain ⟨t, ht, hchar⟩ :=
    escaping_block_quotient_non_characteristic_two_centralizer hq heven hJ hΔ hL hML hLH
  have h := ((Sporadic.ThSchreier.ctuc_Th_inner_involution_centralizers_characteristic_two.2.2
    (L ⧸ center L) he).1 t ht).1
  apply hchar
  unfold CFSG.Assembly.Dichotomy.dichotomyCharP at h
  assumption

end CFSG.LocalAnalysis.ComponentInitial
