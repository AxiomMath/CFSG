module

public import CFSG.LieType.Ree.LargeReeInvolutionComponentFree
public import CFSG.LieType.Ree.LargeReeModelSchreier
public import CFSG.LocalAnalysis.ComponentInitial.EscapingNotAlternating

public noncomputable section

namespace CFSG.LieType.Ree.LargeReeInvolution

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley ReeTag
open CFSG.LocalAnalysis.ComponentInitial CFSG.ComponentClassification

theorem commuting_block_large_Ree_overgroup_exclusion
    {G : Type*} [Group G] [Finite G]
    {J : Subgroup G} (hq : CFSG.Assembly.IsQuasisimple J) (heven : Even (Nat.card J))
    (hJ : IsUniversalComponent J) (hΔ : (block J).Nontrivial) {L : Subgroup G}
    (hL : CFSG.Assembly.IsQuasisimple L) (hML : blockGroup J ≤ L)
    (hLH : ¬ L ≤ normalizer (blockGroup J : Set G)) (a : ℕ) (ha : 1 ≤ a) (k : Type) [Field k]
    [Finite k] [CharP k F4.prime] (hk : Nat.card k = 2 ^ (2 * a + 1)) :
    ¬ Nonempty (L ⧸ center L ≃* DerivedCentralQuotient (F4.reeGamma k a)) := by
  rintro ⟨e⟩
  obtain ⟨-, -, -, -, u, hu, Q, hQ⟩ :=
    escaping_block_quotient_inherits_local_components hq heven hJ hΔ hL hML hLH
  obtain ⟨f⟩ := nonempty_derivedCentralQuotient_mulEquiv_reeGamma (K := k) ha hk
  set ψ : L ⧸ center L →* ModGL F4.tag k :=
    (F4.reeGamma k a).subtype.comp (e.trans f).toMonoidHom with hψdef
  have hψ : Function.Injective ψ :=
    (F4.reeGamma k a).subtype_injective.comp (e.trans f).injective
  have hrange : ψ.range = F4.reeGamma k a := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact ((e.trans f) x).2
    · intro hy
      exact ⟨(e.trans f).symm ⟨y, hy⟩, by simp [hψdef]⟩
  have h := (isComponentOf_map_iff hψ).2 hQ
  rw [map_centralizer_singleton_of_injective hψ, hrange] at h
  have hu' : orderOf (ψ u) = 2 := by
    rw [orderOf_injective ψ hψ]
    exact hu
  exact (large_Ree_involution_centralizers_component_free a ha k hk).2 (ψ u)
    (hrange ▸ ⟨u, rfl⟩) hu' _ h

end CFSG.LieType.Ree.LargeReeInvolution
