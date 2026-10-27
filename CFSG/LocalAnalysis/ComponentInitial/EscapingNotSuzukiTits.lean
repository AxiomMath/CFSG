module

public import CFSG.LocalAnalysis.ComponentInitial.BlockCentralQuotient
public import CFSG.Sporadic.Schreier.TitsComponent

public section

namespace CFSG.LocalAnalysis.ComponentInitial

open Subgroup CFSG.Blueprint

theorem exists_isComponent_centralizer_of_mulEquiv {T X : Type*} [Group T] [Group X]
    (e : T ≃* X) {u : T} (hu : orderOf u = 2) {Q : Subgroup T}
    (hQ : CFSG.Assembly.IsComponentOf Q (centralizer ({u} : Set T))) :
    ∃ x : X, orderOf x = 2 ∧
      ∃ B : Subgroup (centralizer ({x} : Set X)), CFSG.IsComponent B := by
  have h := isComponentOf_map_of_injective hQ e.toMonoidHom e.injective
  rw [map_centralizer_singleton_mulEquiv] at h
  exact ⟨e u, by rw [MulEquiv.orderOf_eq, hu], _,
    (isComponentOf_iff_isComponent_subgroupOf h.1).1 h⟩

theorem commuting_block_suzuki_tits_overgroup_exclusion {G : Type*} [Group G] [Finite G]
    {J : Subgroup G} (hq : CFSG.Assembly.IsQuasisimple J) (heven : Even (Nat.card J))
    (hJ : IsUniversalComponent J) (hΔ : (block J).Nontrivial) {L : Subgroup G}
    (hL : CFSG.Assembly.IsQuasisimple L) (hML : blockGroup J ≤ L)
    (hLH : ¬ L ≤ normalizer (blockGroup J : Set G)) :
    ¬ ((∃ (a : ℕ) (k : Type) (_ : Field k) (_ : Finite k), Nat.card k = 2 ^ (2 * a + 1) ∧
        Nonempty (L ⧸ center L ≃* suzukiGroup a k)) ∨
      Nonempty (L ⧸ center L ≃* Sporadic.Schreier.Tits.titsD)) := by
  obtain ⟨-, -, -, -, u, hu, Q, hQ⟩ :=
    escaping_block_quotient_inherits_local_components hq heven hJ hΔ hL hML hLH
  rintro (⟨a, k, _, _, hk, ⟨e⟩⟩ | ⟨⟨e⟩⟩)
  · obtain ⟨x, hx, B, hB⟩ := exists_isComponent_centralizer_of_mulEquiv e hu hQ
    exact (Sporadic.Schreier.Tits.CTI_Suzuki_Tits_involution_centralizers_component_free.1
      a k hk x hx B) hB
  · obtain ⟨x, hx, B, hB⟩ := exists_isComponent_centralizer_of_mulEquiv e hu hQ
    exact (Sporadic.Schreier.Tits.CTI_Suzuki_Tits_involution_centralizers_component_free.2
      x hx B) hB

end CFSG.LocalAnalysis.ComponentInitial
