module

public import CFSG.LocalAnalysis.ComponentInitial.CommutingBlock
public import CFSG.LocalAnalysis.ComponentInitial.StandardBasics

public section

namespace CFSG.LocalAnalysis.ComponentInitial

open Subgroup CFSG.Assembly CFSG.Assembly.ComponentType

variable {G : Type*} [Group G]

theorem normalizer_le_normalizer_centralizer (L : Subgroup G) :
    normalizer (L : Set G) ≤ normalizer (centralizer (L : Set G) : Set G) := fun g hg => by
  have hL := conjSub_eq_of_mem_normalizer hg
  refine mem_normalizer_of_conjSub_le ?_ ?_
  · rw [conjSub_centralizer, hL]
  · have hL' := conjSub_eq_of_mem_normalizer (inv_mem hg)
    rw [conjSub_centralizer, hL']

theorem involution_component_standard_criterion [Finite G] {L : Subgroup G}
    (hq : CFSG.Assembly.IsQuasisimple L) (heven : Even (Nat.card (centralizer (L : Set G))))
    (hLg : ∀ g : G, ⁅L, L.map (MulAut.conj g).toMonoidHom⁆ ≠ ⊥) :
    CFSG.Assembly.ComponentType.IsStandardSubgroup L ↔ ∀ t ∈ centralizer (L : Set G),
      orderOf t = 2 →
      CFSG.Assembly.IsComponentOf L (centralizer ({t} : Set G)) := by
  constructor
  · intro hL t ht ht2
    exact (standard_involution_centralizer_normality hL ht ht2).2.2.2.1
  · intro hcomp
    set C := centralizer (L : Set G)
    have key : ∀ g : G, Even (Nat.card (C ⊓ C.map (MulAut.conj g).toMonoidHom : Subgroup G)) →
        g ∈ normalizer (L : Set G) := by
      intro g hg
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card'
        (G := (C ⊓ C.map (MulAut.conj g).toMonoidHom : Subgroup G)) 2 (even_iff_two_dvd.1 hg)
      have ht2 : orderOf (t : G) = 2 := by rw [Subgroup.orderOf_coe, ht]
      obtain ⟨htC, s, hsC, hst⟩ := t.2
      have hs2 : orderOf s = 2 := by
        rw [← ht2, ← hst, MulEquiv.coe_toMonoidHom, MulEquiv.orderOf_eq]
      have h1 := hcomp t htC ht2
      have h2 := isComponentOf_map_conj (hcomp s hsC hs2) g
      rw [map_conj_centralizer_singleton] at h2
      have hgs : g * s * g⁻¹ = t := hst
      rw [hgs] at h2
      rcases isComponentOf_eq_or_commute h1 h2 with h | h
      · refine mem_normalizer_of_conjSub_le (le_of_eq h.symm) (le_of_eq ?_)
        calc conjSub g⁻¹ L = conjSub g⁻¹ (conjSub g L) := by
              rw [show conjSub g L = L from h.symm]
          _ = L := conjSub_inv_conjSub g L
      · exact absurd h (hLg g)
    have hNL : normalizer (L : Set G) ≤ normalizer (C : Set G) :=
      normalizer_le_normalizer_centralizer L
    refine ⟨hq, heven, fun g hg => ?_, le_antisymm (fun g hg => ?_) hNL, hLg⟩
    · rw [← Nat.not_even_iff_odd]
      exact fun he => hg (hNL (key g he))
    · apply key g
      rw [show C.map (MulAut.conj g).toMonoidHom = C from conjSub_eq_of_mem_normalizer hg,
        inf_idem]
      exact heven

end CFSG.LocalAnalysis.ComponentInitial
