module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoB.Setting
public import CFSG.LocalAnalysis.EvenSporadicStandard.Common

public section

namespace CFSG.EvenSporadicStandard.TwoB

open Subgroup CFSG.Blueprint.NativeSporadic CFSG.Open
  CFSG.LocalAnalysis.ComponentInitial.Finkelstein1977

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {t : G}

theorem Setting.mem_centralizer (h : Setting G L t) : t ∈ centralizer (L : Set G) := by
  have htmem : t ∈ (center L).map L.subtype := h.center_eq ▸ mem_zpowers t
  exact ((map_center_eq_inf_centralizer L) ▸ htmem).2

theorem Setting.orderOf_eq (h : Setting G L t) : orderOf t = 2 :=
  orderOf_eq_two_of_center h.card_center h.center_eq

section Certified

theorem Setting.centralizer_le_sup (h : Setting G L t) :
    centralizer ({t} : Set G) ≤ L ⊔ centralizer (L : Set G) :=
  h.std.centralizer_le_sup_centralizer_of_mulAut_inner h.mem_centralizer h.orderOf_eq
    (IsTwoBCover.of_stdHyp h.std h.card_center h.quot_B).allInner

theorem Setting.exists_cyclic_sylow_centralizer_eq (h : Setting G L t) :
    ∃ S : Sylow 2 (centralizer (L : Set G)), IsCyclic S ∧
      (⟨t, h.mem_centralizer⟩ : centralizer (L : Set G)) ∈ S ∧
      centralizer ({t} : Set G) =
        L ⊔ (S : Subgroup (centralizer (L : Set G))).map (centralizer (L : Set G)).subtype := by
  obtain ⟨S, hS, htS⟩ := h.std.exists_cyclic_sylow_mem h.mem_centralizer h.orderOf_eq
  exact ⟨S, hS, htS, h.std.centralizer_eq_sup_map_sylow h.mem_centralizer h.orderOf_eq S hS htS
    h.centralizer_le_sup⟩

theorem Setting.centralizer_eq_of_card_sylow (h : Setting G L t)
    (hS : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) :
    centralizer ({t} : Set G) = L :=
  h.std.centralizer_eq_of_mem_center hS h.orderOf_eq (h.center_eq ▸ mem_zpowers t)
    h.centralizer_le_sup

theorem Setting.centralizer_eq_of_finkelstein (h : Setting G L t)
    (hI : HypothesisOne (L ⧸ center L)) (hrank : 3 ≤ twoRank (L ⧸ center L))
    (h25 : Finkelstein77.Asc76Lemma25) : centralizer ({t} : Set G) = L :=
  h.centralizer_eq_of_card_sylow fun S => h.std.card_sylow_centralizer_eq_two hI hrank h25 S

end Certified

end CFSG.EvenSporadicStandard.TwoB
