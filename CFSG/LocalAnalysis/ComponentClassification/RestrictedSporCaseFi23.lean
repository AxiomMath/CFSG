module

public import CFSG.LocalAnalysis.ComponentClassification.RestrictedSporCaseFi24
public import CFSG.LocalAnalysis.ComponentClassification.RestrictedSporLocal
public import CFSG.Sporadic.FischerOddCore.Fi23Aut

public section

namespace CFSG.ComponentClassification.RestrictedStd.Spor

open CFSG Subgroup CFSG.Blueprint CFSG.Sporadic.FischerOddCore
open CFSG.ComponentClassification.OuterAutomorphisms

theorem fi23_inner_comps {G : Type} [Group G] (e : G ≃* NativeSporadic.Fi23) (t : G)
    (ht : orderOf t = 2) :
    CompsSatisfy (centralizer ({t} : Set G)) fun Y _ =>
      Nat.card (Y ⧸ center Y) ∈ ({64561751654400, 9196830720} : Set ℕ) := by
  set f : G ≃* CFSG.Sporadic.Fi23.J := e.trans CFSG.Sporadic.Fi23.fi23EquivJ
  have hQ := isoInvariant_card_quotient_center ({64561751654400, 9196830720} : Set ℕ)
  refine @CompsSatisfy.of_mulEquiv _ _ _ (Subgroup.toGroup _) _ hQ
    (@centralizerEquiv G _ _ (Subgroup.toGroup _) f t) ?_
  have hx2 : f t ^ 2 = 1 := by
    rw [← map_pow, ← ht, pow_orderOf_eq_one, map_one]
  have hx1 : f t ≠ 1 := fun h => by
    rw [MulEquiv.map_eq_one_iff] at h
    rw [h, orderOf_one] at ht
    omega
  rcases CFSG.Sporadic.Fi23.involution_cover (f t) hx2 hx1 with h | h | h
  · exact @compsSatisfy_centralizer_of_isConj _ (Subgroup.toGroup _) _ _ h _ hQ fun B hB =>
      Or.inl (card_quotient_center_of_component_Cd hB)
  · exact @compsSatisfy_centralizer_of_isConj _ (Subgroup.toGroup _) _ _ h _ hQ fun B hB =>
      Or.inr (card_quotient_center_of_component_dd1 hB)
  · exact @compsSatisfy_centralizer_of_isConj _ (Subgroup.toGroup _) _ _ h _ hQ fun B hB =>
      absurd hB (fi23_no_component_t2 B)

theorem sporadicCase_Fi23 : SporadicCase .Fi23 := by
  refine sporadicCase_of_comps (fun G _ _ ⟨e⟩ t ht => ?_)
    (outer_of_forall_inner fun α => by
      show α ∈ inner NativeSporadic.Fi23
      rw [CTUC_Fi23_all_automorphisms_inner.1]
      trivial)
  refine (fi23_inner_comps e t ht).mono fun Y _ h => not_small_of_card_quotient ?_
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h
  rcases h with h | h <;> rw [h]
  · exact not_isSmallOrder_Fi22
  · exact not_isSmallOrder_U62

end CFSG.ComponentClassification.RestrictedStd.Spor
