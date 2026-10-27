module

public import CFSG.GroupTheory.SevenInvolutionWreathLawLocal

public section

namespace CFSG.GroupTheory

open CFSG.Assembly CFSG.GroupTheory.SevenInvolutionWreathLaw

theorem seven_involution_centralizer_wreath_law_and_small_polygons {K : Type*} [Group K]
    [Finite K] (hconj : ∀ u v : K, orderOf u = 2 → orderOf v = 2 → IsConj u v)
    (S : Subgroup K) (s t w : K) (hst : s * t = t * s) (hs : orderOf s = 4) (ht : orderOf t = 4)
    (hinter : Subgroup.zpowers s ⊓ Subgroup.zpowers t = ⊥) (hw : orderOf w = 2)
    (hwout : w ∉ Subgroup.closure {s, t}) (hsw : w⁻¹ * s * w = t) (htw : w⁻¹ * t * w = s)
    (_hS : S = Subgroup.closure {s, t, w})
    (h7 : {g : K | g ∈ Subgroup.centralizer {(s * t) ^ 2} ∧ orderOf g = 2}.ncard = 7) :
    (∀ z u v : K, orderOf z = 2 → orderOf u = 2 → orderOf v = 2 →
      u ∈ Subgroup.centralizer {z} → v ∈ Subgroup.centralizer {z} → u ≠ v → u ≠ z → v ≠ z →
      (u * v = v * u → u * v = z) ∧ (u * v ≠ v * u → (u * v) ^ 2 = z)) ∧
    (∀ z : {g : K // orderOf g = 2}, ((involutionGraph K).neighborSet z).ncard = 6) ∧
    (∀ z u : {g : K // orderOf g = 2}, (involutionGraph K).Adj z u →
      ∃ u' : {g : K // orderOf g = 2}, (u' : K) = z * u ∧ (involutionGraph K).Adj z u' ∧
        (involutionGraph K).Adj u u' ∧
        ∀ v, (involutionGraph K).Adj z v → (involutionGraph K).Adj u v → v = u') ∧
    (∀ a b c : {g : K // orderOf g = 2}, (involutionGraph K).Adj a b →
      (involutionGraph K).Adj b c → (involutionGraph K).Adj a c →
      ∃ V : Subgroup K, IsKleinFour V ∧ (V : Set K) \ {1} = {(a : K), (b : K), (c : K)}) ∧
    (¬ ∃ a b c d : {g : K // orderOf g = 2}, [a, b, c, d].Nodup ∧
      (involutionGraph K).Adj a b ∧ (involutionGraph K).Adj b c ∧
      (involutionGraph K).Adj c d ∧ (involutionGraph K).Adj d a ∧
      ¬ (involutionGraph K).Adj a c ∧ ¬ (involutionGraph K).Adj b d) ∧
    ¬ ∃ a b c d e : {g : K // orderOf g = 2}, [a, b, c, d, e].Nodup ∧
      (involutionGraph K).Adj a b ∧ (involutionGraph K).Adj b c ∧
      (involutionGraph K).Adj c d ∧ (involutionGraph K).Adj d e ∧
      (involutionGraph K).Adj e a ∧ ¬ (involutionGraph K).Adj a c ∧
      ¬ (involutionGraph K).Adj a d ∧ ¬ (involutionGraph K).Adj b d ∧
      ¬ (involutionGraph K).Adj b e ∧ ¬ (involutionGraph K).Adj c e := by
  obtain ⟨hxord, hlawx⟩ := local_product_law hst hs ht hinter hw hwout hsw htw h7
  have hlaw := involutionProductLaw_of_conj hconj hxord hlawx
  refine ⟨hlaw, fun z => ncard_neighborSet_eq_six z
    (ncard_involutions_centralizer_of_conj hconj hxord h7 z.2),
    exists_neighbor_partner hlaw, exists_kleinFour_of_triangle hlaw,
    not_exists_induced_square hlaw, not_exists_induced_pentagon hlaw⟩

end CFSG.GroupTheory
