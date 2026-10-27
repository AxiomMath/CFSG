module

public import CFSG.GroupTheory.InvolutionHexagonAction
public import CFSG.GroupTheory.SevenInvolutionWreathLaw

public section

namespace CFSG.GroupTheory.InvolutionHexagon

open CFSG.Assembly CFSG.GroupTheory.SevenInvolutionWreathLaw

theorem involution_hexagon_of_local_data {G : Type*} [Group G] [Finite G]
    (hcard : Nat.card {g : G // orderOf g = 2} = 63) (hlaw : InvolutionProductLaw G)
    (hval : ∀ z : {g : G // orderOf g = 2}, ((involutionGraph G).neighborSet z).ncard = 6) :
    Nat.card (InvLine G) = 63 ∧ (∀ T : InvLine G, T.1.ncard = 3) ∧
    (∀ p : {g : G // orderOf g = 2}, {T : InvLine G | (p : G) ∈ T.1}.ncard = 3) ∧
    (incidenceGraph (invInc G)).Connected ∧ (incidenceGraph (invInc G)).girth = 12 ∧
    (incidenceGraph (invInc G)).diam = 6 ∧
    involutionGraph G = collinearityGraph (invInc G) ∧
    (involutionGraph G).Connected ∧ (involutionGraph G).diam = 3 ∧
    (∀ (p : {g : G // orderOf g = 2}) (k : Fin 4),
      {q : {g : G // orderOf g = 2} | (involutionGraph G).dist p q = k}.ncard =
        ![1, 6, 24, 32] k) ∧
    (∀ (p : {g : G // orderOf g = 2}) (T : InvLine G), ∃! q : {g : G // orderOf g = 2},
      (q : G) ∈ T.1 ∧ ∀ q' : {g : G // orderOf g = 2}, (q' : G) ∈ T.1 →
        (involutionGraph G).dist p q ≤ (involutionGraph G).dist p q') ∧
    (∀ (g : G) (p : {g : G // orderOf g = 2}), ∃ p' : {g : G // orderOf g = 2},
      conjAction G g (Sum.inl p) = Sum.inl p' ∧ (p' : G) = g * p * g⁻¹) ∧
    (∀ (g : G) (T : InvLine G), ∃ T' : InvLine G, conjAction G g (Sum.inr T) = Sum.inr T' ∧
      T'.1 = (fun y => g * y * g⁻¹) '' T.1) ∧
    (IsSimpleGroup G → Function.Injective (conjAction G)) ∧
    ∀ (x : {g : G // orderOf g = 2}) (S : Subgroup G), Nat.card S = 32 →
      (∀ s ∈ S, s * (x : G) = x * s) →
      {z : {g : G // orderOf g = 2} | (involutionGraph G).dist x z = 3}.ncard = 32 ∧
      ∀ z z' : {g : G // orderOf g = 2}, (involutionGraph G).dist x z = 3 →
        (involutionGraph G).dist x z' = 3 → ∃! s : S, (s : G) * z * (s : G)⁻¹ = z' := by
  have H := involutionHexagonData hcard hlaw hval
  obtain ⟨hL, hconn, hgirth, hdiam, hΓconn, hΓdiam, hlayer, hnear⟩ := H.hexagon
  have hΓ := involutionGraph_eq_collinearityGraph (G := G)
  refine ⟨hL, fun T => T.ncard, ncard_lines_through hval, hconn, hgirth, hdiam, hΓ,
    hΓ ▸ hΓconn, hΓ ▸ hΓdiam, hΓ ▸ hlayer, hΓ ▸ hnear,
    fun g p => ⟨conjPoint g p, rfl, coe_conjPoint g p⟩, fun g T => ⟨conjLine g T, rfl, ?_⟩,
    fun _ => conjAction_injective hcard hval,
    fun x S hS hSx => regular_on_opposite hcard hlaw hval x S hS hSx⟩
  show MulAut.conj g '' T.1 = (fun y => g * y * g⁻¹) '' T.1
  rfl

theorem localData_of_wreath {G : Type*} [Group G] [Finite G]
    (hconj : ∀ u v : G, orderOf u = 2 → orderOf v = 2 → IsConj u v) {s t w : G}
    (hst : s * t = t * s) (hs : orderOf s = 4) (ht : orderOf t = 4)
    (hinter : Subgroup.zpowers s ⊓ Subgroup.zpowers t = ⊥) (hw : orderOf w = 2)
    (hwout : w ∉ Subgroup.closure {s, t}) (hsw : w⁻¹ * s * w = t) (htw : w⁻¹ * t * w = s)
    (h7 : {g : G | g ∈ Subgroup.centralizer {(s * t) ^ 2} ∧ orderOf g = 2}.ncard = 7) :
    InvolutionProductLaw G ∧
      ∀ z : {g : G // orderOf g = 2}, ((involutionGraph G).neighborSet z).ncard = 6 := by
  obtain ⟨hlaw, hval, -⟩ := seven_involution_centralizer_wreath_law_and_small_polygons hconj
    (Subgroup.closure {s, t, w}) s t w hst hs ht hinter hw hwout hsw htw rfl h7
  exact ⟨hlaw, hval⟩

end CFSG.GroupTheory.InvolutionHexagon
