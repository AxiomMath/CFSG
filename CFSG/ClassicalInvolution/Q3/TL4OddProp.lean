module

public import CFSG.ClassicalInvolution.Q3.TL3GlueEdge

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Balance

section Edge

variable {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}

theorem card_closure_edge_eq_four (hd : TightDatum R S t) {J : Subgroup Y}
    (hJ : J ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R)) {u : Y}
    (hu : IsUniqueInvolution J u) : Nat.card (Subgroup.closure ({t, u} : Set Y)) = 4 := by
  obtain ⟨hne, hu2, hut, -⟩ := hd.edge_involution hJ hu
  have ht2 : t * t = 1 := by
    rw [← pow_two]
    exact hd.order ▸ pow_orderOf_eq_one t
  have ht1 : t ≠ 1 := fun h => by
    have h2 := hd.order
    rw [h, orderOf_one] at h2
    norm_num at h2
  exact Bootstrap.card_closure_pair_eq_four ht2 hu2 ht1 hu.ne_one (Ne.symm hne)
    (Subgroup.mem_centralizer_singleton_iff.mp hut).symm

end Edge

end CFSG.ClassicalInvolution.Q3.TL4
