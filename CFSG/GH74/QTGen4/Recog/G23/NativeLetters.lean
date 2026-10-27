module

public import CFSG.GH74.QTGen4.Recog.G23.Native
public import CFSG.RankThree.PartTwo.Census.Carrier.G2Three

public section

namespace CFSG.GH74.QTGen4.Recog.G23

open CFSG.RankThree.PartTwo.Census.Carrier.G2Three

theorem involutions_conj_transfer {G : Type} [Group G] {H : Type} [Group H] [Finite H]
    (e : G ≃* H) (t : H) (S : Subgroup H) (hcard : Nat.card H = 4245696)
    (hS : Nat.card S = 64) (hSinv : ∀ u ∈ S, orderOf u = 2 → ∃ g : H, u = g * t * g⁻¹)
    (a b : G) (ha : orderOf a = 2) (hb : orderOf b = 2) : ∃ g : G, b = g * a * g⁻¹ := by
  have hea : orderOf (e a) = 2 := (orderOf_injective e.toMonoidHom e.injective a).trans ha
  have heb : orderOf (e b) = 2 := (orderOf_injective e.toMonoidHom e.injective b).trans hb
  obtain ⟨g1, hg1⟩ := exists_conj_of_sylow (t := t) hcard hS hSinv hea
  obtain ⟨g2, hg2⟩ := exists_conj_of_sylow (t := t) hcard hS hSinv heb
  refine ⟨e.symm (g2 * g1⁻¹), ?_⟩
  apply e.injective
  rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply, hg1, hg2]
  group

theorem ghat_card : Nat.card Ghat = 7371 * 576 :=
  (Nat.card_congr adjointEquivR3.toEquiv).trans (card_R3.trans (by norm_num))

set_option maxHeartbeats 400000 in
theorem ghat_involutions_conj :
    ∀ a b : Ghat, orderOf a = 2 → orderOf b = 2 → ∃ g, b = g * a * g⁻¹ := by
  have hcard3 : Nat.card H3 = 4245696 := card_R3
  have hfin : Finite H3 := Nat.finite_of_card_ne_zero (by rw [hcard3]; norm_num)
  intro a b ha hb
  exact involutions_conj_transfer (G := Ghat) (H := H3) adjointEquivR3 tH S2H hcard3 card_S2H
    (fun u hu hu2 => exists_conj_of_mem_S2H u hu hu2) a b ha hb

end CFSG.GH74.QTGen4.Recog.G23
