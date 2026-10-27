module

public import CFSG.GF2Type.Aschbacher1976HigherCenter.CenterFacts
import CFSG.Dihedral.DisconnectedInvolutionGraph.CyclicRootTI

public section

namespace CFSG.GF2Type.Aschbacher1976HigherCenter

open Subgroup CFSG CFSG.Open

theorem exists_order_four_subgroup
    {G : Type} [Group G] [Finite G] {M B Q : Subgroup G} {z : G} {D : Subgroup Q} {k u : ℕ}
    (h : Setup M B Q z D k u) :
    ∃ T : Subgroup G, T ≤ critCenter D ∧ Nat.card T = 4 ∧ z ∈ T ∧ IsCyclic T := by
  classical
  obtain ⟨hYcyc, -, hYcard, -, -, -, huniq, -⟩ := center_facts h
  obtain ⟨y₀, hy₀⟩ := hYcyc.exists_generator
  have hk3 := h.three_le
  have hy₀o : orderOf (y₀ : G) = 2 ^ k := by
    rw [Subgroup.orderOf_coe, orderOf_eq_card_of_forall_mem_zpowers hy₀, hYcard]
  have hdvd : 2 ^ (k - 2) ∣ orderOf (y₀ : G) := hy₀o ▸ pow_dvd_pow 2 (by omega)
  have htY : (y₀ : G) ^ 2 ^ (k - 2) ∈ critCenter D := pow_mem y₀.2 _
  have ht4 : orderOf ((y₀ : G) ^ 2 ^ (k - 2)) = 4 := by
    rw [orderOf_pow_of_dvd (by positivity) hdvd, hy₀o, Nat.pow_div (by omega) (by norm_num),
      show k - (k - 2) = 2 by omega]
  have hz : ((y₀ : G) ^ 2 ^ (k - 2)) ^ 2 = z :=
    huniq _ (pow_mem htY 2) (by rw [orderOf_pow' _ two_ne_zero, ht4]; rfl)
  refine ⟨zpowers ((y₀ : G) ^ 2 ^ (k - 2)), zpowers_le.2 htY, by rw [Nat.card_zpowers, ht4], ?_,
    inferInstance⟩
  rw [← hz]
  exact pow_mem (mem_zpowers _) 2

theorem normalizer_order_four_eq
    {G : Type} [Group G] [Finite G] {M B Q : Subgroup G} {z : G} {D : Subgroup Q} {k u : ℕ}
    (h : Setup M B Q z D k u) {T : Subgroup G} (hTY : T ≤ critCenter D) (hT4 : Nat.card T = 4) :
    normalizer (T : Set G) = M := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hYcyc, -, -, -, hnorm, -, huniq, -⟩ := center_facts h
  haveI : IsCyclic (critCenter D) := hYcyc
  have hzT : z ∈ T := by
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := T) 2 (by rw [hT4]; norm_num)
    have hxz : (x : G) = z := huniq _ (hTY x.2) (by rw [Subgroup.orderOf_coe]; exact hx)
    rw [← hxz]
    exact x.2
  ext g
  constructor
  · intro hg
    have h1 : g * z * g⁻¹ ∈ T := (mem_normalizer_iff.mp hg z).mp hzT
    have h2 : orderOf (g * z * g⁻¹) = 2 := by
      have h3 := MulEquiv.orderOf_eq (MulAut.conj g) z
      rw [MulAut.conj_apply] at h3
      rw [h3]
      exact h.involution
    have h4 : g * z * g⁻¹ = z := huniq _ (hTY h1) h2
    rw [h.local_eq]
    exact mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp h4)
  · intro hgM
    rw [← hnorm] at hgM
    have hY : (critCenter D).map (MulAut.conj g).toMonoidHom = critCenter D :=
      mem_normalizer_iff_map_conj_eq.mp hgM
    have hle : T.map (MulAut.conj g).toMonoidHom ≤ critCenter D := hY ▸ map_mono hTY
    have hcard : Nat.card T = Nat.card (T.map (MulAut.conj g).toMonoidHom) :=
      (card_map_of_injective (MulAut.conj g).injective).symm
    have hTT := CFSG.DisconnectedInvolutionGraph.Helpers.cyclic_overgroup_equal_card_subgroups
      (critCenter D) T (T.map (MulAut.conj g).toMonoidHom) hTY hle hcard
    exact mem_normalizer_iff_map_conj_eq.mpr hTT.symm

end CFSG.GF2Type.Aschbacher1976HigherCenter
