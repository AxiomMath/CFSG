module

public import CFSG.GF2Type.Aschbacher1976HigherCenter.OrderFour
public import CFSG.GF2Type.Aschbacher1976Common.CyclicTIWeakClosure
import CFSG.GroupTheory.PCore.PrimeSetCore
import CFSG.Dihedral.DisconnectedInvolutionGraph.CyclicRootTI

public section

namespace CFSG.GF2Type.Aschbacher1976HigherCenter

open Subgroup CFSG CFSG.Open

theorem exists_conjugate_center_in_local
    {G : Type} [Group G] [Finite G] {M B Q : Subgroup G} {z : G} {D : Subgroup Q} {k u : ℕ}
    (h : Setup M B Q z D k u) {T : Subgroup G} (hTY : T ≤ critCenter D) (hT4 : Nat.card T = 4)
    (hT : ∃ g : G, conjugate T g ≤ normalizer (T : Set G) ∧ conjugate T g ≠ T) :
    ∃ g : G, conjugate (critCenter D) g ≤ M ∧ conjugate (critCenter D) g ≠ critCenter D := by
  classical
  obtain ⟨hYcyc, hY2, hYcard, hTI, hnorm, -⟩ := center_facts h
  haveI : IsCyclic (critCenter D) := hYcyc
  have hTN : normalizer (T : Set G) = M := normalizer_order_four_eq h hTY hT4
  obtain ⟨g, hgT, hgne⟩ := hT
  have hTcyc : IsCyclic T :=
    isCyclic_of_surjective (Subgroup.subgroupOfEquivOfLe hTY).toMonoidHom (MulEquiv.surjective _)
  have hTgcyc : IsCyclic (conjugate T g) :=
    isCyclic_of_surjective
      (T.equivMapOfInjective (MulAut.conj g⁻¹).toMonoidHom (MulAut.conj g⁻¹).injective).toMonoidHom
      (MulEquiv.surjective _)
  have hTgcard : Nat.card (conjugate T g) = 4 := by
    rw [← hT4]
    exact card_map_of_injective (MulAut.conj g⁻¹).injective
  obtain ⟨t, ht⟩ := hTgcyc.exists_generator
  have hto : orderOf (t : G) = 4 := by
    rw [Subgroup.orderOf_coe, orderOf_eq_card_of_forall_mem_zpowers ht, hTgcard]
  have htYg : (t : G) ∈ conjugate (critCenter D) g := by
    have : conjugate T g ≤ conjugate (critCenter D) g := by
      intro x hx
      rw [mem_conjugate_iff] at hx ⊢
      exact hTY hx
    exact this t.2
  have htN : (t : G) ∈ normalizer (critCenter D : Set G) := by
    rw [hnorm]
    exact hTN ▸ hgT t.2
  have hne : conjugate (critCenter D) g ≠ critCenter D := by
    intro hcon
    apply hgne
    have hle : conjugate T g ≤ critCenter D := by
      intro x hx
      have : x ∈ conjugate (critCenter D) g := by
        rw [mem_conjugate_iff] at hx ⊢
        exact hTY hx
      rwa [hcon] at this
    exact CFSG.DisconnectedInvolutionGraph.Helpers.cyclic_overgroup_equal_card_subgroups
      (critCenter D) (conjugate T g) T hle hTY (by rw [hTgcard, hT4])
  have hk2 : (t : G) ^ 2 ≠ 1 := by
    intro h1
    have := orderOf_dvd_of_pow_eq_one h1
    rw [hto] at this
    norm_num at this
  have hle := CFSG.GF2Type.Aschbacher1976Common.conjugate_inv_le_normalizer hYcyc hY2 hTI hne
    htYg htN hk2
  refine ⟨g⁻¹, hnorm ▸ hle, ?_⟩
  intro hcon
  apply hne
  have h1 := congrArg (fun H => conjugate H g) hcon
  have h2 : critCenter D = conjugate (critCenter D) g := by simpa [conjugate_conjugate] using h1
  exact h2.symm

end CFSG.GF2Type.Aschbacher1976HigherCenter
