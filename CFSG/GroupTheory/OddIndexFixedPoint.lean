module

public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.GroupTheory

theorem exists_conj_normalizer_of_odd_relIndex_of_prime {G : Type} [Group G] [Finite G]
    {p : ℕ} (hp : p.Prime) (H T : Subgroup G) (hT : IsPGroup p T)
    (hodd : ¬ p ∣ H.relIndex ⊤) :
    ∃ g : G, T ≤ Subgroup.normalizer ((H.map (MulAut.conj g).toMonoidHom) : Set G) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have hcard : Nat.card (G ⧸ H) = H.relIndex ⊤ := by
    rw [← Subgroup.index_eq_card, Subgroup.relIndex_top_right]
  have hnot : ¬ p ∣ Nat.card (G ⧸ H) := by
    rw [hcard]
    exact hodd
  obtain ⟨q, hq⟩ := hT.nonempty_fixed_point_of_prime_not_dvd_card (G ⧸ H) hnot
  refine ⟨q.out, ?_⟩
  have hstab : MulAction.stabilizer G ((q.out : G ⧸ H)) =
      H.map (MulAut.conj q.out).toMonoidHom := by
    rw [show ((q.out : G ⧸ H)) = q.out • ((1 : G) : G ⧸ H) by simp,
      MulAction.stabilizer_smul_eq_stabilizer_map_conj,
      MulAction.stabilizer_quotient]
  have hTle : T ≤ H.map (MulAut.conj q.out).toMonoidHom := by
    rw [← hstab]
    intro t ht
    rw [MulAction.mem_stabilizer_iff]
    simpa [QuotientGroup.out_eq'] using hq ⟨t, ht⟩
  exact hTle.trans Subgroup.le_normalizer

theorem exists_conj_normalizer_of_odd_relIndex {G : Type} [Group G] [Finite G]
    (H T : Subgroup G) (hT : IsPGroup 2 T) (hodd : Odd (H.relIndex ⊤)) :
    ∃ g : G, T ≤ Subgroup.normalizer ((H.map (MulAut.conj g).toMonoidHom) : Set G) :=
  exists_conj_normalizer_of_odd_relIndex_of_prime Nat.prime_two H T hT hodd.not_two_dvd_nat

end CFSG.GroupTheory
