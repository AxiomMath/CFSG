module

public import CFSG.RankThree.PartOne.S12.Hyp

public section

namespace CFSG

theorem le_pElementSubgroup_of_isPGroup {G : Type} [Group G] {p : ℕ} (hp : p.Prime)
    {X P : Subgroup G} (hX : IsPGroup p X) (hXP : X ≤ P) :
    X ≤ CFSG.RankThree.PartOne.pElementSubgroup p P := by
  intro x hx
  apply Subgroup.subset_closure
  refine ⟨hXP hx, ?_⟩
  obtain ⟨k, hk⟩ := hX ⟨x, hx⟩
  have hk' : x ^ p ^ k = 1 := congrArg Subtype.val hk
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hp).1 (orderOf_dvd_of_pow_eq_one hk')
  exact ⟨j, hj⟩

end CFSG
