module

public import Mathlib.GroupTheory.Index

public section

namespace CFSG.EvenSporadicStandard.TwoB.MW3

theorem natCard_eq_natCard_map_mul {G H : Type*} [Group G] [Group H] (f : G →* H)
    (S : Subgroup G) : Nat.card S = Nat.card (S.map f) * Nat.card ↥(S ⊓ f.ker) := by
  let g : S →* H := f.comp S.subtype
  have h1 : Nat.card g.ker * g.ker.index = Nat.card S := Subgroup.card_mul_index g.ker
  have h2 : g.ker.index = Nat.card g.range := Subgroup.index_ker g
  have h3 : Nat.card g.range = Nat.card (S.map f) := by
    refine Nat.card_congr (Equiv.subtypeEquivRight fun x => ?_)
    simp only [MonoidHom.mem_range, Subgroup.mem_map, g, MonoidHom.comp_apply,
      Subgroup.coe_subtype]
    constructor
    · rintro ⟨s, rfl⟩
      exact ⟨s, s.2, rfl⟩
    · rintro ⟨s, hs, rfl⟩
      exact ⟨⟨s, hs⟩, rfl⟩
  have h4 : Nat.card g.ker = Nat.card ↥(S ⊓ f.ker) := by
    refine Nat.card_congr
      { toFun := fun x => ⟨(x.1 : G), x.1.2, x.2⟩
        invFun := fun y => ⟨⟨y.1, (Subgroup.mem_inf.1 y.2).1⟩, (Subgroup.mem_inf.1 y.2).2⟩
        left_inv := fun x => rfl
        right_inv := fun y => rfl }
  rw [← h1, h2, h3, h4, mul_comm]

theorem eq_of_le_of_natCard_le {G : Type*} [Group G] {H K : Subgroup G} (hle : H ≤ K)
    (hK : Nat.card K ≠ 0) (hcard : Nat.card K ≤ Nat.card H) : H = K := by
  have : Finite K := Nat.finite_of_card_ne_zero hK
  exact Subgroup.eq_of_le_of_card_ge hle hcard

end CFSG.EvenSporadicStandard.TwoB.MW3
