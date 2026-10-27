module

public import CFSG.CharacterTheory.Burnside
public import CFSG.HardMathSupport.Curtis.Proving.PerfectTwoThree

public section

namespace CFSG.HardMathSupport.Curtis.Proving

theorem perfect_eq_bot_of_card_dvd_two_pow_mul_nine {G : Type*} [Group G] [Finite G] {a : ℕ}
    (V : Subgroup G) (hV : ⁅V, V⁆ = V) (hcard : Nat.card V ∣ 2 ^ a * 9) : V = ⊥ := by
  have hsolv : Group.IsSolvable V := by
    obtain ⟨d1, d2, hd1, hd2, hdeq⟩ := Nat.dvd_mul.mp hcard
    obtain ⟨i, -, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hd1
    have h9 : (9 : ℕ) = 3 ^ 2 := by norm_num
    rw [h9] at hd2
    obtain ⟨j, -, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hd2
    let : Fintype V := Fintype.ofFinite V
    refine CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow
      (a := i) (b := j) Nat.prime_two Nat.prime_three (by norm_num) ?_
    rw [← Nat.card_eq_fintype_card]
    exact hdeq.symm
  have hmap : Subgroup.map V.subtype ⊤ = V := by
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have hperf : ⁅(⊤ : Subgroup V), (⊤ : Subgroup V)⁆ = ⊤ := by
    apply Subgroup.map_injective (f := V.subtype) Subtype.val_injective
    rw [Subgroup.map_commutator, hmap, hV]
  have htop := eq_bot_of_perfect_solvable (K := V) ⊤ hperf
  rw [Subgroup.eq_bot_iff_forall]
  intro x hx
  have hx' : (⟨x, hx⟩ : V) ∈ (⊤ : Subgroup V) := Subgroup.mem_top _
  rw [htop, Subgroup.mem_bot] at hx'
  simpa using congrArg Subtype.val hx'

end CFSG.HardMathSupport.Curtis.Proving

end
