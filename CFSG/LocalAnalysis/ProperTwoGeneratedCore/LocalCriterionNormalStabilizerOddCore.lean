module

public import CFSG.LocalAnalysis.ComponentClassification.OddCore
public import CFSG.GroupTheory.PCore.Defs

public section

namespace CFSG.ProperTwoGeneratedCore

variable {G : Type*} [Group G] [Finite G]

theorem actual_odd_core_normal_intersection (M : Subgroup G) [M.Normal] :
    (CFSG.oddCore M).map M.subtype = M ⊓ CFSG.oddCore G :=
  CFSG.ComponentClassification.OddCore.normal_intersection G M

theorem actual_odd_core_normal_subgroup_eq_bot
    (hodd : CFSG.oddCore G = ⊥) (M : Subgroup G) [M.Normal] : CFSG.oddCore M = ⊥ := by
  apply le_antisymm _ bot_le
  intro m hm
  have hmem := Subgroup.mem_map_of_mem M.subtype hm
  rw [actual_odd_core_normal_intersection, hodd, inf_bot_eq] at hmem
  exact Subgroup.mem_bot.mpr (Subtype.ext (Subgroup.mem_bot.mp hmem))

theorem actual_odd_core_intermediate_normal_element_eq_one
    (hodd : CFSG.oddCore G = ⊥) (M A : Subgroup G) [M.Normal] (hMA : M ≤ A)
    {x : G} (hxM : x ∈ M) (hxOdd : (⟨x, hMA hxM⟩ : A) ∈ CFSG.oddCore A) : x = 1 := by
  have hx : (⟨x, hxM⟩ : M) ∈ CFSG.oddCore M :=
    (CFSG.ComponentClassification.OddCore.normal_step_mem_iff hMA ⟨x, hxM⟩).mpr hxOdd
  rw [actual_odd_core_normal_subgroup_eq_bot hodd M] at hx
  exact congrArg Subtype.val (Subgroup.mem_bot.mp hx)

theorem center_eq_bot_of_actual_odd_core_and_two_core
    (hodd : CFSG.oddCore G = ⊥) (htwo : CFSG.pCore 2 G = ⊥) :
    Subgroup.center G = ⊥ := by
  by_contra hcenter
  have hcard : Nat.card (Subgroup.center G) ≠ 1 := by
    intro hcard
    exact hcenter (Subgroup.card_eq_one.mp hcard)
  obtain ⟨p, hp, hpcard⟩ := Nat.exists_prime_and_dvd hcard
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.center G) p hpcard
  let X := Subgroup.zpowers (x : G)
  have hXcenter : X ≤ Subgroup.center G := Subgroup.zpowers_le.mpr x.property
  have hXnormal : X.Normal := Subgroup.normal_of_le_center hXcenter
  have hXcard : Nat.card X = p := by
    rw [Nat.card_zpowers, Subgroup.orderOf_coe, hx]
  have hx1 : (x : G) ≠ 1 := by
    intro hx1
    have hone : x = 1 := Subtype.ext hx1
    rw [hone, orderOf_one] at hx
    exact hp.ne_one hx.symm
  have hxbot : (x : G) ∈ (⊥ : Subgroup G) := by
    by_cases hp2 : p = 2
    · have hXtwo : IsPGroup 2 X := IsPGroup.of_card (n := 1)
        (by simpa only [pow_one, hp2] using hXcard)
      have hle : X ≤ CFSG.pCore 2 G := le_sSup ⟨hXnormal, hXtwo⟩
      rw [htwo] at hle
      exact hle (Subgroup.mem_zpowers (x : G))
    · have hXodd : Odd (Nat.card X) := hXcard.symm ▸ hp.odd_of_ne_two hp2
      have hle : X ≤ CFSG.oddCore G := le_sSup ⟨hXnormal, hXodd⟩
      rw [hodd] at hle
      exact hle (Subgroup.mem_zpowers (x : G))
  exact hx1 (Subgroup.mem_bot.mp hxbot)

end CFSG.ProperTwoGeneratedCore
