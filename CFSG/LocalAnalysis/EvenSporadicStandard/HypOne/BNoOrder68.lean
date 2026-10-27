module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HypOne.BAux
public import CFSG.LocalAnalysis.EvenSporadicStandard.HypOne.BMain

public section

set_option linter.unusedSectionVars false

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.EvenSporadicStandard.HypOne.BabyHyp

open Subgroup CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.Monster.GMS
  CFSG.EvenSporadicStandard.Solomon78

@[expose] def BabyNoOrder68 : Prop := ∀ g : NativeSporadic.B, orderOf g ≠ 68

theorem isPerfect_of_isSimpleGroup {F : Type*} [Group F] [Finite F] [IsSimpleGroup F]
    (h : ¬ (Nat.card F).Prime) : Group.IsPerfect F := by
  refine ⟨?_⟩
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator F) with h0 | h0
  · exfalso
    obtain ⟨x, y, hxy⟩ := exists_noncomm_of_isSimpleGroup h
    have hmem : x * y * x⁻¹ * y⁻¹ ∈ commutator F :=
      Subgroup.commutator_mem_commutator (Subgroup.mem_top x) (Subgroup.mem_top y)
    rw [h0, Subgroup.mem_bot, mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at hmem
    exact hxy hmem
  · exact h0

theorem rootClassLarge_of_simple_seventeen {Y : Type*} [Group Y] [Finite Y] {a : Y}
    (ha : orderOf a = 2) (hno : ∀ g : Y, orderOf g ≠ 68) {F : Subgroup Y}
    (hFle : F ≤ centralizer ({a} : Set Y)) [IsSimpleGroup F] (hF17 : 17 ∣ Nat.card F)
    (hFnp : ¬ (Nat.card F).Prime) : RootClassLarge a := by
  intro n hn
  by_contra hlt
  have hle : Nat.card {y : centralizer ({a} : Set Y) // IsConj n y} ≤ 4 := by omega
  let L : Subgroup (centralizer ({a} : Set Y)) := F.subgroupOf (centralizer ({a} : Set Y))
  let eL : L ≃* F := Subgroup.subgroupOfEquivOfLe hFle
  have : IsSimpleGroup L := MulEquiv.isSimpleGroup eL
  have hLcard : Nat.card L = Nat.card F := Nat.card_congr eL.toEquiv
  have hLperf : Group.IsPerfect L := isPerfect_of_isSimpleGroup (by rw [hLcard]; exact hFnp)
  have hcent := isPerfect_centralizes_of_card_conj_le L hLperf n hle
  have : Fact (Nat.Prime 17) := ⟨by norm_num⟩
  obtain ⟨x, hx17⟩ := exists_prime_orderOf_dvd_card' (G := L) 17 (by rw [hLcard]; exact hF17)
  have hxn : (x : centralizer ({a} : Set Y)) * n = n * x := by
    have h1 := hcent x x.2
    rwa [mul_inv_eq_iff_eq_mul] at h1
  have hcomm : Commute ((x : centralizer ({a} : Set Y)) : Y) (n : Y) := congrArg Subtype.val hxn
  have ha2 : a ^ 2 = 1 := ha ▸ pow_orderOf_eq_one a
  have ha1 : a ≠ 1 := fun h => by rw [h, orderOf_one] at ha; omega
  have hn2 : (n : Y) ^ 2 = a := by rw [pow_two]; exact hn
  have hn4 : orderOf (n : Y) = 4 := by
    have h4 : orderOf (n : Y) = 2 ^ (1 + 1) :=
      orderOf_eq_prime_pow (p := 2) (by rw [pow_one, hn2]; exact ha1)
        (by rw [show 2 ^ (1 + 1) = 2 * 2 from rfl, pow_mul, hn2, ha2])
    rw [h4]
    norm_num
  have hx17' : orderOf (((x : centralizer ({a} : Set Y)) : Y)) = 17 := by
    rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe]
    exact hx17
  have h68 : orderOf (((x : centralizer ({a} : Set Y)) : Y) * (n : Y)) = 68 := by
    rw [hcomm.orderOf_mul_eq_mul_orderOf_of_coprime (by rw [hx17', hn4]; norm_num), hx17', hn4]
  exact hno _ h68


theorem babyRootClassLarge_three_of_noOrder68 (h68 : BabyNoOrder68) : BabyRootClassLarge 3 := by
  have hfin := CFSG.Monster.B.Pinned.finite_B
  intro a ha
  obtain ⟨F, hFle, hFs, hFcard⟩ := babyF4Subgroup_B a ha
  exact @rootClassLarge_of_simple_seventeen NativeSporadic.B Units.instGroup hfin a ha.1 h68 F hFle
    hFs (by rw [hFcard]; norm_num) (by rw [hFcard]; norm_num)

end CFSG.EvenSporadicStandard.HypOne.BabyHyp
