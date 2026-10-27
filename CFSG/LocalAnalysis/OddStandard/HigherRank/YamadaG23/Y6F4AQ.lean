module

public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.Algebra.Group.TypeTags.Finite
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.NormNum.Pow

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup

variable {Γ : Type*} [Group Γ]

private abbrev Z4cube : Type := Fin 3 → Multiplicative (ZMod 4)

theorem y6f4a_card_z4cube_sq_eq_one :
    Nat.card {f : Fin 3 → Multiplicative (ZMod 4) // f * f = 1} = 8 := by
  rw [Nat.card_eq_fintype_card]
  decide

private lemma natCard_z4cube : Nat.card Z4cube = 64 := by
  rw [Nat.card_fun, Nat.card_fin]
  rw [← Nat.card_congr (Multiplicative.ofAdd : ZMod 4 ≃ Multiplicative (ZMod 4))]
  rw [Nat.card_zmod]
  norm_num

private lemma z4cube_pow_four (x : Z4cube) : x ^ 4 = 1 := by
  funext i
  change (x i) ^ 4 = 1
  have h := pow_card_eq_one (G := Multiplicative (ZMod 4)) (x := x i)
  rw [Fintype.card_multiplicative, ZMod.card] at h
  exact h

private lemma card_sq_eq_one_of_mulEquiv {H : Type*} [Group H] (e : H ≃* Z4cube) :
    Nat.card {x : H // x * x = 1} = 8 := by
  have h : Nat.card {x : H // x * x = 1} = Nat.card {f : Z4cube // f * f = 1} :=
    Nat.card_congr (e.toEquiv.subtypeEquiv (fun x => by
      constructor
      · intro hx
        change e x * e x = 1
        rw [← map_mul, hx, map_one]
      · intro hx
        change e x * e x = 1 at hx
        apply e.injective
        rw [map_mul, hx, map_one]))
  rw [h]
  exact y6f4a_card_z4cube_sq_eq_one

private lemma exists_order_four_of_index_le_two {H : Type*} [Group H]
    (e : H ≃* Z4cube) (K : Subgroup H) (hK : K.index ≤ 2) :
    ∃ x ∈ K, orderOf x = 4 := by
  have hcardH : Nat.card H = 64 := by
    rw [Nat.card_congr e.toEquiv, natCard_z4cube]
  haveI : Finite H := Nat.finite_of_card_ne_zero (by rw [hcardH]; norm_num)
  have hcard : Nat.card K * K.index = 64 := by
    rw [Subgroup.card_mul_index, hcardH]
  have hne : K.index ≠ 0 := by
    intro h
    rw [h, mul_zero] at hcard
    omega
  have hge : 32 ≤ Nat.card K := by
    have h1 : 1 ≤ K.index := Nat.one_le_iff_ne_zero.mpr hne
    have hcases : K.index = 1 ∨ K.index = 2 := by omega
    rcases hcases with h | h <;> rw [h] at hcard <;> omega
  have hex : ∃ x ∈ K, x * x ≠ 1 := by
    by_contra hcon
    push_neg at hcon
    have hinj : Function.Injective
        (fun x : K => (⟨(x : H), hcon x x.2⟩ : {x : H // x * x = 1})) := by
      intro a b hab
      have h : (a : H) = (b : H) :=
        congrArg (fun z : {x : H // x * x = 1} => (z : H)) hab
      exact Subtype.ext h
    have hle : Nat.card K ≤ Nat.card {x : H // x * x = 1} :=
      Nat.card_le_card_of_injective _ hinj
    rw [card_sq_eq_one_of_mulEquiv e] at hle
    omega
  obtain ⟨x, hxK, hxne⟩ := hex
  refine ⟨x, hxK, ?_⟩
  have hx4 : x ^ 4 = 1 := by
    apply e.injective
    rw [map_pow, z4cube_pow_four, map_one]
  have hnot : ¬ x ^ 2 ^ 1 = 1 := by
    have hpow : (2 : ℕ) ^ 1 = 2 := by norm_num
    rw [hpow]
    intro h
    exact hxne (by rwa [pow_two] at h)
  have hfin : x ^ 2 ^ (1 + 1) = 1 := by
    have hpow : (2 : ℕ) ^ (1 + 1) = 4 := by norm_num
    rw [hpow]
    exact hx4
  exact orderOf_eq_prime_pow (p := 2) (n := 1) hnot hfin

theorem y6f4a_exists_order_four {M K : Subgroup Γ}
    (hM : Nonempty (↥M ≃* (Fin 3 → Multiplicative (ZMod 4)))) (hidx : K.relIndex M ≤ 2) :
    ∃ x ∈ K, x ∈ M ∧ orderOf x = 4 := by
  obtain ⟨e⟩ := hM
  have hidx' : (K.subgroupOf M).index ≤ 2 := by
    simpa only [Subgroup.relIndex] using hidx
  obtain ⟨x, hxK, hxord⟩ := exists_order_four_of_index_le_two e (K.subgroupOf M) hidx'
  exact ⟨(x : Γ), Subgroup.mem_subgroupOf.mp hxK, x.2, by
    rw [Subgroup.orderOf_coe]; exact hxord⟩

end CFSG.OddStandard.HigherRank.YamadaG23
