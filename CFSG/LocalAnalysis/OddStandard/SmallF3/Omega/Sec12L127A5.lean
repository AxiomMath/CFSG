module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Blueprint.Chevalley
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.TypesSign

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint
open scoped Pointwise

variable {G : Type} [Group G]

theorem sec127_card_alt5_type : Nat.card ↥(alternatingGroup (Fin 5)) = 60 := by
  rw [nat_card_alternatingGroup]
  simp [Nat.factorial]

theorem sec127_card_alt5 {X : Subgroup G}
    (hX : Nonempty (↥X ≃* ↥(alternatingGroup (Fin 5)))) : Nat.card ↥X = 60 := by
  obtain ⟨e⟩ := hX
  rw [Nat.card_congr e.toEquiv, sec127_card_alt5_type]

theorem sec127_center_alt5 {X : Subgroup G}
    (hX : Nonempty (↥X ≃* ↥(alternatingGroup (Fin 5)))) {u : G} (hu : u ∈ X)
    (hc : ∀ x ∈ X, u * x = x * u) : u = 1 := by
  obtain ⟨e⟩ := hX
  have hz : e ⟨u, hu⟩ ∈ Subgroup.center ↥(alternatingGroup (Fin 5)) := by
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨x, rfl⟩ := e.surjective g
    rw [← map_mul, ← map_mul]
    exact congrArg e (Subtype.ext (hc x x.2).symm)
  rw [alternatingGroup.center_eq_bot (by simp)] at hz
  have h1 : (⟨u, hu⟩ : ↥X) = 1 := e.injective (by simpa using hz)
  exact congrArg Subtype.val h1

theorem sec127_exists_order_three [Finite G] {X : Subgroup G}
    (hX : Nonempty (↥X ≃* ↥(alternatingGroup (Fin 5)))) : ∃ x ∈ X, orderOf x = 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hd : 3 ∣ Nat.card ↥X := by rw [sec127_card_alt5 hX]; norm_num
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 3 hd
  refine ⟨x, x.2, ?_⟩
  rw [Subgroup.orderOf_coe]
  exact hx

theorem sec127_simple_dich {X Y : Subgroup G}
    (hX : Nonempty (↥X ≃* ↥(alternatingGroup (Fin 5)))) (hXY : X ≤ normalizer (Y : Set G)) :
    X ⊓ Y = ⊥ ∨ X ≤ Y := by
  obtain ⟨e⟩ := hX
  haveI : IsSimpleGroup ↥X := e.isSimpleGroup
  haveI : (Y.subgroupOf X).Normal :=
    ⟨fun n hn g => by
      rw [Subgroup.mem_subgroupOf] at hn ⊢
      have := (Subgroup.mem_normalizer_iff.mp (hXY g.2) n).mp hn
      simpa using this⟩
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Y.subgroupOf X) with h | h
  · left
    rw [eq_bot_iff]
    intro x hx
    have hx' : (⟨x, hx.1⟩ : ↥X) ∈ Y.subgroupOf X := Subgroup.mem_subgroupOf.mpr hx.2
    rw [h, Subgroup.mem_bot] at hx'
    exact Subgroup.mem_bot.mpr (congrArg Subtype.val hx')
  · right
    intro x hx
    have hx' : (⟨x, hx⟩ : ↥X) ∈ Y.subgroupOf X := by rw [h]; trivial
    exact Subgroup.mem_subgroupOf.mp hx'

theorem sec127_pow_mul {Q : Subgroup G} {s : G} (hs : s ∈ normalizer (Q : Set G)) {q : G}
    (hq : q ∈ Q) (m : ℕ) : ∃ q' ∈ Q, (q * s) ^ m = q' * s ^ m := by
  induction m with
  | zero => exact ⟨1, Q.one_mem, by simp⟩
  | succ m ih =>
    obtain ⟨q', hq', h⟩ := ih
    have hsm : s ^ m ∈ normalizer (Q : Set G) := (normalizer (Q : Set G)).pow_mem hs m
    have hc : s ^ m * q * (s ^ m)⁻¹ ∈ Q := (Subgroup.mem_normalizer_iff.mp hsm q).mp hq
    refine ⟨q' * (s ^ m * q * (s ^ m)⁻¹), Q.mul_mem hq' hc, ?_⟩
    rw [pow_succ, h]
    group

theorem sec127_mem_of_odd_orderOf {Q S : Subgroup G} (hS : IsPGroup 2 ↥S)
    (hSQ : S ≤ normalizer (Q : Set G)) {x : G} (hx : x ∈ Q ⊔ S) (hodd : Odd (orderOf x)) :
    x ∈ Q := by
  have hcoe := Subgroup.coe_mul_of_right_le_normalizer_left Q S hSQ
  have hx' : x ∈ ((Q : Set G) * (S : Set G)) := by
    rw [← hcoe]
    exact hx
  obtain ⟨q, hq, s, hs, hqs⟩ := Set.mem_mul.mp hx'
  subst hqs
  obtain ⟨k, hk⟩ := hS ⟨s, hs⟩
  have hsk : s ^ (2 ^ k) = 1 := congrArg Subtype.val hk
  obtain ⟨q', hq', hpow⟩ := sec127_pow_mul (hSQ hs) hq (2 ^ k)
  rw [hsk, mul_one] at hpow
  have hcop : Nat.Coprime (2 ^ k) (orderOf (q * s)) :=
    Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hodd)
  obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime hcop
  rw [← hm, hpow]
  exact Q.pow_mem hq' m

theorem sec127_le_of_alt5_sup [Finite G] {Q S X : Subgroup G} (hS : IsPGroup 2 ↥S)
    (hSQ : S ≤ normalizer (Q : Set G)) (hX : Nonempty (↥X ≃* ↥(alternatingGroup (Fin 5))))
    (hXQS : X ≤ Q ⊔ S) : X ≤ Q := by
  have hXN : X ≤ normalizer (Q : Set G) :=
    hXQS.trans (sup_le Subgroup.le_normalizer hSQ)
  rcases sec127_simple_dich hX hXN with h | h
  · exfalso
    obtain ⟨x, hxX, hx3⟩ := sec127_exists_order_three hX
    have hxQ : x ∈ Q :=
      sec127_mem_of_odd_orderOf hS hSQ (hXQS hxX) (by rw [hx3]; decide)
    have : x ∈ X ⊓ Q := Subgroup.mem_inf.mpr ⟨hxX, hxQ⟩
    rw [h, Subgroup.mem_bot] at this
    rw [this, orderOf_one] at hx3
    omega
  · exact h

end CFSG.OddStandard.SmallF3.Omega
