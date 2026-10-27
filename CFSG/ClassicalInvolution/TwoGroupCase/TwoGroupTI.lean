module

public import CFSG.ClassicalInvolution.TwoGroupCase.CommutingFamily
public import CFSG.ClassicalInvolution.TwoGroupCase.SylowOf

public section

namespace CFSG.ClassicalInvolution

open CFSG.Open
open scoped Pointwise

universe u

variable {G : Type u} [Group G]

structure TIPairData (X V A : Subgroup G) : Prop where
  two : IsPGroup 2 X
  le_V : V ≤ X
  le_A : A ≤ X
  exp_V : ∀ v ∈ V, v * v = 1
  exp_A : ∀ a ∈ A, a * a = 1
  inf_eq_bot : V ⊓ A = ⊥
  ti_V : ∀ x ∈ X, conjSubgroup x V = V ∨ V ⊓ conjSubgroup x V = ⊥
  ti_A : ∀ x ∈ X, conjSubgroup x A = A ∨ A ⊓ conjSubgroup x A = ⊥

namespace TIPairData

variable {X V A : Subgroup G} (d : TIPairData X V A)
include d

theorem symm : TIPairData X A V :=
  ⟨d.two, d.le_A, d.le_V, d.exp_A, d.exp_V, by rw [inf_comm]; exact d.inf_eq_bot, d.ti_A, d.ti_V⟩

theorem mem_normalizer_of_commute {v b : G} (hv : v ∈ V) (hb : b ∈ A) (hb1 : b ≠ 1)
    (hc : v * b = b * v) : v ∈ Subgroup.normalizer (A : Set G) := by
  rcases d.ti_A v (d.le_V hv) with h | h
  · exact conjSubgroup_eq_self_iff.mp h
  · exfalso
    apply hb1
    have hmem : b ∈ A ⊓ conjSubgroup v A := by
      refine ⟨hb, ?_⟩
      show b ∈ conjSubgroup v A
      rw [mem_conjSubgroup_iff]
      have : v⁻¹ * b * v = b := by rw [mul_assoc, ← hc, inv_mul_cancel_left]
      rw [this]
      exact hb
    rw [h, Subgroup.mem_bot] at hmem
    exact hmem

theorem commute_of_mem_normalizer {u b : G} (hu : u ∈ V ⊓ Subgroup.normalizer (A : Set G))
    (hb : b ∈ A ⊓ Subgroup.normalizer (V : Set G)) : u * b = b * u := by
  have h1 : u * b * u⁻¹ * b⁻¹ ∈ A :=
    A.mul_mem ((Subgroup.mem_normalizer_iff.mp hu.2 b).mp hb.1) (A.inv_mem hb.1)
  have h2 : u * b * u⁻¹ * b⁻¹ ∈ V := by
    have e : u * b * u⁻¹ * b⁻¹ = u * (b * u⁻¹ * b⁻¹) := by group
    rw [e]
    exact V.mul_mem hu.1 ((Subgroup.mem_normalizer_iff.mp hb.2 u⁻¹).mp (V.inv_mem hu.1))
  have h3 : u * b * u⁻¹ * b⁻¹ ∈ V ⊓ A := ⟨h2, h1⟩
  rw [d.inf_eq_bot, Subgroup.mem_bot] at h3
  have h4 : u * b * u⁻¹ = b := mul_inv_eq_one.mp h3
  calc u * b = (u * b * u⁻¹) * u := by group
    _ = b * u := by rw [h4]

theorem commutator_mem {v b : G} (hv : v ∈ V) (hb : b ∈ A ⊓ Subgroup.normalizer (V : Set G)) :
    v * b * v⁻¹ * b⁻¹ ∈ V ⊓ Subgroup.normalizer (A : Set G) := by
  have hwV : v * b * v⁻¹ * b⁻¹ ∈ V := by
    have e : v * b * v⁻¹ * b⁻¹ = v * (b * v⁻¹ * b⁻¹) := by group
    rw [e]
    exact V.mul_mem hv ((Subgroup.mem_normalizer_iff.mp hb.2 v⁻¹).mp (V.inv_mem hv))
  refine ⟨hwV, ?_⟩
  by_cases hb1 : b = 1
  · rw [hb1]
    have : v * 1 * v⁻¹ * (1 : G)⁻¹ = 1 := by group
    rw [this]
    exact Subgroup.one_mem _
  · have hb2 : b * b = 1 := d.exp_A b hb.1
    have hbinv : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb2
    have hw2 : (v * b * v⁻¹ * b⁻¹) * (v * b * v⁻¹ * b⁻¹) = 1 := d.exp_V _ hwV
    have hwinv : (v * b * v⁻¹ * b⁻¹)⁻¹ = v * b * v⁻¹ * b⁻¹ := inv_eq_of_mul_eq_one_right hw2
    have key : b * (v * b * v⁻¹ * b⁻¹) * b⁻¹ = (v * b * v⁻¹ * b⁻¹)⁻¹ := by
      calc b * (v * b * v⁻¹ * b⁻¹) * b⁻¹ = b * v * b * v⁻¹ * (b⁻¹ * b⁻¹) := by group
        _ = b * v * b * v⁻¹ := by rw [hbinv, hb2, mul_one]
        _ = b * v * b⁻¹ * v⁻¹ := by rw [hbinv]
        _ = (v * b * v⁻¹ * b⁻¹)⁻¹ := by group
    rw [hwinv] at key
    have hcomm : (v * b * v⁻¹ * b⁻¹) * b = b * (v * b * v⁻¹ * b⁻¹) := by
      have := key
      rw [mul_inv_eq_iff_eq_mul] at this
      exact this.symm
    exact d.mem_normalizer_of_commute hwV hb.1 hb1 hcomm

theorem card_le_of_le_normalizer [Finite G] (hA : A ≤ Subgroup.normalizer (V : Set G)) {v : G}
    (hv : v ∈ V) (hvn : v ∉ Subgroup.normalizer (A : Set G)) :
    Nat.card A ≤ Nat.card (V ⊓ Subgroup.normalizer (A : Set G) : Subgroup G) := by
  let f : A → (V ⊓ Subgroup.normalizer (A : Set G) : Subgroup G) := fun a =>
    ⟨v * a * v⁻¹ * (a : G)⁻¹, d.commutator_mem hv ⟨a.2, hA a.2⟩⟩
  have hf : Function.Injective f := by
    intro a a' haa
    have heq : v * (a : G) * v⁻¹ * (a : G)⁻¹ = v * (a' : G) * v⁻¹ * (a' : G)⁻¹ :=
      congrArg Subtype.val haa
    have h1 : (a : G) * v⁻¹ * (a : G)⁻¹ = (a' : G) * v⁻¹ * (a' : G)⁻¹ := by
      have e1 : v * (a : G) * v⁻¹ * (a : G)⁻¹ = v * ((a : G) * v⁻¹ * (a : G)⁻¹) := by group
      have e2 : v * (a' : G) * v⁻¹ * (a' : G)⁻¹ = v * ((a' : G) * v⁻¹ * (a' : G)⁻¹) := by group
      rw [e1, e2] at heq
      exact mul_left_cancel heq
    have h2 : ((a' : G)⁻¹ * a) * v⁻¹ = v⁻¹ * ((a' : G)⁻¹ * a) := by
      calc ((a' : G)⁻¹ * a) * v⁻¹ = (a' : G)⁻¹ * ((a : G) * v⁻¹ * (a : G)⁻¹) * a := by group
        _ = (a' : G)⁻¹ * ((a' : G) * v⁻¹ * (a' : G)⁻¹) * a := by rw [h1]
        _ = v⁻¹ * ((a' : G)⁻¹ * a) := by group
    have h3 : v * ((a' : G)⁻¹ * a) = ((a' : G)⁻¹ * a) * v := by
      calc v * ((a' : G)⁻¹ * a) = v * (((a' : G)⁻¹ * a) * v⁻¹) * v := by group
        _ = v * (v⁻¹ * ((a' : G)⁻¹ * a)) * v := by rw [h2]
        _ = ((a' : G)⁻¹ * a) * v := by group
    by_contra hne
    have hc1 : (a' : G)⁻¹ * a ≠ 1 := fun h => hne (Subtype.ext (inv_mul_eq_one.mp h).symm)
    exact hvn (d.mem_normalizer_of_commute hv (A.mul_mem (A.inv_mem a'.2) a.2) hc1 h3)
  exact Nat.card_le_card_of_injective f hf

theorem le_normalizer_of_le_normalizer [Finite G] (hA : A ≤ Subgroup.normalizer (V : Set G))
    (hcard : Nat.card V = Nat.card A) : V ≤ Subgroup.normalizer (A : Set G) := by
  by_contra hV
  obtain ⟨v, hv, hvn⟩ := IsConcreteLE.not_le_iff_exists.mp hV
  have h1 := d.card_le_of_le_normalizer hA hv hvn
  have h2 : Nat.card (V ⊓ Subgroup.normalizer (A : Set G) : Subgroup G) ≤ Nat.card V :=
    Subgroup.card_le_of_le inf_le_left
  have h3 : V ⊓ Subgroup.normalizer (A : Set G) ≠ V := fun h => by
    have hvU : v ∈ V ⊓ Subgroup.normalizer (A : Set G) := by
      rw [h]
      exact hv
    exact hvn hvU.2
  have h4 : Nat.card (V ⊓ Subgroup.normalizer (A : Set G) : Subgroup G) ≠ Nat.card V := fun h =>
    h3 (Subgroup.eq_of_le_of_card_ge inf_le_left h.ge)
  omega

theorem exists_mul_of_mem_sup {y : G}
    (hy : y ∈ (V ⊓ Subgroup.normalizer (A : Set G)) ⊔ (A ⊓ Subgroup.normalizer (V : Set G))) :
    ∃ u ∈ V ⊓ Subgroup.normalizer (A : Set G), ∃ b ∈ A ⊓ Subgroup.normalizer (V : Set G),
      y = u * b := by
  have hBn : (A ⊓ Subgroup.normalizer (V : Set G)) ≤
      Subgroup.normalizer ((V ⊓ Subgroup.normalizer (A : Set G) : Subgroup G) : Set G) := by
    refine le_trans (fun b hb => ?_) (Subgroup.centralizer_le_normalizer _)
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    exact d.commute_of_mem_normalizer hu hb
  have hmul := Subgroup.coe_mul_of_right_le_normalizer_left (V ⊓ Subgroup.normalizer (A : Set G))
    (A ⊓ Subgroup.normalizer (V : Set G)) hBn
  have hy' : y ∈ (((V ⊓ Subgroup.normalizer (A : Set G)) ⊔
      (A ⊓ Subgroup.normalizer (V : Set G)) : Subgroup G) : Set G) := hy
  rw [hmul] at hy'
  obtain ⟨u, hu, b, hb, rfl⟩ := hy'
  exact ⟨u, hu, b, hb, rfl⟩

theorem conj_mem_sup {v y : G} (hv : v ∈ V)
    (hy : y ∈ (V ⊓ Subgroup.normalizer (A : Set G)) ⊔ (A ⊓ Subgroup.normalizer (V : Set G))) :
    v * y * v⁻¹ ∈
      (V ⊓ Subgroup.normalizer (A : Set G)) ⊔ (A ⊓ Subgroup.normalizer (V : Set G)) := by
  obtain ⟨u, hu, b, hb, rfl⟩ := d.exists_mul_of_mem_sup hy
  have hvu : v * u = u * v :=
    commute_of_mul_self_eq_one (d.exp_V v hv) (d.exp_V u hu.1) (d.exp_V (v * u) (V.mul_mem hv hu.1))
  have hw := d.commutator_mem hv hb
  have e : v * (u * b) * v⁻¹ = (u * (v * b * v⁻¹ * b⁻¹)) * b := by
    calc v * (u * b) * v⁻¹ = (v * u) * b * v⁻¹ := by group
      _ = (u * v) * b * v⁻¹ := by rw [hvu]
      _ = (u * (v * b * v⁻¹ * b⁻¹)) * b := by group
  rw [e]
  exact Subgroup.mul_mem_sup (Subgroup.mul_mem _ hu hw) hb

theorem false_of_not_le_normalizer [Finite G] (hU : V ⊓ Subgroup.normalizer (A : Set G) ≠ ⊥)
    (hV : ¬ V ≤ Subgroup.normalizer (A : Set G)) (hA : ¬ A ≤ Subgroup.normalizer (V : Set G)) :
    False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨v₀, hv₀, hv₀n⟩ := IsConcreteLE.not_le_iff_exists.mp hV
  obtain ⟨a₀, ha₀, ha₀n⟩ := IsConcreteLE.not_le_iff_exists.mp hA
  set Y : Subgroup G :=
    (V ⊓ Subgroup.normalizer (A : Set G)) ⊔ (A ⊓ Subgroup.normalizer (V : Set G)) with hY
  set X₀ : Subgroup G := V ⊔ A with hX₀
  have hVX₀ : V ≤ X₀ := le_sup_left
  have hAX₀ : A ≤ X₀ := le_sup_right
  have hYX₀ : Y ≤ X₀ := sup_le (inf_le_left.trans hVX₀) (inf_le_left.trans hAX₀)
  have hX₀2 : IsPGroup 2 X₀ := d.two.to_le (sup_le d.le_V d.le_A)
  have hYV : V ≤ Subgroup.normalizer (Y : Set G) :=
    le_normalizer_of_conj_mem fun v hv y hy => d.conj_mem_sup hv hy
  have hYA : A ≤ Subgroup.normalizer (Y : Set G) := by
    refine le_normalizer_of_conj_mem fun a ha y hy => ?_
    have hy' : y ∈
        (A ⊓ Subgroup.normalizer (V : Set G)) ⊔ (V ⊓ Subgroup.normalizer (A : Set G)) := by
      rwa [hY, sup_comm] at hy
    have := d.symm.conj_mem_sup ha hy'
    rwa [sup_comm] at this
  have hX₀n : X₀ ≤ Subgroup.normalizer (Y : Set G) := sup_le hYV hYA
  have : Group.IsNilpotent X₀ := hX₀2.isNilpotent
  have : (Y.subgroupOf X₀).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hYX₀).mpr hX₀n
  have hYne : Y.subgroupOf X₀ ≠ ⊥ := by
    intro h
    obtain ⟨u, hu1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hU
    have huY : (u : G) ∈ Y := Subgroup.mem_sup_left u.2
    have hmem : (⟨(u : G), hYX₀ huY⟩ : X₀) ∈ Y.subgroupOf X₀ := huY
    rw [h, Subgroup.mem_bot] at hmem
    have hval : (u : G) = 1 := congrArg Subtype.val hmem
    exact hu1 (Subtype.ext hval)
  obtain ⟨z', hz'⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp
    (Group.IsNilpotent.inf_center_ne_bot_of_normal hYne)
  have hzY : ((z' : X₀) : G) ∈ Y := z'.2.1
  have hz1 : ((z' : X₀) : G) ≠ 1 := fun h => hz' (Subtype.ext (Subtype.ext h))
  have hzc : ∀ x ∈ X₀, x * ((z' : X₀) : G) = ((z' : X₀) : G) * x := by
    intro x hx
    have := Subgroup.mem_center_iff.mp z'.2.2 ⟨x, hx⟩
    exact congrArg Subtype.val this
  obtain ⟨u, hu, b, hb, hzub⟩ := d.exists_mul_of_mem_sup hzY
  have hvu : v₀ * u = u * v₀ :=
    commute_of_mul_self_eq_one (d.exp_V v₀ hv₀) (d.exp_V u hu.1)
      (d.exp_V (v₀ * u) (V.mul_mem hv₀ hu.1))
  have hb1 : b = 1 := by
    by_contra hb1
    have h1 := hzc v₀ (hVX₀ hv₀)
    rw [hzub] at h1
    have h2 : v₀ * b = b * v₀ := by
      have : u * (v₀ * b) = u * (b * v₀) := by
        calc u * (v₀ * b) = (u * v₀) * b := by rw [mul_assoc]
          _ = (v₀ * u) * b := by rw [hvu]
          _ = v₀ * (u * b) := by rw [mul_assoc]
          _ = (u * b) * v₀ := h1
          _ = u * (b * v₀) := by rw [mul_assoc]
      exact mul_left_cancel this
    exact hv₀n (d.mem_normalizer_of_commute hv₀ hb.1 hb1 h2)
  have hu1 : u = 1 := by
    by_contra hu1
    have h1 := hzc a₀ (hAX₀ ha₀)
    rw [hzub, hb1, mul_one] at h1
    exact ha₀n (d.symm.mem_normalizer_of_commute ha₀ hu.1 hu1 h1)
  rw [hzub, hb1, hu1, mul_one] at hz1
  exact hz1 rfl

theorem commute [Finite G] (hcard : Nat.card V = Nat.card A)
    (hU : V ⊓ Subgroup.normalizer (A : Set G) ≠ ⊥) : ∀ v ∈ V, ∀ a ∈ A, v * a = a * v := by
  have hboth : V ≤ Subgroup.normalizer (A : Set G) ∧ A ≤ Subgroup.normalizer (V : Set G) := by
    by_cases hA : A ≤ Subgroup.normalizer (V : Set G)
    · exact ⟨d.le_normalizer_of_le_normalizer hA hcard, hA⟩
    · by_cases hV : V ≤ Subgroup.normalizer (A : Set G)
      · exact ⟨hV, d.symm.le_normalizer_of_le_normalizer hV hcard.symm⟩
      · exact (d.false_of_not_le_normalizer hU hV hA).elim
  intro v hv a ha
  have h1 : v * a * v⁻¹ * a⁻¹ ∈ A :=
    A.mul_mem ((Subgroup.mem_normalizer_iff.mp (hboth.1 hv) a).mp ha) (A.inv_mem ha)
  have h2 : v * a * v⁻¹ * a⁻¹ ∈ V := by
    have e : v * a * v⁻¹ * a⁻¹ = v * (a * v⁻¹ * a⁻¹) := by group
    rw [e]
    exact V.mul_mem hv ((Subgroup.mem_normalizer_iff.mp (hboth.2 ha) v⁻¹).mp (V.inv_mem hv))
  have h3 : v * a * v⁻¹ * a⁻¹ ∈ V ⊓ A := ⟨h2, h1⟩
  rw [d.inf_eq_bot, Subgroup.mem_bot] at h3
  have h4 : v * a * v⁻¹ = a := mul_inv_eq_one.mp h3
  calc v * a = (v * a * v⁻¹) * v := by group
    _ = a * v := by rw [h4]

end TIPairData

theorem twoGroupTIInput : TwoGroupTIInput.{u} := by
  intro G _ _ X V A hX hVX hAX hV hA hcard hVA hTIV hTIA _ hU v hv a ha
  exact (TIPairData.mk hX hVX hAX hV hA hVA hTIV hTIA).commute hcard hU v hv a ha

namespace TightData

variable [Finite G] {K H Q S : Subgroup G} (d : TightData K H Q S)
include d

theorem commute_of_inf_normalizer_ne_bot {g : G} (hg : g ∈ H) (hne : conjSubgroup g Q ≠ Q)
    (hgS : conjSubgroup g Q ≤ S)
    (hN : conjSubgroup g Q ⊓ Subgroup.normalizer (Q : Set G) ≠ ⊥) :
    Q ⊓ conjSubgroup g Q = ⊥ ∧ ∀ x ∈ Q, ∀ y ∈ conjSubgroup g Q, x * y = y * x :=
  d.commute_of_normalizer_ne_bot twoGroupTIInput hg hne hgS hN

end TightData

end CFSG.ClassicalInvolution
