module

public import Mathlib.GroupTheory.PGroup
public import Mathlib.GroupTheory.SpecificGroups.Alternating

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open Subgroup
open scoped commutatorElement

@[expose] def OddThree (P : Type) [Group P] : Prop :=
  ∃ T : Subgroup P, T.Normal ∧ Nat.card ↥T = 3 ∧ ∀ y : P, Odd (orderOf y) → y ∈ T

theorem oddThree_mulZMod3 : OddThree (Multiplicative (ZMod 3)) := by
  refine ⟨⊤, inferInstance, ?_, fun _ _ => Subgroup.mem_top _⟩
  rw [Subgroup.card_top, Nat.card_eq_fintype_card]
  decide

theorem oddThree_perm3 : OddThree (Equiv.Perm (Fin 3)) := by
  refine ⟨alternatingGroup (Fin 3), inferInstance, ?_, ?_⟩
  · rw [Nat.card_eq_fintype_card]
    decide
  · intro y hy
    rw [Equiv.Perm.mem_alternatingGroup]
    obtain ⟨k, hk⟩ := hy
    have h1 : Equiv.Perm.sign y ^ orderOf y = 1 := by
      rw [← map_pow, pow_orderOf_eq_one, map_one]
    rw [hk, pow_succ, pow_mul, Int.units_pow_two, one_pow, one_mul] at h1
    exact h1

theorem odd_orderOf_of_isPGroup {D : Type} [Group D] {p : ℕ} (hp : p.Prime) (hodd : p ≠ 2)
    {X : Subgroup D} (hX : IsPGroup p ↥X) {x : D} (hx : x ∈ X) : Odd (orderOf x) := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hX) ⟨x, hx⟩
  rw [Subgroup.orderOf_mk] at hk
  rw [hk]
  exact (hp.odd_of_ne_two hodd).pow

theorem orderOf_eq_two_pow_of_isPGroup {D : Type} [Group D] {W : Subgroup D} (hW : IsPGroup 2 ↥W)
    {w : D} (hw : w ∈ W) : ∃ k : ℕ, orderOf w = 2 ^ k := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hW) ⟨w, hw⟩
  rw [Subgroup.orderOf_mk] at hk
  exact ⟨k, hk⟩

theorem two_p_image_of_oddThree {D P : Type} [Group D] [Group P] (hP : OddThree P) (φ : D →* P)
    {p : ℕ} (hp : p.Prime) (hodd : p ≠ 2) {W₁ X₁ : Subgroup D}
    (hW : IsPGroup 2 ↥W₁) (hX : IsPGroup p ↥X₁) (hWX : ⁅W₁, X₁⁆ = W₁) :
    W₁ ≤ φ.ker ∧ (φ.ker.subgroupOf X₁).index ∣ 3 := by
  obtain ⟨T, hTn, hT3, hTodd⟩ := hP
  set N₃ : Subgroup D := T.comap φ with hN₃
  have : N₃.Normal := hTn.comap φ
  have hXT : ∀ x ∈ X₁, φ x ∈ T := by
    intro x hx
    apply hTodd
    have hd : orderOf (φ x) ∣ orderOf x := orderOf_map_dvd φ x
    exact (odd_orderOf_of_isPGroup hp hodd hX hx).of_dvd_nat hd
  have hXN : X₁ ≤ N₃ := fun x hx => hXT x hx
  have hWN : W₁ ≤ N₃ := by
    rw [← hWX, Subgroup.commutator_le]
    intro w hw x hx
    have h1 : w * x * w⁻¹ ∈ N₃ := (inferInstance : N₃.Normal).conj_mem x (hXN hx) w
    exact N₃.mul_mem h1 (N₃.inv_mem (hXN hx))
  have hW1 : W₁ ≤ φ.ker := by
    intro w hw
    rw [MonoidHom.mem_ker]
    have hwT : φ w ∈ T := hWN hw
    obtain ⟨k, hk⟩ := orderOf_eq_two_pow_of_isPGroup hW hw
    have hd : orderOf (φ w) ∣ 2 ^ k := hk ▸ orderOf_map_dvd φ w
    have hd3 : orderOf (φ w) ∣ 3 := by
      have : orderOf (⟨φ w, hwT⟩ : T) ∣ Nat.card T := orderOf_dvd_natCard _
      rw [hT3, Subgroup.orderOf_mk] at this
      exact this
    have hcop : Nat.Coprime (2 ^ k) 3 := Nat.Coprime.pow_left k (by norm_num)
    have : orderOf (φ w) = 1 := Nat.eq_one_of_dvd_coprimes hcop hd hd3
    exact orderOf_eq_one_iff.mp this
  refine ⟨hW1, ?_⟩
  have hker : φ.ker.subgroupOf X₁ = (φ.comp X₁.subtype).ker := rfl
  rw [hker, Subgroup.index_ker]
  have hrange : (φ.comp X₁.subtype).range ≤ T := by
    rintro _ ⟨x, rfl⟩
    exact hXT x x.2
  rw [← hT3]
  exact Subgroup.card_dvd_of_le hrange

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
