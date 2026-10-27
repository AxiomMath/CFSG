module

public import Mathlib.GroupTheory.PGroup

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open Subgroup

variable {G : Type*} [Group G] {p : ℕ}

theorem inf_centralizer_eq_bot_of_normalizer_not_le {M H S B : Subgroup G}
    (hNS : ¬ normalizer (S : Set G) ≤ M)
    (hNSB : normalizer (S : Set G) ≤ normalizer (B : Set G))
    (hCB : H ⊓ centralizer (B : Set G) ≠ ⊥ → normalizer (B : Set G) ≤ M) :
    H ⊓ centralizer (B : Set G) = ⊥ := by
  by_contra h
  exact hNS (hNSB.trans (hCB h))

theorem inf_centralizer_singleton_eq_bot_of_inf_centralizer_eq_bot
    {H S B Z : Subgroup G} (hp : p.Prime) (hS : IsPGroup p S) (hZS : Z ≤ S)
    (hB : Nat.card B = p) (hOmega : {x ∈ (Z : Set G) | x ^ p = 1} = (B : Set G))
    (hCB : H ⊓ centralizer (B : Set G) = ⊥) {z : G} (hz : z ∈ Z) (hz1 : z ≠ 1) :
    H ⊓ centralizer ({z} : Set G) = ⊥ := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨k, hk⟩ := (hS.to_le hZS).exists_orderOf_eq_pow (⟨z, hz⟩ : Z)
  have hk' : orderOf z = p ^ k := (Subgroup.orderOf_coe (⟨z, hz⟩ : Z)).trans hk
  have hk1 : k ≠ 0 := by
    rintro rfl
    rw [pow_zero, orderOf_eq_one_iff] at hk'
    exact hz1 hk'
  set w : G := z ^ p ^ (k - 1) with hw
  have hwZ : w ∈ Z := Z.pow_mem hz _
  have hwp : w ^ p = 1 := by
    rw [hw, ← pow_mul, ← pow_succ, Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hk1), ← hk',
      pow_orderOf_eq_one]
  have hwB : w ∈ B := by
    have hmem : w ∈ ({x ∈ (Z : Set G) | x ^ p = 1}) := ⟨hwZ, hwp⟩
    rwa [hOmega] at hmem
  have hw1 : w ≠ 1 := by
    intro h
    rw [hw, ← orderOf_dvd_iff_pow_eq_one, hk'] at h
    have := (Nat.pow_dvd_pow_iff_le_right hp.one_lt).mp h
    omega
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨hxH, hxz⟩ := hx
  have hzx : Commute z x := (Subgroup.mem_centralizer_singleton_iff.mp hxz).symm
  have hwx : Commute w x := hzx.pow_left _
  have hxB : x ∈ centralizer (B : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    have : Fact (Nat.card B).Prime := ⟨hB ▸ hp⟩
    obtain ⟨m, hm⟩ : (⟨b, hb⟩ : B) ∈ Subgroup.zpowers (⟨w, hwB⟩ : B) :=
      mem_zpowers_of_prime_card rfl (by simpa [Subtype.ext_iff] using hw1)
    have hb' : b = w ^ m := by
      have := congrArg Subtype.val hm
      simpa using this.symm
    rw [hb']
    exact (hwx.zpow_left m).eq
  have hfin : x ∈ H ⊓ centralizer (B : Set G) := ⟨hxH, hxB⟩
  rw [hCB] at hfin
  simpa using hfin

theorem inf_centralizer_singleton_eq_bot_of_normalizer_not_le
    {M H S B Z : Subgroup G} (hp : p.Prime) (hS : IsPGroup p S) (hB : Nat.card B = p)
    (hNS : ¬ normalizer (S : Set G) ≤ M)
    (hNSB : normalizer (S : Set G) ≤ normalizer (B : Set G))
    (hCB : H ⊓ centralizer (B : Set G) ≠ ⊥ → normalizer (B : Set G) ≤ M)
    (hZS : Z ≤ S) [IsCyclic Z] [Nontrivial Z]
    (hOmega : {x ∈ (Z : Set G) | x ^ p = 1} = (B : Set G)) :
    ∀ z ∈ Z, z ≠ 1 → H ⊓ centralizer ({z} : Set G) = ⊥ := fun _z hz hz1 =>
  inf_centralizer_singleton_eq_bot_of_inf_centralizer_eq_bot hp hS hZS hB hOmega
    (inf_centralizer_eq_bot_of_normalizer_not_le hNS hNSB hCB) hz hz1

end CFSG.FeitThompson
