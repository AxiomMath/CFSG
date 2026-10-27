module

public import CFSG.CharacterTheory.Semidihedral.Local.TransferCosetOrbit
public import Mathlib.GroupTheory.IsPerfect

public section

namespace CFSG.OddStandard

open Subgroup CFSG.Semidihedral.Local

variable {G : Type*} [Group G]

theorem exists_iterate_orbit_reps {α : Type*} [Finite α] (f : α → α)
    (hf : Function.Injective f) :
    ∃ R : Finset α, ∀ a, ∃! a₀, a₀ ∈ R ∧ ∃ k : ℕ, f^[k] a₀ = a := by
  classical
  have hpos : ∀ a, 0 < Function.minimalPeriod f a := fun a =>
    Function.minimalPeriod_pos_of_mem_periodicPts (hf.mem_periodicPts a)
  let s : Setoid α :=
    { r := fun a b => ∃ k : ℕ, f^[k] a = b
      iseqv := ⟨fun _ => ⟨0, rfl⟩, fun {a b} ⟨k, hk⟩ => ⟨k * Function.minimalPeriod f a - k, by
          rw [← hk, ← Function.iterate_add_apply,
            Nat.sub_add_cancel (Nat.le_mul_of_pos_right k (hpos a)), mul_comm]
          exact ((Function.isPeriodicPt_minimalPeriod f a).mul_const k).eq⟩,
        fun {a b c} ⟨k, hk⟩ ⟨l, hl⟩ => ⟨l + k, by rw [Function.iterate_add_apply, hk, hl]⟩⟩ }
  let := Fintype.ofFinite α
  refine ⟨Finset.univ.image fun a => (Quotient.mk s a).out, fun a =>
    ⟨(Quotient.mk s a).out, ⟨Finset.mem_image_of_mem _ (Finset.mem_univ a), Quotient.mk_out a⟩,
      ?_⟩⟩
  rintro a₁ ⟨ha₁, k, hk⟩
  obtain ⟨b, -, rfl⟩ := Finset.mem_image.mp ha₁
  have h1 : Quotient.mk s (Quotient.mk s b).out = Quotient.mk s a := Quotient.sound ⟨k, hk⟩
  rw [Quotient.out_eq] at h1
  rw [h1]

theorem transfer_fusion_contradiction [Finite G] [Group.IsPerfect G] {Q : Subgroup G}
    (hQ : ¬ 2 ∣ Q.index) {s : G} (hsQ : s ∈ Q) {a : ℕ} (hs : orderOf s = 2 ^ a)
    (ψ : Q →* Multiplicative (ZMod 2))
    (hψ : ∀ (g : G) (b : ℕ), b ≤ a → ∀ hy : g * s ^ 2 ^ b * g⁻¹ ∈ Q,
      ψ ⟨g * s ^ 2 ^ b * g⁻¹, hy⟩ = if b = 0 then Multiplicative.ofAdd 1 else 1) : False := by
  classical
  have _ := hsQ
  let := Fintype.ofFinite (Quotient (QuotientGroup.rightRel Q))
  set f := rightCosetMul Q s with hf
  obtain ⟨R, hR⟩ := exists_iterate_orbit_reps f (rightCosetMul_injective Q s)
  have hdvd : ∀ C, Function.minimalPeriod f C ∣ 2 ^ a := by
    intro C
    refine Function.IsPeriodicPt.minimalPeriod_dvd ?_
    induction C using Quotient.inductionOn with
    | h c =>
      change f^[2 ^ a] (Quotient.mk _ c) = Quotient.mk _ c
      rw [hf, rightCosetMul_iterate_mk, ← hs, pow_orderOf_eq_one, mul_one]
  have key : ∀ (c : G) (r : ℕ), r ∣ 2 ^ a → ∀ h : c * s ^ r * c⁻¹ ∈ Q,
      ψ ⟨c * s ^ r * c⁻¹, h⟩ = Multiplicative.ofAdd ((r : ℕ) : ZMod 2) := by
    intro c r hr h
    obtain ⟨b, hb, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hr
    rw [hψ c b hb h]
    rcases Nat.eq_zero_or_pos b with rfl | hb0
    · simp
    · rw [ite_eq_right hb0.ne']
      have h2 : ((2 ^ b : ℕ) : ZMod 2) = 0 := by
        rw [Nat.cast_pow, show ((2 : ℕ) : ZMod 2) = 0 from rfl, zero_pow hb0.ne']
      rw [h2, ofAdd_zero]
  have htr : ψ.transfer s = Multiplicative.ofAdd ((Q.index : ℕ) : ZMod 2) := by
    rw [transfer_eq_prod_orbit Q ψ s R hR (fun C => C.out) (fun C _ => Quotient.out_eq C),
      ← sum_minimalPeriod_eq_index Q s R hR, Nat.cast_sum, ofAdd_sum, ← Finset.prod_coe_sort R]
    exact Fintype.prod_congr _ _ fun C => key _ _ (hdvd C) _
  have hodd : ((Q.index : ℕ) : ZMod 2) = 1 := by
    rw [ZMod.natCast_eq_one_iff_odd, Nat.odd_iff]
    omega
  have h1 : ψ.transfer s = 1 :=
    Abelianization.commutator_subset_ker ψ.transfer Group.IsPerfect.mem_commutator
  rw [htr, hodd] at h1
  exact absurd h1 (by decide)

end CFSG.OddStandard
