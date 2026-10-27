module

public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.Tactic.Group

public section

namespace CFSG.EvenSporadicStandard.Induction

open Subgroup

theorem exists_involution_of_inner {L : Type} [Group L] [Finite L]
    (hodd : Odd (Nat.card (center L))) {σ : MulAut L} (hσ1 : σ ≠ 1) (hσ2 : σ * σ = 1) {l : L}
    (hl : σ = MulAut.conj l) : ∃ l' : L, orderOf l' = 2 ∧ σ = MulAut.conj l' := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hzc : l * l ∈ center L := by
    have h3 : MulAut.conj (l * l) = (1 : MulAut L) := by
      rw [map_mul, ← hl]
      exact hσ2
    rw [Subgroup.mem_center_iff]
    intro g
    have h4 := congrArg (fun f : MulAut L => f g) h3
    simp only [MulAut.conj_apply, MulAut.one_apply] at h4
    calc g * (l * l) = (l * l * g * (l * l)⁻¹) * (l * l) := by rw [h4]
      _ = l * l * g := by group
  set m := orderOf (l * l) with hm
  have hmodd : Odd m := by
    have h1 : orderOf (⟨l * l, hzc⟩ : ↥(center L)) = m := by
      rw [← Subgroup.orderOf_coe]
    exact hodd.of_dvd_nat (h1 ▸ orderOf_dvd_natCard _)
  have hsq : (l ^ m) ^ 2 = 1 := by
    rw [← pow_mul, mul_comm, pow_mul, pow_two]
    exact pow_orderOf_eq_one (l * l)
  have hconj : MulAut.conj (l ^ m) = σ := by
    rw [map_pow, ← hl]
    obtain ⟨k, hk⟩ := hmodd
    have hσ : σ ^ 2 = 1 := by rw [pow_two]; exact hσ2
    rw [hk, pow_succ, pow_mul, hσ, one_pow, one_mul]
  have hne : l ^ m ≠ 1 := by
    intro h1
    apply hσ1
    rw [← hconj, h1, map_one]
  exact ⟨l ^ m, orderOf_eq_prime hsq hne, hconj.symm⟩

end CFSG.EvenSporadicStandard.Induction
