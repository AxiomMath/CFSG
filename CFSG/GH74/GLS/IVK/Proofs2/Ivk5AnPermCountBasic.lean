module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk5AnPermDefs
public import Mathlib.GroupTheory.Perm.Centralizer
public import Mathlib.GroupTheory.SpecificGroups.Alternating

public section

namespace CFSG.GH74.GLS.IVK.Proofs2.Ivk5An

open Equiv Equiv.Perm Nat

private theorem cycleType_of_sq_card {α : Type*} [Fintype α] [DecidableEq α] {σ : Perm α}
    (h : σ ^ 2 = 1) (k : ℕ) (hs : σ.support.card = 2 * k) :
    σ.cycleType = Multiset.replicate k 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 := Perm.cycleType_of_pow_prime_eq_one h
  have h2 := Perm.sum_cycleType σ
  rw [h1, Multiset.sum_replicate, smul_eq_mul, hs] at h2
  rw [h1]
  congr 1
  omega

theorem card_eq_two_mul_card_inf_alt {α : Type*} [Fintype α] [DecidableEq α]
    (C : Subgroup (Perm α)) {ρ : Perm α} (hρC : ρ ∈ C) (hρ : Perm.sign ρ = -1) :
    Nat.card C = 2 * Nat.card ↥(C ⊓ alternatingGroup α) := by
  have hidx : ((alternatingGroup α).subgroupOf C).index = 2 := by
    rw [Subgroup.index_eq_two_iff]
    refine ⟨⟨ρ, hρC⟩, fun b => ?_⟩
    simp only [Subgroup.mem_subgroupOf, Perm.mem_alternatingGroup, Subgroup.coe_mul, map_mul, hρ]
    rcases Int.units_eq_one_or (Perm.sign (b : Perm α)) with h | h <;> simp [h]
  have h1 := Subgroup.card_mul_index ((alternatingGroup α).subgroupOf C)
  rw [hidx] at h1
  have h2 : Nat.card ↥(C ⊓ alternatingGroup α) = Nat.card ((alternatingGroup α).subgroupOf C) :=
    Nat.card_congr
      { toFun := fun x => ⟨⟨x.1, x.2.1⟩, x.2.2⟩
        invFun := fun y => ⟨y.1.1, y.1.2, y.2⟩
        left_inv := fun x => rfl
        right_inv := fun y => rfl }
  omega

section Count

variable (m : ℕ) (h7 : 7 ≤ m) (h10 : m ≤ 10)

include h7 h10

theorem ct_tb' : (tb m).cycleType = {2, 2, 2, 2} :=
  cycleType_of_sq_card (σ := tb m) (by interval_cases m <;> decide) 4
    (by interval_cases m <;> decide)

theorem card_centralizer_tb :
    Nat.card ↥(Subgroup.centralizer ({tb m} : Set (Perm (Fin (m + 1))))) = 384 * (m - 7)! := by
  rw [Equiv.Perm.nat_card_centralizer, ct_tb' m h7 h10]
  have e1 : ({2, 2, 2, 2} : Multiset ℕ).sum = 8 := by decide
  have e2 : ({2, 2, 2, 2} : Multiset ℕ).prod = 16 := by decide
  have e3 : ∏ n ∈ ({2, 2, 2, 2} : Multiset ℕ).toFinset, (({2, 2, 2, 2} : Multiset ℕ).count n)! =
      24 := by decide
  have hsum : (m + 1) - 8 = m - 7 := by omega
  rw [e1, e2, e3, Fintype.card_fin, hsum]
  ring

theorem sw_mem_centralizer_tb :
    sw m 0 1 ∈ Subgroup.centralizer ({tb m} : Set (Perm (Fin (m + 1)))) := by
  rw [Subgroup.mem_centralizer_singleton_iff]
  interval_cases m <;> decide

theorem sign_sw01 : Perm.sign (sw m 0 1) = -1 := by
  have hne : Fin.ofNat (m + 1) 0 ≠ Fin.ofNat (m + 1) 1 := by
    interval_cases m <;> decide
  exact Perm.sign_swap hne

theorem card_centralizer_tb_alt :
    Nat.card ↥(Subgroup.centralizer ({tb m} : Set (Perm (Fin (m + 1)))) ⊓
      alternatingGroup (Fin (m + 1))) = 192 * (m - 7)! := by
  have h := card_eq_two_mul_card_inf_alt
    (Subgroup.centralizer ({tb m} : Set (Perm (Fin (m + 1))))) (sw_mem_centralizer_tb m h7 h10)
    (sign_sw01 m h7 h10)
  rw [card_centralizer_tb m h7 h10] at h
  omega

theorem exists_conj_tb (σ : Perm (Fin (m + 1))) (hσ : σ.cycleType = {2, 2, 2, 2}) :
    ∃ g ∈ alternatingGroup (Fin (m + 1)), g * σ * g⁻¹ = tb m := by
  obtain ⟨c, hc⟩ := isConj_iff.mp
    (isConj_iff_cycleType_eq.mpr (hσ.trans (ct_tb' m h7 h10).symm))
  rcases Int.units_eq_one_or (Perm.sign c) with h | h
  · exact ⟨c, Perm.mem_alternatingGroup.mpr h, hc⟩
  · refine ⟨sw m 0 1 * c, ?_, ?_⟩
    · rw [Perm.mem_alternatingGroup, map_mul, h, sign_sw01 m h7 h10]
      rfl
    · have hs := Subgroup.mem_centralizer_singleton_iff.mp (sw_mem_centralizer_tb m h7 h10)
      calc sw m 0 1 * c * σ * (sw m 0 1 * c)⁻¹
          = sw m 0 1 * (c * σ * c⁻¹) * (sw m 0 1)⁻¹ := by group
        _ = tb m := by
          rw [hc, mul_inv_eq_iff_eq_mul]
          exact hs

end Count

end CFSG.GH74.GLS.IVK.Proofs2.Ivk5An
