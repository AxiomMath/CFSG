module

public import CFSG.GH74.GLS.Basic
public import CFSG.GroupTheory.QuasisimpleCenterDivisibility
public import CFSG.GroupTheory.LocalCores.Components

public section

namespace CFSG.SecondGeneration

open Subgroup
open CFSG.GH74.GLS (oPrimeResidual)

variable {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]

theorem not_sylow_le_center_of_isQuasisimple (hG : IsQuasisimple G) (P : Sylow p G)
    (hpG : p ∣ Nat.card G) : ¬ (P : Subgroup G) ≤ center G := by
  intro hP
  let S : Sylow p (G ⧸ center G) :=
    P.mapSurjective (QuotientGroup.mk'_surjective (center G))
  have hS : (S : Subgroup (G ⧸ center G)) = ⊥ := by
    rw [Sylow.coe_mapSurjective, Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
    exact hP
  have hnot : ¬ p ∣ Nat.card (G ⧸ center G) := by
    simpa only [hS, Subgroup.index_bot] using S.not_dvd_index
  exact hnot (CFSG.dvd_card_quotient_center_of_quasisimple hG Fact.out hpG)

omit [Finite G] [Fact p.Prime] in
private theorem oPrimeResidual_normal (p : ℕ) : (oPrimeResidual p G).Normal := by
  refine ⟨?_⟩
  intro x hx y
  change (MulAut.conj y) x ∈
    Subgroup.closure {z : G | ∃ k : ℕ, z ^ (p ^ k) = 1}
  change x ∈ Subgroup.closure {z : G | ∃ k : ℕ, z ^ (p ^ k) = 1} at hx
  induction hx using Subgroup.closure_induction with
  | mem z hz =>
      apply Subgroup.subset_closure
      obtain ⟨k, hk⟩ := hz
      refine ⟨k, ?_⟩
      simpa only [map_pow, map_one] using congrArg (MulAut.conj y) hk
  | one =>
      simpa only [map_one, oPrimeResidual] using
        (Subgroup.one_mem (oPrimeResidual p G))
  | mul a b ha hb ia ib =>
      simpa only [map_mul, oPrimeResidual] using (oPrimeResidual p G).mul_mem ia ib
  | inv a ha ia =>
      simpa only [map_inv, oPrimeResidual] using (oPrimeResidual p G).inv_mem ia

omit [Finite G] [Fact p.Prime] in
private theorem le_oPrimeResidual_of_isPGroup (P : Subgroup G) (hP : IsPGroup p P) :
    P ≤ oPrimeResidual p G := by
  intro x hx
  obtain ⟨k, hk⟩ := hP ⟨x, hx⟩
  apply Subgroup.subset_closure
  exact ⟨k, congrArg Subtype.val hk⟩

theorem oPrimeResidual_eq_top_of_isQuasisimple (hG : IsQuasisimple G)
    (hpG : p ∣ Nat.card G) : oPrimeResidual p G = ⊤ := by
  rcases LocalCores.quasisimple_normal_subgroups hG (oPrimeResidual_normal p) with h | h
  · exact h
  · let P : Sylow p G := Sylow.nonempty.some
    exact False.elim (not_sylow_le_center_of_isQuasisimple hG P hpG
      ((le_oPrimeResidual_of_isPGroup (P : Subgroup G) P.isPGroup').trans h))

end CFSG.SecondGeneration
