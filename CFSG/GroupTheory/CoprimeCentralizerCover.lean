module

public import CFSG.GroupTheory.ABGLocalTools.Basic
import CFSG.HardMathSupport.Solomon.Coordinator.Generation228
import CFSG.GroupTheory.SteinbergCBFTFactorization

public section

namespace CFSG.GroupTheory

open Subgroup
open scoped Pointwise

variable {G : Type*} [Group G] [Finite G]

private theorem exists_mul_mem_inf_centralizer_of_commutator_le {p : ℕ} [Fact p.Prime]
    {X N R : Subgroup G} (hNX : N ≤ X) (hRN : R ≤ Subgroup.normalizer (N : Set G))
    (hR : IsPGroup p R) (hN : ¬ p ∣ Nat.card N) (hcomm : ⁅X, R⁆ ≤ N) {x : G}
    (hxX : x ∈ X) :
    ∃ n ∈ N, ∃ c ∈ X ⊓ Subgroup.centralizer (R : Set G), x = n * c := by
  classical
  obtain ⟨n, hn, hc⟩ :=
    CFSG.HardMathSupport.Solomon.Coordinator.Generation228.exists_fixed_mem_coset
      (Fact.out : p.Prime) hR hRN hN (y := x⁻¹) (by
        intro a ha
        simpa [commutatorElement_def, mul_assoc] using
          hcomm (Subgroup.commutator_mem_commutator hxX ha))
  have hcX : x⁻¹ * n ∈ X := X.mul_mem (X.inv_mem hxX) (hNX hn)
  refine ⟨n, hn, (x⁻¹ * n)⁻¹, ⟨X.inv_mem hcX, ?_⟩, ?_⟩
  · exact (Subgroup.centralizer (R : Set G)).inv_mem hc
  · group

theorem inf_centralizer_sup_eq_of_commutator_le {p : ℕ} [Fact p.Prime] {X N R : Subgroup G}
    (hNX : N ≤ X) (hRX : R ≤ Subgroup.normalizer (X : Set G))
    (hRN : R ≤ Subgroup.normalizer (N : Set G))
    (hR : IsPGroup p R) (hN : ¬ p ∣ Nat.card N)
    (hcomm : ⁅X, R⁆ ≤ N) :
    X ⊓ Subgroup.centralizer (R : Set G) ⊔ N = X := by
  classical
  apply le_antisymm
  · exact sup_le inf_le_left hNX
  · intro x hxX
    obtain ⟨n, hn, c, hc, hxn⟩ :=
      exists_mul_mem_inf_centralizer_of_commutator_le hNX hRN hR hN hcomm hxX
    have hmem : n * c ∈ N ⊔ (X ⊓ Subgroup.centralizer (R : Set G)) :=
      Subgroup.mul_mem _ (Subgroup.mem_sup_left hn) (Subgroup.mem_sup_right hc)
    rw [hxn]
    simpa [sup_comm] using hmem

theorem exists_isSylowOf_le_centralizer_of_commutator_le {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    {X N R : Subgroup G} (hNX : N ≤ X) (hRX : R ≤ Subgroup.normalizer (X : Set G))
    (hRN : R ≤ Subgroup.normalizer (N : Set G))
    (hR : IsPGroup p R) (hN : ¬ p ∣ Nat.card N)
    (hcomm : ⁅X, R⁆ ≤ N) (hqN : ¬ q ∣ Nat.card N) :
    ∃ S : Subgroup G, CFSG.ABGLocalTools.IsSylowOf q S X ∧
      S ≤ Subgroup.centralizer (R : Set G) := by
  classical
  set C : Subgroup G := X ⊓ Subgroup.centralizer (R : Set G) with hC
  have hCX : C ≤ X := by rw [hC]; exact inf_le_left
  have hCcent : C ≤ Subgroup.centralizer (R : Set G) := by rw [hC]; exact inf_le_right
  have hXset : (X : Set G) = (N : Set G) * (C : Set G) := by
    apply Set.Subset.antisymm
    · intro x hxX
      obtain ⟨n, hn, c, hc, hxn⟩ :=
        exists_mul_mem_inf_centralizer_of_commutator_le hNX hRN hR hN hcomm hxX
      rw [hxn]
      exact Set.mul_mem_mul hn hc
    · rintro x ⟨n, hn, c, hc, rfl⟩
      exact X.mul_mem (hNX hn) hc.1
  have hcard := CFSG.GroupTheory.FT63ChII.card_setMul_mul_card_inf (A := N) (B := C)
  have hcardX : Nat.card ((N : Set G) * (C : Set G)) = Nat.card X := by
    rw [← hXset]
    rfl
  rw [hcardX] at hcard
  have hrelC : C.relIndex X * Nat.card C = Nat.card X := by
    have h := Subgroup.relIndex_mul_card (H := C) (K := X)
    rwa [inf_eq_left.mpr hCX] at h
  have hkey : C.relIndex X * Nat.card ↥(N ⊓ C) = Nat.card N := by
    refine Nat.eq_of_mul_eq_mul_right (Nat.card_pos (α := C)) ?_
    calc C.relIndex X * Nat.card ↥(N ⊓ C) * Nat.card C
        = (C.relIndex X * Nat.card C) * Nat.card ↥(N ⊓ C) := by ring
      _ = Nat.card X * Nat.card ↥(N ⊓ C) := by rw [hrelC]
      _ = Nat.card N * Nat.card C := hcard
  have hdvd : C.relIndex X ∣ Nat.card N := ⟨Nat.card ↥(N ⊓ C), hkey.symm⟩
  have hqC : ¬ q ∣ C.relIndex X := fun h => hqN (h.trans hdvd)
  obtain ⟨S, hS⟩ := CFSG.ABGLocalTools.exists_isSylowOf q C
  refine ⟨S, ?_, hS.le.trans hCcent⟩
  rw [CFSG.ABGLocalTools.isSylowOf_iff]
  refine ⟨hS.le.trans hCX, hS.isPGroup, ?_⟩
  rw [← Subgroup.relIndex_mul_relIndex S C X hS.le hCX]
  rintro h
  rcases (Fact.out : q.Prime).dvd_mul.mp h with h1 | h2
  · exact (CFSG.ABGLocalTools.isSylowOf_iff.mp hS).2.2 h1
  · exact hqC h2

end CFSG.GroupTheory
