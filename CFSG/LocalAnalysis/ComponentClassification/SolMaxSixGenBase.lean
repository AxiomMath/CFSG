
module

public import Certificates.Data.SolMaxSixGen
public import CFSG.LocalAnalysis.ComponentClassification.PSL3FourEnumSpec
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.GroupTheory.Perm.Centralizer

@[expose] public section

namespace CFSG.ComponentClassification.SolMax

open CFSG Subgroup Equiv
open CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four

namespace SixGen

theorem tabRep_tabOf (g : Perm (Fin 9)) : TabRep (tabOf g) g :=
  ⟨Array.size_ofFn, fun i => by rw [tabOf, getElem!_pos _ _ (by simp), Array.getElem_ofFn]⟩

theorem enumerates_of_list {L : List Swaps} {E : Enum}
    (h : enumOK 9 (L.map fun l => tabOf (permOf l)).toArray E = true) :
    Enumerates (closure {a | ∃ l ∈ L, a = permOf l}) E.tabs.toList := by
  set gens : Array Tab := (L.map fun l => tabOf (permOf l)).toArray with hgdef
  have hsize : gens.size = L.length := by simp [hgdef]
  have hget : ∀ j (hj : j < L.length), gens[j]! = tabOf (permOf L[j]) := by
    intro j hj
    rw [getElem!_pos gens j (by rw [hsize]; exact hj)]
    simp [hgdef]
  refine enumerates_closure (A := {a | ∃ l ∈ L, a = permOf l}) ?_ ?_ h
  · rintro a ⟨l, hl, rfl⟩
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hl
    exact ⟨j, by rw [hsize]; exact hj, by rw [hget j hj]; exact tabRep_tabOf _⟩
  · intro j hj
    have hj' : j < L.length := by rw [← hsize]; exact hj
    exact ⟨permOf L[j], ⟨L[j], List.getElem_mem hj', rfl⟩, by rw [hget j hj']; exact tabRep_tabOf _⟩

theorem commute_of_commutes {a b : Perm (Fin 9)} (h : commutes (tabOf a) (tabOf b) = true) :
    a * b = b * a :=
  ((tabRep_tabOf a).comp (tabRep_tabOf b)).perm_eq
    (by rw [commutes, beq_iff_eq] at h; rw [h]; exact (tabRep_tabOf b).comp (tabRep_tabOf a))

theorem cycleType_of_mul_self {σ : Perm (Fin 9)} {k : ℕ} (h2 : σ * σ = 1) (hk : 0 < k)
    (hs : σ.support.card = 2 * k) : σ.cycleType = Multiset.replicate k 2 := by
  have h1 : σ ≠ 1 := by
    rintro rfl
    rw [Perm.support_one, Finset.card_empty] at hs
    omega
  have ho : orderOf σ = 2 := orderOf_eq_prime (by rw [sq]; exact h2) h1
  obtain ⟨n, hn⟩ := Perm.cycleType_prime_order (σ := σ) (by rw [ho]; exact Nat.prime_two)
  rw [ho] at hn
  have hsum := Perm.sum_cycleType σ
  rw [hn, Multiset.sum_replicate, smul_eq_mul, hs] at hsum
  rw [hn]
  congr 1
  omega

theorem u₀_mul_self : permOf u₀ * permOf u₀ = 1 := by decide

theorem card_support_u₀ : (permOf u₀).support.card = 6 := by decide

theorem card_centralizer_u₀ : Nat.card (centralizer {permOf u₀}) = 288 := by
  rw [Perm.nat_card_centralizer,
    cycleType_of_mul_self (k := 3) u₀_mul_self (by norm_num) card_support_u₀]
  simp
  decide

end SixGen

end CFSG.ComponentClassification.SolMax
