module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.HFIBasic
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.HFIPerm
import Mathlib.Tactic.IntervalCases

public section

namespace CFSG.EvenSporadicStandard.HSStd.HFI

open Equiv Equiv.Perm Subgroup

theorem sign_eq_neg_one_of_card_eq_240 {σ : Perm (Fin 7)} (h2 : σ * σ = 1) (h1 : σ ≠ 1)
    (hc : Nat.card (centralizer ({σ} : Set (Perm (Fin 7)))) = 240) : Perm.sign σ = -1 := by
  obtain ⟨m, hm1, hm2, hcard, hsign⟩ := exists_card_centralizer_involution h2 h1
  rw [hcard] at hc
  have hm3 : m ≤ 3 := by omega
  interval_cases m
  · simpa using hsign
  · norm_num [Nat.factorial] at hc
  · norm_num [Nat.factorial] at hc

theorem false_of_good_triple_perm_seven {D : Type*} [Group D] (e7 : D ≃* Perm (Fin 7)) {a b : D}
    (ha : orderOf a = 2) (hb : orderOf b = 2) (hab : a ≠ b) (hcomm : a * b = b * a)
    (ea : Nonempty (↥(centralizer ({a} : Set D)) ≃* Multiplicative (ZMod 2) × Perm (Fin 5)))
    (eb : Nonempty (↥(centralizer ({b} : Set D)) ≃* Multiplicative (ZMod 2) × Perm (Fin 5)))
    (eab : Nonempty (↥(centralizer ({a * b} : Set D)) ≃* Multiplicative (ZMod 2) × Perm (Fin 5))) :
    False := by
  have hodd : ∀ {x : D}, orderOf x = 2 →
      Nonempty (↥(centralizer ({x} : Set D)) ≃* Multiplicative (ZMod 2) × Perm (Fin 5)) →
        Perm.sign (e7 x) = -1 := by
    intro x hx ex
    have hx2 : x * x = 1 := by rw [← sq, ← hx]; exact pow_orderOf_eq_one x
    have hx1 : x ≠ 1 := fun h => by rw [h, orderOf_one] at hx; omega
    refine sign_eq_neg_one_of_card_eq_240 (by rw [← map_mul, hx2, map_one])
      (fun h => hx1 (e7.injective (h.trans (map_one e7).symm))) ?_
    rw [card_centralizer_singleton_map e7 x, card_centralizer_of_good ex]
  have h1 := hodd ha ea
  have h2 := hodd hb eb
  have h3 := hodd (orderOf_mul_eq_two ha hb hab hcomm) eab
  rw [map_mul, Perm.sign_mul, h1, h2] at h3
  exact absurd h3 (by decide)

end CFSG.EvenSporadicStandard.HSStd.HFI
