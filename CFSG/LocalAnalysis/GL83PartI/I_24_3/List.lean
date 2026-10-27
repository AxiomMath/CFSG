module

public import CFSG.LocalAnalysis.GL83PartI.I_24_3.ListDefs
public import CFSG.LocalAnalysis.ComponentClassification.SolAltLitSol78Inputs
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverList
import CFSG.LocalAnalysis.GL83PartI.I_24_3.ListLie

public section

namespace GL83.I243

open CFSG

namespace CoverList

theorem eq_three_of_dvd_twelve {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (h : p ∣ 12) : p = 3 := by
  have h' : p ∣ 2 ^ 2 * 3 := by simpa using h
  rcases (Nat.Prime.dvd_mul hp).1 h' with h2 | h3
  · exact absurd ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h2)) hp2
  · exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 h3

theorem sporadic_three_cases (s : TauCeti.SporadicName)
    (h : 3 ∣ CFSG.RankThree.PartTwo.Sec4.Census.sporadicMultiplierOrder s) :
    s = .M22 ∨ s = .J3 ∨ s = .McL ∨ s = .Suz ∨ s = .ONan ∨ s = .Fi22 ∨ s = .Fi24Prime := by
  revert h
  cases s <;> decide

theorem sporadicMultiplierOrder_dvd_twelve (s : TauCeti.SporadicName) :
    CFSG.RankThree.PartTwo.Sec4.Census.sporadicMultiplierOrder s ∣ 12 := by
  cases s <;> decide

theorem false_of_cyclic {K : Type} [Group K] (hq : CFSG.IsQuasisimple K) {r : ℕ} {hr : r.Prime}
    (e : K ⧸ Subgroup.center K ≃* (TauCeti.CFSGIndex.cyclic r hr).Group) : False := by
  obtain ⟨a, b, hab⟩ := hq.2.2
  apply hab
  apply e.injective
  rw [map_mul, map_mul]
  exact mul_comm (G := Multiplicative (ZMod r)) _ _

theorem card_center_dvd_alternating
    (hAlt : CFSG.ComponentClassification.SolAltLit.SchurAlternatingMultiplierInput) {K : Type}
    [Group K] [Finite K] (hq : CFSG.IsQuasisimple K) {n : ℕ} (hn : 5 ≤ n)
    (e : K ⧸ Subgroup.center K ≃* (TauCeti.CFSGIndex.alternating n hn).Group) :
    Nat.card (Subgroup.center K) ∣ if n = 6 ∨ n = 7 then 6 else 2 := by
  have hdvd := CFSG.GH74.Generic.card_center_dvd_hopfMultiplier hq e
  rwa [(hAlt n hn).2] at hdvd

theorem card_center_dvd_sporadic (hSpor : CFSG.RankThree.PartTwo.Sec4.Census.SporadicMultipliers)
    {K : Type} [Group K] [Finite K] (hq : CFSG.IsQuasisimple K) {s : TauCeti.SporadicName}
    (e : K ⧸ Subgroup.center K ≃* (TauCeti.CFSGIndex.sporadic s).Group) :
    Nat.card (Subgroup.center K) ∣ CFSG.RankThree.PartTwo.Sec4.Census.sporadicMultiplierOrder s := by
  have hdvd := CFSG.GH74.Generic.card_center_dvd_hopfMultiplier hq e
  rwa [hSpor.1 s] at hdvd

end CoverList

open CoverList in
theorem pCoverList_of_tables
    (hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels)
    (hAlt : CFSG.ComponentClassification.SolAltLit.SchurAlternatingMultiplierInput)
    (hSpor : CFSG.RankThree.PartTwo.Sec4.Census.SporadicMultipliers) : PCoverList := by
  intro K _ _ hq p hp hp2 hpZ i ⟨e⟩
  have hq' := isQuasisimple_of_open hq
  cases i with
  | cyclic r hr => exact (false_of_cyclic hq' e).elim
  | alternating n hn =>
    have hdvd := card_center_dvd_alternating hAlt hq' hn e
    by_cases h67 : n = 6 ∨ n = 7
    · rw [if_pos h67] at hdvd
      have hp3 : p = 3 := eq_three_of_dvd_twelve hp hp2 ((hpZ.trans hdvd).trans (by norm_num))
      refine Or.inr ⟨hp3, Or.inr ⟨Or.inl (Or.inl ⟨n, hn, h67, rfl⟩), fun h9 => ?_⟩⟩
      have := h9.trans hdvd
      norm_num at this
    · rw [if_neg h67] at hdvd
      exact absurd ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hpZ.trans hdvd)) hp2
  | sporadic s =>
    have hdvd := card_center_dvd_sporadic hSpor hq' e
    have h12 : Nat.card (Subgroup.center K) ∣ 12 :=
      hdvd.trans (sporadicMultiplierOrder_dvd_twelve s)
    have hp3 : p = 3 := eq_three_of_dvd_twelve hp hp2 (hpZ.trans h12)
    subst hp3
    refine Or.inr ⟨rfl, ?_⟩
    have h9 : ¬ 3 ^ 2 ∣ Nat.card (Subgroup.center K) := fun h9 => by
      have := h9.trans h12
      norm_num at this
    rcases sporadic_three_cases s (hpZ.trans hdvd) with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inr ⟨Or.inl (Or.inr rfl), h9⟩
    · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
    · exact Or.inl (Or.inl rfl)
    · exact Or.inl (Or.inr (Or.inl rfl))
    · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
    · exact Or.inl (Or.inr (Or.inr (Or.inl rfl)))
    · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  | lie d =>
    rcases lie_case hGA hq hp hp2 hpZ d e with ⟨h1, h2, h3⟩ | ⟨h3, h | ⟨h, h9⟩⟩
    · exact Or.inl ⟨d, rfl, h1, h2, h3⟩
    · exact Or.inr ⟨h3, Or.inl h⟩
    · exact Or.inr ⟨h3, Or.inr ⟨Or.inr h, h9⟩⟩

end GL83.I243
