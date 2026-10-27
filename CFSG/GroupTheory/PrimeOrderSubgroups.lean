module

public import Mathlib.Tactic.IntervalCases
public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.ZMod.QuotientGroup

public section

namespace CFSG.GroupTheory

theorem disjoint_of_card_eq_prime_of_ne {E : Type*} [Group E]
    {p : ℕ} (hp : p.Prime) {L M : Subgroup E} (hL : Nat.card L = p)
    (hM : Nat.card M = p) (hne : L ≠ M) : Disjoint L M := by
  haveI : Finite L := Nat.finite_of_card_ne_zero (by rw [hL]; exact hp.ne_zero)
  haveI : Finite M := Nat.finite_of_card_ne_zero (by rw [hM]; exact hp.ne_zero)
  rw [disjoint_iff]
  have hdvd : Nat.card (L ⊓ M : Subgroup E) ∣ p := by
    rw [← hL]
    exact Subgroup.card_dvd_of_le inf_le_left
  rcases (Nat.dvd_prime hp).mp hdvd with h1 | hp'
  · exact Subgroup.eq_bot_of_card_eq (H := L ⊓ M) h1
  · exfalso
    have hLeq : (L ⊓ M : Subgroup E) = L :=
      Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hp', hL])
    have hLM : L ≤ M := by rw [← hLeq]; exact inf_le_right
    exact hne (Subgroup.eq_of_le_of_card_ge hLM (by rw [hM, hL]))

theorem exists_generator_of_card_prime {E : Type*} [Group E]
    {p : ℕ} (hp : p.Prime) {L : Subgroup E} (hL : Nat.card L = p) :
    ∃ x : E, x ∈ L ∧ orderOf x = p ∧ L = Subgroup.zpowers x := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Finite L := Nat.finite_of_card_ne_zero (by rw [hL]; exact hp.ne_zero)
  have hLnt : Nontrivial L := by
    rw [← Finite.one_lt_card_iff_nontrivial, hL]
    exact hp.one_lt
  obtain ⟨xL, hx1L⟩ := exists_ne (1 : L)
  let x : E := xL
  have hxL : x ∈ L := xL.2
  have hx1 : x ≠ 1 := by
    intro h
    exact hx1L (Subtype.ext h)
  have hxp : x ^ p = 1 := by
    have h := pow_card_eq_one' (G := L) (x := xL)
    rw [hL] at h
    simpa [x] using congrArg Subtype.val h
  have hxord : orderOf x = p := orderOf_eq_prime hxp hx1
  refine ⟨x, hxL, hxord, ?_⟩
  symm
  exact Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hxL)
    (by rw [Nat.card_zpowers, hxord, hL])

theorem sup_eq_top_of_card_eq_prime_of_ne {E : Type*} [Group E]
    {p : ℕ} (hp : p.Prime) {L M : Subgroup E} (hL : Nat.card L = p)
    (hM : Nat.card M = p) (hne : L ≠ M) (hEcard : Nat.card E = p ^ 2) :
    L ⊔ M = ⊤ := by
  haveI : Finite E := Nat.finite_of_card_ne_zero (by rw [hEcard]; exact pow_ne_zero 2 hp.ne_zero)
  haveI : Finite (L ⊔ M : Subgroup E) := Subtype.finite
  have hne_sup : L ≠ (L ⊔ M : Subgroup E) := by
    intro h
    have hMle : M ≤ L := by rw [h]; exact le_sup_right
    exact hne (Subgroup.eq_of_le_of_card_ge hMle (by rw [hM, hL])).symm
  have hlt : L < (L ⊔ M : Subgroup E) := lt_of_le_of_ne le_sup_left hne_sup
  have hcard_lt : p < Nat.card (L ⊔ M : Subgroup E) := by
    rw [← hL]
    exact Subgroup.card_lt_of_lt hlt
  have hdvd : Nat.card (L ⊔ M : Subgroup E) ∣ p ^ 2 := by
    have h := Subgroup.card_dvd_of_le (H := L ⊔ M) (K := ⊤) le_top
    simpa [Subgroup.card_top, hEcard, ← Nat.card_eq_fintype_card] using h
  rcases (Nat.dvd_prime_pow hp).mp hdvd with ⟨k, hk, hcard⟩
  have hcard' : Nat.card (L ⊔ M : Subgroup E) = p ^ 2 := by
    have hp1 : 1 < p := hp.one_lt
    interval_cases k
    · rw [pow_zero] at hcard
      have : p < 1 := by rwa [hcard] at hcard_lt
      omega
    · rw [pow_one] at hcard
      have : p < p := by rwa [hcard] at hcard_lt
      omega
    · exact hcard
  exact Subgroup.eq_top_of_card_eq (H := L ⊔ M) (by rw [hcard', hEcard])

theorem exists_complement_line_of_prime {E : Type*} [Group E]
    {p : ℕ} (hp : p.Prime) (hEcard : Nat.card E = p ^ 2)
    {A B L : Subgroup E} (hA : Nat.card A = p) (hB : Nat.card B = p)
    (hAB : A ≠ B) (hL : Nat.card L = p) :
    ∃ M : Subgroup E, Nat.card M = p ∧ M ≠ L ∧ IsCompl L M := by
  have hcomp : ∀ M : Subgroup E, Nat.card M = p → M ≠ L → IsCompl L M := by
    intro M hM hne
    exact ⟨disjoint_of_card_eq_prime_of_ne hp hL hM hne.symm,
      codisjoint_iff.mpr (sup_eq_top_of_card_eq_prime_of_ne hp hL hM hne.symm hEcard)⟩
  by_cases hLA : L = A
  · exact ⟨B, hB, by rw [hLA]; exact hAB.symm, hcomp B hB (by rw [hLA]; exact hAB.symm)⟩
  · exact ⟨A, hA, fun h => hLA h.symm, hcomp A hA (fun h => hLA h.symm)⟩

end CFSG.GroupTheory
