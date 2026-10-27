module

public import CFSG.Goldschmidt.Basic

public section

namespace CFSG.Goldschmidt75

open CFSG.Open CFSG.Goldschmidt Subgroup

variable {G : Type*} [Group G]

theorem odd_card_oddCore [Finite G] : Odd (Nat.card (goldschmidtOddCore G)) := by
  rw [goldschmidtOddCore_eq_pPrimeCore]
  have h : Nat.Coprime 2 (Nat.card (CFSG.pPrimeCore 2 G)) := CFSG.pPrimeCore_coprime_card
  exact Nat.coprime_two_left.mp h

theorem le_oddCore {N : Subgroup G} (hN : N.Normal) (hodd : Odd (Nat.card N)) :
    N ≤ goldschmidtOddCore G :=
  le_sSup ⟨hN, hodd⟩

theorem eq_one_of_mem_odd_of_two_power [Finite G] {X : Subgroup G} (hX : Odd (Nat.card X))
    {x : G} (hx : x ∈ X) {k : ℕ} (hk : x ^ (2 ^ k) = 1) : x = 1 := by
  have h1 : orderOf x ∣ Nat.card X := by
    rw [← Subgroup.orderOf_mk x hx]; exact orderOf_dvd_natCard _
  have h2 : orderOf x ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h2
  have hodd : Odd (orderOf x) := Odd.of_dvd_nat hX h1
  rcases j with _ | j
  · rwa [pow_zero, orderOf_eq_one_iff] at hj
  · rw [hj, pow_succ] at hodd
    exact absurd hodd (by simp [Nat.not_odd_iff_even])

theorem oddCore_quotient_eq_bot [Finite G] :
    goldschmidtOddCore (G ⧸ goldschmidtOddCore G) = ⊥ :=
  goldschmidtOddCore_quotient_eq_bot G

theorem map_oddCore_le [Finite G] {H : Type*} [Group H] (f : G →* H)
    (hf : Function.Surjective f) : (goldschmidtOddCore G).map f ≤ goldschmidtOddCore H := by
  refine le_oddCore ((goldschmidtOddCore_normal G).map f hf) ?_
  exact Odd.of_dvd_nat odd_card_oddCore (Subgroup.card_map_dvd _ _)

theorem oddCoreOf_le_of_normal [Finite G] {N : Subgroup G} [N.Normal] :
    oddCoreOf N ≤ goldschmidtOddCore G := by
  have : (goldschmidtOddCore N).Characteristic := by
    rw [goldschmidtOddCore_eq_pPrimeCore]; infer_instance
  refine le_oddCore (ConjAct.normal_of_characteristic_of_normal) ?_
  have e := Nat.card_congr ((goldschmidtOddCore N).equivMapOfInjective _
    N.subtype_injective).toEquiv
  unfold oddCoreOf
  rw [← e]
  exact odd_card_oddCore

theorem oddCore_eq_bot_of_normal [Finite G] {N : Subgroup G} [N.Normal]
    (hO : goldschmidtOddCore G = ⊥) : goldschmidtOddCore N = ⊥ := by
  have h := oddCoreOf_le_of_normal (N := N)
  rw [hO, le_bot_iff] at h
  exact (Subgroup.map_eq_bot_iff_of_injective _ N.subtype_injective).mp h

end CFSG.Goldschmidt75
