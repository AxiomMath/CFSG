module

public import CFSG.GH74.GLS.IVK.Defs

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

private theorem isOddPrimePower_of_odd_card {F : Type} [Field F] [Finite F]
    (hodd : Odd (Nat.card F)) : GorensteinWalter.IsOddPrimePower (Nat.card F) := by
  have : Fintype F := Fintype.ofFinite F
  have hprime : (ringChar F).Prime := CharP.char_is_prime F _
  have : CharP F (ringChar F) := ringChar.charP F
  obtain ⟨n, -, hFn0⟩ := FiniteField.card F (ringChar F)
  have hFn : Nat.card F = ringChar F ^ (n : ℕ) := by
    rw [Nat.card_eq_fintype_card]
    exact hFn0
  refine ⟨ringChar F, n, hprime, ?_, n.pos, hFn⟩
  rw [hFn] at hodd
  exact (Nat.odd_pow_iff n.ne_zero).1 hodd

theorem card_L2_mul_two_of_odd {F : Type} [Field F] [Finite F] (hodd : Odd (Nat.card F)) :
    Nat.card (IVK.L2 F) * 2 = Nat.card F * (Nat.card F ^ 2 - 1) := by
  rw [Nat.card_congr (IVK.L2.equivPSL F).toEquiv,
    GorensteinWalter.psl2_card_formula F (isOddPrimePower_of_odd_card hodd)]
  apply Nat.div_mul_cancel
  obtain ⟨k, hk⟩ := hodd
  rw [hk]
  have h1 : (2 * k + 1) ^ 2 - 1 = 4 * (k * (k + 1)) := by
    have : (2 * k + 1) ^ 2 = 4 * (k * (k + 1)) + 1 := by ring
    omega
  rw [h1]
  exact ⟨(2 * k + 1) * (2 * (k * (k + 1))), by ring⟩

theorem ge_168_of_eight_dvd_isL2 {X : Type} [Group X] {q : ℕ} (hq : Odd q) (hq3 : 3 < q)
    (hX : IVK.IsL2 X (fun r => r = q)) (h8 : 8 ∣ Nat.card X) : 168 ≤ Nat.card X := by
  obtain ⟨F, _, _, hFq, ⟨e⟩⟩ := hX
  have hFq' : Nat.card F = q := hFq
  have hc := card_L2_mul_two_of_odd (F := F) (by rw [hFq']; exact hq)
  rw [← Nat.card_congr e.toEquiv, hFq'] at hc
  by_cases h5 : q = 5
  · subst h5
    omega
  · have h7 : 7 ≤ q := by
      obtain ⟨a, rfl⟩ := hq
      omega
    have h1 : 7 * (7 ^ 2 - 1) ≤ q * (q ^ 2 - 1) :=
      Nat.mul_le_mul h7 (Nat.sub_le_sub_right (Nat.pow_le_pow_left h7 2) 1)
    omega

private theorem nat_card_alternatingGroup_fin_seven :
    Nat.card (alternatingGroup (Fin 7)) = 2520 := by
  rw [Nat.card_eq_fintype_card, card_alternatingGroup]
  simp [Nat.factorial]

theorem no_solution_two_mul_card_alt7 {r : ℕ} (h5 : 5 ≤ r) : r * (r ^ 2 - 1) ≠ 5040 := by
  intro h
  have hr18 : r < 18 := by
    by_contra hge
    have h18 : 18 ≤ r := by omega
    have h1 : 18 * (18 ^ 2 - 1) ≤ r * (r ^ 2 - 1) :=
      Nat.mul_le_mul h18 (Nat.sub_le_sub_right (Nat.pow_le_pow_left h18 2) 1)
    omega
  interval_cases r <;> omega

theorem not_isL2_alt7 : ¬ IVK.IsL2 (alternatingGroup (Fin 7)) (fun r => Odd r ∧ 5 ≤ r) := by
  rintro ⟨F, _, _, ⟨hodd, h5⟩, ⟨e⟩⟩
  have hc := card_L2_mul_two_of_odd (F := F) hodd
  rw [← Nat.card_congr e.toEquiv, nat_card_alternatingGroup_fin_seven] at hc
  exact no_solution_two_mul_card_alt7 h5 (by omega)

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
