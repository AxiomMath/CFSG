module

public import CFSG.GH74.GLS.IVK.L2.FieldProj
import CFSG.GH74.GLS.IVK.L2.Lemma12

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87.L29M12

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS

theorem mul_self_mod_eight_ne_three_five (x : ℕ) : x * x % 8 ≠ 3 ∧ x * x % 8 ≠ 5 := by
  have h : x % 8 < 8 := Nat.mod_lt _ (by norm_num)
  rw [Nat.mul_mod]
  interval_cases (x % 8) <;> decide

theorem odd_card_ringEquiv_of_mod_eight {F : Type} [Field F] [Finite F] (hF : IVK.L2Field F)
    (h8 : Nat.card F % 8 = 3 ∨ Nat.card F % 8 = 5) {K : Type} [Group K]
    (e : K ≃* IVK.L2 F) : Odd (Nat.card (F ≃+* F)) := by
  have : Finite K := Finite.of_equiv _ e.toEquiv.symm
  obtain ⟨p, hp⟩ := CharP.exists F
  have hpp : p.Prime := CharP.char_is_prime F p
  have := Fintype.ofFinite F
  obtain ⟨n, -, hn⟩ := FiniteField.card F p
  have hcard : Nat.card F = p ^ (n : ℕ) := by rw [Nat.card_eq_fintype_card]; exact hn
  obtain ⟨-, ⟨ε⟩, hεn⟩ := IVK.ivk_1_2e F hF K e
  rw [← Nat.card_congr ε.toEquiv, hεn p n hpp hcard]
  by_contra hev
  rw [Nat.not_odd_iff_even] at hev
  obtain ⟨m, hm⟩ := hev
  have hsq : Nat.card F = p ^ m * p ^ m := by rw [hcard, ← pow_add, ← hm]
  have := mul_self_mod_eight_ne_three_five (p ^ m)
  rw [← hsq] at this
  omega

theorem mem_innDiagSub_of_involution {F : Type} [Field F] [Finite F] (hF : IVK.L2Field F)
    (h8 : Nat.card F % 8 = 3 ∨ Nat.card F % 8 = 5) {K : Type} [Group K]
    (e : K ≃* IVK.L2 F) (α : MulAut K) (hα : α * α = 1) : α ∈ IVK.innDiagSub e := by
  rw [IVK.mem_innDiagSub_iff, ← orderOf_eq_one_iff]
  have hσ : IVK.fieldProj e α * IVK.fieldProj e α = 1 := by rw [← map_mul, hα, map_one]
  have h1 : orderOf (IVK.fieldProj e α) ∣ 2 :=
    orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hσ)
  have h2 : orderOf (IVK.fieldProj e α) ∣ Nat.card (F ≃+* F) := orderOf_dvd_natCard _
  have hodd := odd_card_ringEquiv_of_mod_eight hF h8 e
  rcases (Nat.dvd_prime Nat.prime_two).1 h1 with h | h
  · exact h
  · rw [h] at h2
    exact absurd (hodd.not_two_dvd_nat h2) (by simp)

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87.L29M12
