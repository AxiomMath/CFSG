module

public import CFSG.HardMathSupport.Dickson.Sec6.I923Fam.TriD4Aux.Basic

public section

open CFSG.HardMathSupport.Solomon.LocalBalance.Lemma514CoverNs CFSG.Open
  CFSG.HardMathSupport.Solomon.Coordinator
open CFSG.HardMathSupport.Dickson.Sec6.I923

namespace CFSG.HardMathSupport.Dickson.Sec6.I923.TriD4A2

theorem l2_arith_false {x C M r : ℕ} (hx : x = 1 ∨ IsPrimePow x) (hxM : x ∣ M)
    (hMle : M ≤ x * C) (hkey : 2 * C < (x - 1) * (x - 2)) (hr : 10 ≤ r)
    (hodd : Odd r → 2 * M + r = r ^ 3) (heven : Even r → M + r = r ^ 3) : False := by
  have hxr := le_succ_of_dvd_l2 hx (by omega) hxM hodd heven
  obtain ⟨y, rfl⟩ : ∃ y, x = y + 3 := by
    rcases Nat.lt_or_ge x 3 with h | h
    · exfalso
      interval_cases x <;> simp at hkey
    · exact ⟨x - 3, by omega⟩
  simp only [show y + 3 - 1 = y + 2 by omega, show y + 3 - 2 = y + 1 by omega] at hkey
  obtain ⟨s, rfl⟩ : ∃ s, r = s + 1 := ⟨r - 1, by omega⟩
  have hs : y + 1 ≤ s := by omega
  have h3 : (y + 3) * ((y + 2) * (y + 1)) ≤ (s + 2) * ((s + 1) * s) :=
    Nat.mul_le_mul (by omega) (Nat.mul_le_mul (by omega) (by omega))
  have h2M : (y + 3) * ((y + 2) * (y + 1)) ≤ 2 * M := by
    rcases Nat.even_or_odd (s + 1) with hev | hod
    · have h1 := heven hev
      have : M = (s + 2) * ((s + 1) * s) := by nlinarith
      omega
    · have h1 := hodd hod
      have : 2 * M = (s + 2) * ((s + 1) * s) := by nlinarith
      omega
  have h5 : (y + 3) * ((y + 2) * (y + 1)) ≤ (y + 3) * (2 * C) := by
    calc (y + 3) * ((y + 2) * (y + 1)) ≤ 2 * M := h2M
      _ ≤ 2 * ((y + 3) * C) := by omega
      _ = (y + 3) * (2 * C) := by ring
  have h4 := Nat.le_of_mul_le_mul_left h5 (by omega)
  omega

theorem not_typeL2_of_arith {S : Type} [Group S] [Finite S] [IsSimpleGroup S]
    (hnab : ∃ a b : S, a * b ≠ b * a) {x C : ℕ} (hx : x = 1 ∨ IsPrimePow x)
    (hxS : x ∣ Nat.card S) (hSC : Nat.card S ≤ x * C) (hkey : 2 * C < (x - 1) * (x - 2))
    {r : ℕ} (hr : 10 ≤ r) : ¬ IsTypeL2 r S := by
  intro hT
  obtain ⟨-, hodd, heven⟩ := CFSG.HardMathSupport.Solomon.Proving.typeL2_card S hT
  have hcard : Nat.card (S ⧸ Subgroup.center S) = Nat.card S := by
    rw [center_eq_bot_of_simple hnab]
    exact Nat.card_congr (QuotientGroup.quotientBot (G := S)).toEquiv
  exact l2_arith_false hx hxS hSC hkey hr (fun h => by rw [← hcard]; exact hodd h)
    (fun h => by rw [← hcard]; exact (heven h).1)

theorem noL2Layer_of_simple_normal {P : Type} [Group P] [Finite P] (ψ : MulAut P) {G : Type}
    [Group G] (e : ↥(fixSubgroup ψ) ≃* G) (S : Subgroup G) [S.Normal]
    (hsol : Group.IsSolvable (G ⧸ S)) (hs : IsSimpleGroup ↥S) (hnab : ∃ a b : ↥S, a * b ≠ b * a)
    {x C : ℕ} (hx : x = 1 ∨ IsPrimePow x) (hxS : x ∣ Nat.card S) (hSC : Nat.card S ≤ x * C)
    (hkey : 2 * C < (x - 1) * (x - 2)) : NoL2Layer ψ := by
  haveI : Finite G := Finite.of_equiv _ e.toEquiv
  haveI : Finite ↥S := inferInstance
  refine TriD4Aux.noL2Layer_of_equiv_normal_simple ψ e S hsol hs hnab fun r hr => ?_
  exact not_typeL2_of_arith hnab hx hxS hSC hkey hr

theorem key_of_le_pow_five {q C : ℕ} (hq : 3 ≤ q) (hC : C ≤ q ^ 5) :
    2 * C < (q ^ 3 - 1) * (q ^ 3 - 2) := by
  have h3 : 27 ≤ q ^ 3 := by
    calc 27 = 3 ^ 3 := by norm_num
      _ ≤ q ^ 3 := Nat.pow_le_pow_left hq 3
  obtain ⟨y, hy⟩ : ∃ y, q ^ 3 = y + 3 := ⟨q ^ 3 - 3, by omega⟩
  rw [hy, show y + 3 - 1 = y + 2 by omega, show y + 3 - 2 = y + 1 by omega]
  have h5 : q ^ 5 = q ^ 3 * q ^ 2 := by ring
  have hq2 : 9 ≤ q ^ 2 := by nlinarith
  have h6 : (y + 3) * 9 ≤ q ^ 5 := by rw [h5, hy]; exact Nat.mul_le_mul_left _ hq2
  have h7 : 3 * q ^ 5 ≤ (y + 3) * (y + 3) := by
    have : q ^ 5 * 3 ≤ q ^ 5 * q := Nat.mul_le_mul_left _ hq
    have h8 : q ^ 5 * q = (y + 3) * (y + 3) := by rw [← hy]; ring
    nlinarith
  nlinarith

end CFSG.HardMathSupport.Dickson.Sec6.I923.TriD4A2
