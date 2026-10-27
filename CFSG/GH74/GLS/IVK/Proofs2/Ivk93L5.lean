module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93PGLType
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93Field
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93Leaves

public section

namespace CFSG.GH74.GLS.IVK.Proofs2

open Subgroup CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.Sp4Rec
open scoped MatrixGroups

theorem Ivk93Cfg.false_of_equiv_sl2_sl3 {J : Type} [Group J] [Finite J] {x : J} {q : ℕ}
    {L₁ L₂ : Subgroup J} (h : Ivk93Cfg x q L₁ L₂) {F : Type} [Field F] [Finite F]
    (hodd : Odd (Nat.card F)) (e₁ : SL(2, F) ≃* ↥L₁) (e₂ : SL(3, F) ≃* ↥L₂) : False := by
  have h5 := h.five_le_of_equiv_sl2 e₁
  have hq : Nat.card F = q := h.q_eq_of_equiv_sl2 hodd h5 e₁
  have hc2 := h.card₂
  have hc3 : Nat.card ↥L₂ = Nat.card F ^ 3 * (Nat.card F ^ 2 - 1) * (Nat.card F ^ 3 - 1) := by
    rw [← Nat.card_congr e₂.toEquiv]
    exact CFSG.GH74.KGroups.L3Eps.card_specialLinear_three
  have hcop : Nat.Coprime 2 (Nat.card ↥(pPrimeCore 2 ↥L₂)) :=
    CFSG.pPrimeCore_coprime_card (p := 2) (G := ↥L₂)
  rw [← hq] at hc2
  generalize Nat.card ↥(pPrimeCore 2 ↥L₂) = N at hcop hc2
  generalize Nat.card F = Q at hodd h5 hc2 hc3
  have hpos : 0 < Q * (Q ^ 2 - 1) := by
    have : 4 ≤ Q ^ 2 := by nlinarith
    exact Nat.mul_pos (by omega) (by omega)
  have hN : N = Q ^ 2 * (Q ^ 3 - 1) := by
    apply Nat.eq_of_mul_eq_mul_left hpos
    calc Q * (Q ^ 2 - 1) * N = Nat.card ↥L₂ := hc2.symm
      _ = Q ^ 3 * (Q ^ 2 - 1) * (Q ^ 3 - 1) := hc3
      _ = Q * (Q ^ 2 - 1) * (Q ^ 2 * (Q ^ 3 - 1)) := by ring
  have h2 : 2 ∣ N := by
    rw [hN]
    exact Dvd.dvd.mul_left (even_iff_two_dvd.mp (Nat.Odd.sub_odd hodd.pow odd_one)) _
  exact absurd (Nat.Coprime.eq_one_of_dvd hcop h2) (by norm_num)

theorem ivk93_l5 : ∀ p f : ℕ, p.Prime → 1 ≤ f → p ^ f % 4 = 3 →
    Ivk93Empty (fun X _ => LieModel X .PSL 5 p f) := by
  intro p f hp hf hmod J _ _ hJ x hx q L₁ L₂ h
  obtain ⟨⟨-, -, -⟩, F, _, _, hF, ⟨e⟩⟩ := CFSG.GH74.Generic.stated_of_lieModel_PSL hJ
  have hodd : Odd (Nat.card F) := by rw [hF]; exact Nat.odd_iff.mpr (by omega)
  have h2 : (2 : F) ≠ 0 := two_ne_zero_of_odd_natCard hodd
  have : Finite (StatedProj (StatedSL 5 F)) := Finite.of_equiv _ e.toEquiv
  have h' := h.of_equiv e
  obtain ⟨a, b, ha, hb, hab, ⟨e₁⟩, ⟨e₂⟩⟩ := h'.two_blocks h2 (by norm_num)
  have hab' : (a = 2 ∧ b = 3) ∨ (a = 3 ∧ b = 2) := by omega
  rcases hab' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact h'.false_of_equiv_sl2_sl3 hodd e₁ e₂
  · exact h'.symm.false_of_equiv_sl2_sl3 hodd e₂ e₁

end CFSG.GH74.GLS.IVK.Proofs2
