module

public import CFSG.GH74.GLS.Stage1.Thm3.Sec7.GrpA
public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.Ctx63

public section

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec8

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage1.Thm2.Recip
  CFSG.GH74.GLS.Stage1.Thm3.Sec4 CFSG.GH74.GLS.Stage1.Thm3.Sec5 CFSG.GH74.GLS.Stage1.Thm3.Sec6
  CFSG.GH74.GLS.Stage1.Thm3.Sec7
open scoped commutatorElement Pointwise

namespace Basic

theorem two_val_mul_odd {a b : ℕ} (ha : a ≠ 0) (hb : Odd b) :
    (a * b).factorization 2 = a.factorization 2 := by
  have hb0 : b ≠ 0 := by rintro rfl; simp at hb
  have h2 : ¬ 2 ∣ b := fun h => (Nat.not_even_iff_odd.2 hb) (even_iff_two_dvd.2 h)
  rw [Nat.factorization_mul ha hb0]
  simp [Nat.factorization_eq_zero_of_not_dvd h2]

theorem two_val_pow_mul_odd (e : ℕ) {m : ℕ} (hm : Odd m) : (2 ^ e * m).factorization 2 = e := by
  rw [two_val_mul_odd (by positivity) hm]
  simp [Nat.Prime.factorization_pow Nat.prime_two]

theorem card_statedSL_two (F : Type) [Field F] [Finite F] :
    Nat.card (StatedSL 2 F) = Nat.card F * (Nat.card F ^ 2 - 1) :=
  CFSG.Open.StatedAPI.card_statedSL_two F

theorem two_val_statedSL (F : Type) [Field F] [Finite F] (hodd : Odd (Nat.card F)) :
    (Nat.card (StatedSL 2 F)).factorization 2 = (Nat.card F ^ 2 - 1).factorization 2 := by
  rw [card_statedSL_two]
  have hF : Nat.card F ≠ 0 := Nat.card_pos.ne'
  have h2 : ¬ 2 ∣ Nat.card F := fun h => (Nat.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2 h)
  have hpos : Nat.card F ^ 2 - 1 ≠ 0 := by
    have : 2 ≤ Nat.card F := by
      rcases Nat.lt_or_ge (Nat.card F) 2 with h | h
      · exfalso
        have : Nat.card F = 1 := by omega
        have := Finite.one_lt_card (α := F)
        omega
      · exact h
    have : 4 ≤ Nat.card F ^ 2 := by nlinarith
    omega
  rw [Nat.factorization_mul hF hpos]
  simp [Nat.factorization_eq_zero_of_not_dvd h2]

theorem exists_odd_prime_pow (F : Type) [Field F] [Finite F] (hodd : Odd (Nat.card F)) :
    ∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ p ^ f = Nat.card F := by
  have := Fintype.ofFinite F
  obtain ⟨p, -, n, hp, hc⟩ := FiniteField.card' F
  refine ⟨p, n, hp, ?_, by rw [← hc, Nat.card_eq_fintype_card]⟩
  rintro rfl
  rw [Nat.card_eq_fintype_card, hc] at hodd
  have : Even (2 ^ (n : ℕ)) := (Nat.even_pow.2 ⟨even_two, n.pos.ne'⟩)
  exact (Nat.not_even_iff_odd.2 hodd) this

end Basic

namespace Fused8

variable {G : Type} [Group G] [Finite G] {z : G} {S K₁ K₂ : Subgroup G}

theorem card_P_hat (hII : II4_4_4_center) (hf : Fused8 G z S K₁ K₂) {K : Subgroup G}
    (hK : K = K₁ ∨ K = K₂) :
    ∃ e : ℕ, Nat.card ↥(Pof S K) = 2 ^ e ∧ (Nat.card (HatT K)).factorization 2 = e := by
  have hM := hf.m4 hII
  have hsyl := hM.Pi_syl hK
  have hPeq : M.Pm S K₁ K₂ ⊓ K = Pof S K := by
    rcases hK with rfl | rfl
    · unfold M.Pm Pof
      rw [inf_assoc, inf_eq_right.2 (le_sup_left : K ≤ K ⊔ K₂)]
    · unfold M.Pm Pof
      rw [inf_assoc, inf_eq_right.2 (le_sup_right : K ≤ K₁ ⊔ K)]
  rw [hPeq] at hsyl
  obtain ⟨e, m, hP, hm, hKc⟩ := hsyl.card_eq_pow_mul
  refine ⟨e, hP, ?_⟩
  have h1 : Nat.card ↥K = Nat.card (HatT K) * Nat.card ↥(pPrimeCore 2 ↥K) :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup (pPrimeCore 2 ↥K)
  have hodd : Odd (Nat.card ↥(pPrimeCore 2 ↥K)) := TwoThin.odd_card_pPrimeCore ↥K
  have h2 : (Nat.card ↥K).factorization 2 = e := by rw [hKc]; exact Basic.two_val_pow_mul_odd e hm
  rw [h1, Basic.two_val_mul_odd Nat.card_pos.ne' hodd] at h2
  exact h2

omit [Finite G] in
theorem isCentralProductOfSL2_swap {X : Type*} [Group X] {A B : Subgroup X} {F₁ F₂ : Type} [Field F₁]
    [Field F₂] (hcomm : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) (hcard : Nat.card ↥(A ⊓ B) = 2)
    (e₁ : ↥A ≃* StatedSL 2 F₁) (e₂ : ↥B ≃* StatedSL 2 F₂) :
    IsCentralProductOfSL2 (A ⊔ B) F₂ F₁ :=
  ⟨B, A, sup_comm _ _, fun b hb a ha => (hcomm a ha b hb).symm, by rw [inf_comm]; exact hcard,
    ⟨e₂⟩, ⟨e₁⟩⟩

end Fused8

end CFSG.GH74.GLS.Stage1.Thm3.Sec8
