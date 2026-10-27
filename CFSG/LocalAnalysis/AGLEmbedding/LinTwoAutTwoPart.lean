module

public import CFSG.LocalAnalysis.AGLEmbedding.LinTwoCatalog
import CFSG.LocalAnalysis.AGLEmbedding.LinTwoAutCard
import CFSG.Walter.PSL2Facts.Odd
import CFSG.GH74.GLS.Stage1.Main.Out

set_option autoImplicit false

public section

namespace CFSG.AGLEmbedding

open CFSG.GorensteinWalter

theorem card_dvd_eight_of_injective_mulAut_psl2
    {W : Type*} [Group W] [Finite W]
    {K : Type} [Group K] [Finite K]
    {p f : ℕ} [Fact p.Prime]
    (hp : Odd p) (hf : 0 < f) (h5 : 5 ≤ p ^ f)
    (h8 : p ^ f % 8 = 3 ∨ p ^ f % 8 = 5)
    (e : K ≃* PSL2GF p f)
    (hW : IsPGroup 2 W)
    (α : W →* MulAut K) (hα : Function.Injective α) :
    Nat.card W ∣ 8 := by
  have hqpos : 0 < p ^ f := pow_pos (Fact.out : p.Prime).pos f
  have hq2 : 0 < (p ^ f) ^ 2 - 1 := by
    have h25 : 25 ≤ (p ^ f) ^ 2 := by
      simpa using pow_le_pow_left' h5 2
    omega
  have hprod : p ^ f * ((p ^ f) ^ 2 - 1) ≠ 0 :=
    mul_ne_zero (ne_of_gt hqpos) (ne_of_gt hq2)
  have hcard : Nat.card (MulAut K) = p ^ f * ((p ^ f) ^ 2 - 1) * f := by
    rw [Nat.card_congr (MulAut.congr e).toEquiv, card_mulAut_psl2GF p f (by omega)]
  have hfodd : Odd f := CFSG.Walter.odd_of_pow_mod_eight hp h8
  have hffac : f.factorization 2 = 0 :=
    Nat.factorization_eq_zero_of_not_dvd (Odd.not_two_dvd_nat hfodd)
  have hfac : (Nat.card (MulAut K)).factorization 2 = 3 := by
    rw [hcard, Nat.factorization_mul hprod (ne_of_gt hf), Finsupp.add_apply,
      CFSG.GH74.GLS.Stage1.Main.factorization_two_mul_sq_sub_one (p ^ f) h8, hffac,
      add_zero]
  have hcardne : Nat.card (MulAut K) ≠ 0 := by
    rw [hcard]
    exact mul_ne_zero hprod (ne_of_gt hf)
  have hdvd : Nat.card W ∣ Nat.card (MulAut K) := Subgroup.card_dvd_of_injective α hα
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨r, hr⟩ := hW.exists_card_eq
  have hdvd' : 2 ^ r ∣ Nat.card (MulAut K) := hr ▸ hdvd
  have hrle : r ≤ 3 := by
    have h := (Nat.Prime.pow_dvd_iff_le_factorization (p := 2) (k := r)
      (n := Nat.card (MulAut K)) Nat.prime_two hcardne).mp hdvd'
    simpa [hfac] using h
  rw [hr, show (8 : ℕ) = 2 ^ 3 by norm_num]
  exact pow_dvd_pow 2 hrle

end CFSG.AGLEmbedding
