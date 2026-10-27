module

public import CFSG.GH74.GLS.C3.Layer1.Th2P412GoldBender
import CFSG.Goldschmidt.Steps.GoldTypeBender
import CFSG.LocalAnalysis.ComponentClassification.AschbacherWalterSchurReeJ1

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Open
open scoped MatrixGroups

theorem sec5g_psl2_of_sylow_card_four
    {K : Type} [Group K] [Finite K] (hK : goldschmidtSimpleType K) (T : Sylow 2 K)
    (h4 : Nat.card (T : Subgroup K) = 4) :
    ∃ (p f : ℕ) (_ : Fact p.Prime), Odd p ∧ 0 < f ∧ 5 ≤ p ^ f ∧
      (p ^ f % 8 = 3 ∨ p ^ f % 8 = 5) ∧ Nonempty (K ≃* PSL(2, GaloisField p f)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hΩ : Nat.card (CFSG.Goldschmidt.Omega1 (T : Subgroup K)) ≤ 4 := by
    rw [← h4]
    exact Subgroup.card_le_of_le (CFSG.Goldschmidt.GoldType.omega1_le _)
  rcases hK with ⟨f, hf, ⟨e⟩⟩ | ⟨n, hn, ⟨e⟩⟩ | ⟨f, hf, ⟨e⟩⟩ | h | ⟨m, -, hcard⟩ | he
  · exfalso
    have : Finite PSL(2, GaloisField 2 f) := Finite.of_equiv K e.toEquiv
    obtain ⟨T'⟩ := (inferInstance : Nonempty (Sylow 2 PSL(2, GaloisField 2 f)))
    obtain ⟨-, hcard'⟩ := CFSG.Walter.psl2_even_sylow_two (by omega) T'
    have h1 : Nat.card (T : Subgroup K) =
        Nat.card (T' : Subgroup PSL(2, GaloisField 2 f)) := by
      rw [T.card_eq_multiplicity, T'.card_eq_multiplicity, Nat.card_congr e.toEquiv]
    have h2 : 2 ^ 3 ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
    omega
  · exfalso
    have := CFSG.GH74.GLS.Th2.P412.sylow_card_of_nonabelian_bender
      (Or.inl ⟨n, hn, ⟨e⟩⟩) T hΩ
    omega
  · exfalso
    have := CFSG.GH74.GLS.Th2.P412.sylow_card_of_nonabelian_bender
      (Or.inr ⟨f, hf, ⟨e⟩⟩) T hΩ
    omega
  · exact h
  · exfalso
    obtain ⟨u, hu, hu8⟩ := CFSG.ComponentClassification.WalterSchur.ordRee_eq_eight_mul m
    have h8 : Nat.card (T : Subgroup K) = 8 := by
      rw [T.card_eq_multiplicity, hcard, hu8,
        CFSG.ComponentClassification.WalterSchur.factorization_two_eight_mul hu]
      norm_num
    omega
  · exfalso
    obtain ⟨e⟩ := he
    have hc : Nat.card K = 8 * 21945 := by
      rw [Nat.card_congr e.toEquiv,
        CFSG.ComponentClassification.WalterSchur.goldschmidtJ1_eq_walterJ1,
        CFSG.Walter.J1Props.card_walterJ1]
    have h8 : Nat.card (T : Subgroup K) = 8 := by
      rw [T.card_eq_multiplicity, hc,
        CFSG.ComponentClassification.WalterSchur.factorization_two_eight_mul
          (⟨10972, by norm_num⟩ : Odd 21945)]
      norm_num
    omega

end CFSG.OddStandard.SmallF3.Omega
