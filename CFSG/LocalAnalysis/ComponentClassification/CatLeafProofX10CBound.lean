module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofX10CVal
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB81Frontier
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB81Z
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsTransport

public section

namespace CFSG.ComponentClassification.CatLeafProof.X10CB

theorem lte_facts {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f) :
    padicValNat 2 (p ^ (4 * f) - 1) = padicValNat 2 (p ^ (2 * f) - 1) + 1 ∧
      padicValNat 2 (2 * f) = padicValNat 2 f + 1 ∧
      padicValNat 2 f + 3 ≤ padicValNat 2 (p ^ (2 * f) - 1) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hodd : ¬ 2 ∣ p := fun h => hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp h).symm
  have hp3 : 1 < p := hp.one_lt
  have hp1 : 2 ∣ p - 1 := by omega
  have h2f : padicValNat 2 (2 * f) = padicValNat 2 f + 1 := by
    rw [padicValNat.mul (by norm_num) (by omega), padicValNat_self, add_comm]
  have h4f : padicValNat 2 (4 * f) = padicValNat 2 f + 2 := by
    rw [padicValNat.mul (by norm_num) (by omega),
      show (4 : ℕ) = 2 ^ 2 by norm_num, padicValNat.prime_pow, add_comm]
  have l2 := padicValNat.pow_two_sub_pow hp3 hp1 hodd (n := 2 * f) (by omega) (even_two_mul f)
  have l4 := padicValNat.pow_two_sub_pow hp3 hp1 hodd (n := 4 * f) (by omega)
    ⟨2 * f, by ring⟩
  rw [one_pow] at l2 l4
  have h8 : 8 ∣ (p + 1) * (p - 1) := by
    obtain ⟨m, rfl⟩ := hp.odd_of_ne_two hp2
    have e1 : (2 * m + 1 + 1) * (2 * m + 1 - 1) = 4 * (m * (m + 1)) := by
      rw [Nat.add_sub_cancel]
      ring
    rw [e1]
    obtain ⟨k, hk⟩ := Nat.even_mul_succ_self m
    rw [hk]
    exact ⟨k, by ring⟩
  have h3 : 3 ≤ padicValNat 2 (p + 1) + padicValNat 2 (p - 1) := by
    rw [← padicValNat.mul (by omega) (by omega)]
    exact (padicValNat_dvd_iff_le (Nat.mul_ne_zero (by omega) (by omega))).mp
      (by simpa using h8)
  refine ⟨by omega, h2f, by omega⟩

end CFSG.ComponentClassification.CatLeafProof.X10CB

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer CatLeafProof

namespace Hyp59

variable {H : Type} [Group H] [Finite H] {h : Hyp59 H}

namespace L81Hyp

variable {H₁ : h.L81Hyp}

namespace Data

variable {d : Data H₁} {v : H}

theorem nu_card_H_le (I : In81) (hst : d.Stage7 v) {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hf : 1 ≤ f) (hJ : Blueprint.LieModel (h.J ⧸ pPrimeCore 2 h.J) .PSL 2 p (2 * f)) :
    padicValNat 2 (Nat.card H) ≤ 2 * padicValNat 2 (p ^ (4 * f) - 1) + padicValNat 2 (2 * f) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨T, hT⟩ :=
    isSylow_U hst.isV I.rk I.sy I.b1 I.b6 I.cf23 I.cf24 I.cfc I.cf1 I.cf2 I.c hst.facts
  have hHU : padicValNat 2 (Nat.card H) = padicValNat 2 (Nat.card (h.U81 v)) := by
    rw [← hT, Sylow.card_eq_multiplicity, padicValNat.prime_pow,
      Nat.factorization_def _ Nat.prime_two]
  have hUS : padicValNat 2 (Nat.card (h.U81 v)) ≤ padicValNat 2 (Nat.card h.S) + 1 := by
    have hle : Nat.card (h.U81 v) ≤ 2 * Nat.card h.S := by
      let g : h.S × Bool → h.U81 v := fun x => cond x.2
        ⟨(x.1 : H) * v, mul_mem (mem_sup_left x.1.2) (mem_sup_right (mem_zpowers v))⟩
        ⟨(x.1 : H), mem_sup_left x.1.2⟩
      have hg : Function.Surjective g := by
        rintro ⟨u, hu⟩
        rcases mem_U_cases hst.isV hu with hS | ⟨s, hs, rfl⟩
        · exact ⟨(⟨u, hS⟩, false), rfl⟩
        · exact ⟨(⟨s, hs⟩, true), rfl⟩
      calc Nat.card (h.U81 v) ≤ Nat.card (h.S × Bool) := Nat.card_le_card_of_surjective g hg
        _ = 2 * Nat.card h.S := by
          rw [Nat.card_prod, Nat.card_eq_fintype_card (α := Bool), Fintype.card_bool, mul_comm]
    obtain ⟨a, ha⟩ := (isPGroup_U hst.isV).exists_card_eq
    obtain ⟨b, hb⟩ := h.toHyp52.isPGroup_S.exists_card_eq
    rw [ha, hb] at hle ⊢
    rw [padicValNat.prime_pow, padicValNat.prime_pow]
    have h1 : 2 ^ a ≤ 2 ^ (b + 1) := by rw [pow_succ]; omega
    exact (pow_le_pow_iff_right₀ (by norm_num : (1 : ℕ) < 2)).mp h1
  have hSN : h.S ≤ normalizer (h.J : Set H) := h.S_le.trans inf_le_right
  have hS := Seven.card_eq_card_rhoImg_mul hSN
  have hPD : Nat.card (h.S ⊓ coreActionKernel h.J : Subgroup H) = Nat.card h.D := hst.card_P
  rw [hPD] at hS
  obtain ⟨-, -, -, -, F, _, _, hF, ⟨e⟩⟩ := AutL2Facts.lieModel_psl2_data hJ
  have hoddF : GorensteinWalter.IsOddPrimePower (Nat.card F) :=
    AutL2Facts.isOddPrimePower_of hp hp2 (by omega) hF
  set q := p ^ (2 * f) with hq
  have hq2 : ¬ 2 ∣ q := fun h2 => hp2
    ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp (Nat.prime_two.dvd_of_dvd_pow h2)).symm
  have hq1 : 1 < q := Nat.one_lt_pow (by omega) hp.one_lt
  have hqq : q ^ 2 - 1 ≠ 0 := by
    have : 1 < q ^ 2 := Nat.one_lt_pow (by norm_num) hq1
    omega
  have hA0 : q * (q ^ 2 - 1) ≠ 0 := Nat.mul_ne_zero (by omega) hqq
  have hvA : padicValNat 2 (q * (q ^ 2 - 1)) = padicValNat 2 (q ^ 2 - 1) := by
    rw [padicValNat.mul (by omega) hqq, padicValNat.eq_zero_of_not_dvd hq2, zero_add]
  have hAut : Nat.card (MulAut (↥h.J ⧸ pPrimeCore 2 ↥h.J)) = q * (q ^ 2 - 1) * (2 * f) := by
    rw [Nat.card_congr (AutL2Facts.autEquiv e).toEquiv, SemidirectProduct.card,
      GorensteinWalter.pgl2_card_formula, hF]
    congr 1
    exact (LocalAnalysis.ComponentInitial.card_ringAut_and_isCyclic hp F hF).1
  have hrho : padicValNat 2 (Nat.card (Seven.rhoImg h.J h.S)) ≤
      padicValNat 2 (q ^ 2 - 1) + padicValNat 2 (2 * f) := by
    have h1 := X10CV.padicValNat_le_of_dvd' 2 Nat.card_pos.ne'
      (card_subgroup_dvd_card (Seven.rhoImg h.J h.S))
    rwa [hAut, padicValNat.mul hA0 (by omega), hvA] at h1
  have hJbar : 2 * Nat.card (↥h.J ⧸ pPrimeCore 2 ↥h.J) = q * (q ^ 2 - 1) := by
    rw [Nat.card_congr e.toEquiv, GorensteinWalter.psl2_card_formula F hoddF, hF]
    refine Nat.mul_div_cancel' ?_
    have h1 : 2 ∣ q ^ 2 - 1 := by
      have : ¬ 2 ∣ q ^ 2 := fun h2 => hq2 (Nat.prime_two.dvd_of_dvd_pow h2)
      omega
    exact h1.mul_left q
  have hvJbar : padicValNat 2 (Nat.card (↥h.J ⧸ pPrimeCore 2 ↥h.J)) + 1 =
      padicValNat 2 (q ^ 2 - 1) := by
    have h1 := congrArg (padicValNat 2) hJbar
    rw [padicValNat.mul (by norm_num) Nat.card_pos.ne', padicValNat_self, hvA] at h1
    omega
  have hvJ : padicValNat 2 (Nat.card h.J) =
      padicValNat 2 (Nat.card (↥h.J ⧸ pPrimeCore 2 ↥h.J)) := by
    rw [card_eq_card_quotient_mul_card_subgroup (pPrimeCore 2 ↥h.J),
      padicValNat.mul Nat.card_pos.ne' Nat.card_pos.ne',
      padicValNat.eq_zero_of_not_dvd (Nat.not_even_iff_odd.mpr OddQuot.odd_card_pPrimeCore ∘
        even_iff_two_dvd.mpr), add_zero]
  have hD : padicValNat 2 (Nat.card h.D) ≤ padicValNat 2 (Nat.card h.J) :=
    X10CV.nu_le_of_le 2 inf_le_right
  have hS' := congrArg (padicValNat 2) hS
  rw [padicValNat.mul Nat.card_pos.ne' Nat.card_pos.ne'] at hS'
  have hq4 : q ^ 2 = p ^ (4 * f) := by rw [hq, ← pow_mul]; ring_nf
  rw [hq4] at hrho hvJbar
  omega

theorem nu_card_H_le' (I : In81) (hst : d.Stage7 v) {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hf : 1 ≤ f) (hJ : Blueprint.LieModel (h.J ⧸ pPrimeCore 2 h.J) .PSL 2 p (2 * f)) :
    padicValNat 2 (Nat.card H) ≤
      2 * padicValNat 2 (p ^ (2 * f) - 1) + padicValNat 2 f + 3 := by
  have h1 := nu_card_H_le I hst hp hp2 hf hJ
  obtain ⟨h4, h2, -⟩ := X10CB.lte_facts hp hp2 hf
  omega

end Data

end L81Hyp

end Hyp59

end CFSG.ComponentClassification.GSThmB
