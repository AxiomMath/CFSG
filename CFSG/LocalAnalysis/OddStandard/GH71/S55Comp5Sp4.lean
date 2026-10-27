module

public import CFSG.LocalAnalysis.OddStandard.GH71.S55Comp5Sp4A
public import CFSG.LocalAnalysis.OddStandard.GH71.S55Comp5Sp4B
public import CFSG.LocalAnalysis.OddStandard.GH71.S55Comp5Tr
public import CFSG.LocalAnalysis.OddStandard.GH71.S55Comp5Arith

public section

namespace CFSG.OddStandard.GH71.S55

open Subgroup CFSG CFSG.GH74.GLS.Stage2.Signalizer.Ivk8 Matrix CFSG.Assembly.LowTwoRank
  CFSG.Blueprint CFSG.ClassicalInvolution.Models.SymplecticPairs C5
open scoped MatrixGroups

namespace C5

theorem exists_model_psp {Y : Type} [Group Y] {r f : ℕ} (h : LieModel Y .PSp 2 r f) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = r ^ f ∧
      Nonempty (Y ≃* StatedProj (StatedSp 2 K)) := by
  rcases h with ⟨-, -, h⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩
  · exact h
  all_goals exact absurd h (by norm_num)

end C5

theorem comp5_fSp4d : Comp5 FSp4d := by
  refine comp5_of fun r p Y _ _ hr hr2 hp hp5 hrp hY y g hy hyr hJ => ?_
  obtain ⟨f, hf, hLM⟩ := hY
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := exists_model_psp hLM
  have : Fact p.Prime := ⟨hp⟩
  have : Fact r.Prime := ⟨hr⟩
  refine comp5Concl_of_mulEquiv e (fun hy' hyr' _ => ?_) hy hyr hJ
  have hq : 1 ≤ r ^ f := Nat.one_le_pow _ _ hr.pos
  have hpq : ¬ p ∣ r ^ f := not_dvd_pow hp hr hrp
  have h3 := three_le_pow (f := f) hr hr2 hf
  by_cases h1 : p ∣ (r ^ f) ^ 2 * ((r ^ f) ^ 2 + 1)
  · have h4 : p ∣ (r ^ f) ^ 2 + 1 :=
      (hp.dvd_mul.mp h1).resolve_left (fun h => hpq (hp.dvd_of_dvd_pow h))
    obtain ⟨hq0, hq1, hq2, -, -, -⟩ := cyc4_excl hp5 hq h4
    obtain ⟨L, hLt, hQ, hC, hrL, hidx⟩ := exists_psl2_block hr hr2 hf hK
    refine comp5Concl_of_block (M := L) ?_ le_normalizer hLt hQ hC hrL hy' hyr'
    intro hd
    have hd' := hd.trans hidx
    rw [show (r ^ f) ^ 2 - 1 = (r ^ f + 1) * (r ^ f - 1) by
      simpa using Nat.pow_two_sub_pow_two (r ^ f) 1] at hd'
    rcases hp.dvd_mul.mp hd' with h | h
    · exact absurd (Nat.le_of_dvd two_pos h) (by omega)
    · rcases hp.dvd_mul.mp h with h | h
      · exact hq0 (hp.dvd_of_dvd_pow h)
      · rcases hp.dvd_mul.mp h with h | h
        · exact hq2 h
        · exact hq1 h
  · set φ := CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.proj 2 K with hφdef
    have hφs : Function.Surjective φ := QuotientGroup.mk'_surjective _
    set q := r ^ f with hqdef
    have hSp : Nat.card (StatedSp 2 K) = q ^ 4 * ((q ^ 2 - 1) * (q ^ 4 - 1)) := by
      rw [CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.card_statedSp (K := K) 2, hK,
        show Finset.Icc 1 2 = {1, 2} by decide, Finset.prod_pair (by norm_num)]
      norm_num
    have hY := Subgroup.card_eq_card_quotient_mul_card_subgroup
      ((StatedScalars (Fin 2 ⊕ Fin 2) K).subgroupOf (StatedSp 2 K))
    have e4 : q ^ 4 - 1 = (q ^ 2 - 1) * (q ^ 2 + 1) := by
      zify [Nat.one_le_pow 4 q (by omega), Nat.one_le_pow 2 q (by omega)]
      ring
    have hpY : p ∣ q ^ 4 * ((q ^ 2 - 1) * ((q ^ 2 - 1) * (q ^ 2 + 1))) := by
      rw [← e4, ← hSp, hY]
      exact (hy' ▸ orderOf_dvd_natCard (e y)).trans (dvd_mul_right _ _)
    have hp21 : p ∣ q ^ 2 - 1 := by
      rcases hp.dvd_mul.mp hpY with h | h
      · exact absurd (hp.dvd_of_dvd_pow h) hpq
      · rcases hp.dvd_mul.mp h with h | h
        · exact h
        · rcases hp.dvd_mul.mp h with h | h
          · exact h
          · exact absurd (dvd_mul_of_dvd_right h _) h1
    have hq3 : q ≠ 3 := by
      intro h
      rw [h, show (3 : ℕ) ^ 2 - 1 = 2 ^ 3 by norm_num] at hp21
      exact absurd (Nat.le_of_dvd (by norm_num) (hp.dvd_of_dvd_pow hp21)) (by omega)
    set L := (φ.comp (longBlock K 2 0)).range with hLdef
    let eL : SL(2, K) ≃* ↥L := MonoidHom.ofInjective projSp_longBlock_injective
    obtain ⟨hQ, hC, hrL⟩ := typ_sl hr hr2 hf (Or.inl rfl) hK (Or.inr hq3) eL
    have hML : (blockPair (K := K)).range.map φ ≤
        normalizer (L : Set (StatedProj (StatedSp 2 K))) := by
      rw [hLdef, MonoidHom.range_comp]
      exact (map_mono range_blockPair_le_normalizer).trans (le_normalizer_map φ)
    have hM : ¬ p ∣ ((blockPair (K := K)).range.map φ).index := by
      intro hd
      have := hd.trans (Subgroup.index_map_dvd _ hφs)
      rw [index_range_blockPair, hK] at this
      exact h1 this
    have hLt : L ≠ ⊤ := by
      intro htop
      have hcL : Nat.card ↥L = q * (q ^ 2 - 1) := by
        rw [← Nat.card_congr eL.toEquiv,
          CFSG.LocalAnalysis.ComponentInitial.LinearFlag.card_SL_eq (by norm_num), hK]
        rw [show Finset.Icc 2 2 = {2} from Finset.Icc_self 2, Finset.prod_singleton]
        norm_num
      have hcY : Nat.card ↥L = Nat.card (StatedProj (StatedSp 2 K)) := by
        rw [htop, Subgroup.card_top]
      have hZ := card_scalars_subgroupOf_le (K := K) (StatedSp 2 K)
      rw [hK] at hZ
      rw [← hcY, hcL, hSp] at hY
      have hA : 0 < q ^ 2 - 1 := Nat.sub_pos_of_lt (Nat.one_lt_pow two_ne_zero (by omega))
      have hB : 0 < q ^ 4 - 1 := Nat.sub_pos_of_lt (Nat.one_lt_pow (by norm_num) (by omega))
      generalize q ^ 2 - 1 = A at hY hA
      generalize q ^ 4 - 1 = B at hY hB
      have : q * A * (q - 1) < q ^ 4 * (A * B) := by
        have hq1 : q - 1 < q ^ 3 * B := by
          have h1' : q ≤ q ^ 3 := Nat.le_self_pow (by norm_num) q
          have h2' : q ^ 3 ≤ q ^ 3 * B := Nat.le_mul_of_pos_right _ hB
          omega
        calc q * A * (q - 1) < q * A * (q ^ 3 * B) :=
              Nat.mul_lt_mul_of_pos_left hq1 (by positivity)
          _ = q ^ 4 * (A * B) := by ring
      have := Nat.mul_le_mul_left (q * A) hZ
      omega
    exact comp5Concl_of_block hM hML hLt hQ hC hrL hy' hyr'

end CFSG.OddStandard.GH71.S55
