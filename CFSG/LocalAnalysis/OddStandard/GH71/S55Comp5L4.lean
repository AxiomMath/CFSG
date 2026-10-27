module

public import CFSG.LocalAnalysis.OddStandard.GH71.S55Comp5LinV
public import CFSG.LocalAnalysis.OddStandard.GH71.S55Comp5L4Sp
public import CFSG.LocalAnalysis.OddStandard.GH71.S55Comp5Tr
public import CFSG.LocalAnalysis.OddStandard.GH71.S55Comp5Arith
public import CFSG.LocalAnalysis.OddStandard.GH71.S55Comp5Typ

public section

namespace CFSG.OddStandard.GH71.S55

open Subgroup CFSG CFSG.GH74.GLS.Stage2.Signalizer.Ivk8 Matrix
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag C5

theorem comp5_fL4d : Comp5 FL4d := by
  refine comp5_of fun r p Y _ _ hr hr2 hp hp5 hrp hY y g hy hyr hJ => ?_
  obtain ⟨f, hf, -, hLM⟩ := hY
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := LinearCover.exists_mulEquiv_projectiveSL_of_lieModel hLM
  have : Fact p.Prime := ⟨hp⟩
  have : Fact r.Prime := ⟨hr⟩
  have : Fintype K := Fintype.ofFinite K
  have : CharP K r :=
    charP_of_card_eq_prime_pow (f := f) (by rw [← Nat.card_eq_fintype_card]; exact hK)
  refine comp5Concl_of_mulEquiv e (fun hy' hyr' _ => ?_) hy hyr hJ
  have hq : 1 ≤ r ^ f := Nat.one_le_pow _ _ hr.pos
  by_cases h1 : p ∣ (r ^ f + 1) * ((r ^ f) ^ 2 + 1)
  · by_cases h2 : p ∣ ((r ^ f) ^ 2 + 1) * ((r ^ f) ^ 2 + r ^ f + 1)
    · have h4 : p ∣ (r ^ f) ^ 2 + 1 := by
        rcases hp.dvd_mul.mp h1 with h | h
        · rcases hp.dvd_mul.mp h2 with h' | h'
          · exact h'
          · exact absurd h' (cyc2_excl hp5 hq h).2.2.1
        · exact h
      obtain ⟨hq0, hq1, -, hq3, -, -⟩ := cyc4_excl hp5 hq h4
      have hidx : ¬ p ∣ ((proj 4 K).comp (spSL (K := K))).range.index := by
        intro hd
        have hd' := hd.trans (index_range_projSp_dvd (K := K))
        rw [hK, show (r ^ f) ^ 3 - 1 = (r ^ f - 1) * ((r ^ f) ^ 2 + r ^ f + 1) by
          zify [hq, Nat.one_le_pow 3 _ (by omega : 0 < r ^ f)]
          ring] at hd'
        rcases hp.dvd_mul.mp hd' with h | h
        · exact hq0 (hp.dvd_of_dvd_pow h)
        · rcases hp.dvd_mul.mp h with h | h
          · exact hq1 h
          · exact hq3 h
      obtain ⟨hQ, hC, hrL⟩ := typ_psp4 hr hr2 hf hK projSpEquiv
      exact comp5Concl_of_block hidx le_normalizer range_projSp_ne_top hQ hC hrL hy' hyr'
    · refine absurd hyr' (not_rFree_of_not_dvd_index
        (flagSpace_ne_bot (n := 4) (K := K) (k := 2) (by norm_num) (by norm_num))
        (flagSpace_ne_top (n := 4) (K := K) (k := 2) (by norm_num)) ?_ hy')
      rw [index_four_two, hK]
      exact h2
  · refine absurd hyr' (not_rFree_of_not_dvd_index
      (flagSpace_ne_bot (n := 4) (K := K) (k := 1) (by norm_num) (by norm_num))
      (flagSpace_ne_top (n := 4) (K := K) (k := 1) (by norm_num)) ?_ hy')
    rw [index_four_one, hK]
    exact h1

end CFSG.OddStandard.GH71.S55
