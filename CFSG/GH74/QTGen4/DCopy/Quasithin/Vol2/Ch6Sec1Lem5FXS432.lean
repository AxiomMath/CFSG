module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch6Sec1Lem5FW
public import CFSG.Quasithin.EmptyFaithful.R3c2Types
public import CFSG.Quasithin.Vol2.Ch6Sec1Lem5FP
public import CFSG.Quasithin.Vol2.Ch6Sec1Lem5FU
public import CFSG.Quasithin.Vol2.Ch6Sec1Lem5FV

public section
namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.Quasithin
open CFSG.LieType.BorelTits

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T M L V H : Subgroup G} {n : ℕ}


namespace Cx615C

theorem exists_of_b56Case1_ch615_F4 (h432 : Stmt4_3_2_F4) (c : Cx615C G T M L V H n)
    (hU : IsElemAbelian 2 (UX615 T L H))
    (hN : ¬ borelL T L ≤ Subgroup.normalizer ((kStar615 T L H : Subgroup G) : Set G))
    (h1 : B56Case1 (ffJ (autI hU (borelL T L ⊔ H))))
    (hA7 : IsAlt 7 ↥(quasithinGenFitting (ffJ (autI hU (borelL T L ⊔ H)))) →
      fixV (quasithinGenFitting (ffJ (autI hU (borelL T L ⊔ H)))) = ⊥ →
      ∃ z ∈ quasithinOmegaOneCenter T ⊓ ⁅UX615 T L H, borelL T L ⊔ H⁆,
        z ≠ 1 ∧ (∃ d ∈ borelL T L, Odd (orderOf d) ∧ d ≠ 1 ∧ d * z * d⁻¹ = z) ∧
        ¬ (borelL T L ⊔ H) ⊓ Subgroup.centralizer ({z} : Set G) ≤
          Subgroup.normalizer ((borelL T L : Subgroup G) : Set G))
    (hHat : IsHat ↥(quasithinGenFitting (ffJ (autI hU (borelL T L ⊔ H))))
        ↥(alternatingGroup (Fin 6)) →
      ∃ z ∈ quasithinOmegaOneCenter T ⊓ ⁅UX615 T L H, borelL T L ⊔ H⁆,
        z ≠ 1 ∧ (∃ d ∈ borelL T L, Odd (orderOf d) ∧ d ≠ 1 ∧ d * z * d⁻¹ = z) ∧
        ¬ (borelL T L ⊔ H) ⊓ Subgroup.centralizer ({z} : Set G) ≤
          Subgroup.normalizer ((borelL T L : Subgroup G) : Set G)) :
    ∃ z ∈ quasithinOmegaOneCenter T ⊓ ⁅UX615 T L H, borelL T L ⊔ H⁆,
      z ≠ 1 ∧ (∃ d ∈ borelL T L, Odd (orderOf d) ∧ d ≠ 1 ∧ d * z * d⁻¹ = z) ∧
      ¬ (borelL T L ⊔ H) ⊓ Subgroup.centralizer ({z} : Set G) ≤
        Subgroup.normalizer ((borelL T L : Subgroup G) : Set G) := by
  have hq := h1.1
  rcases h1.2.2 with ⟨m, K, _, _, hK, ⟨e⟩⟩ | ⟨m, K, _, _, hK, ⟨e⟩⟩ | ⟨m, K, _, _, hK, ⟨e⟩⟩ |
    ⟨m, K, _, _, hK, ⟨e⟩⟩ | h6 | h7 | hh | ⟨K, _, _, hK, ⟨e⟩⟩ | h4 | h5
  ·
    exfalso
    have hm := EmptyFaithfulMultiple.FFL.one_le_of_card hK
    rcases (by omega : m = 1 ∨ m = 2 ∨ m = 3 ∨ 4 ≤ m) with rfl | rfl | rfl | hm4
    · refine G64.not_isQuasisimple_of_card_six ?_ hq
      rw [Nat.card_congr e.toEquiv, card_statedSL_two1527d, hK]
      norm_num
    · exact c.false_of_case1_sl2_four_ch615 hU hN h1 hK e
    · exact c.false_of_case1_sl2_eight_ch615 hU h1 hK e
    · exact c.false_of_case1_sl2_ch615 hU h1 hm4 hK e
  ·
    exfalso
    have hm := EmptyFaithfulMultiple.FFL.one_le_of_card hK
    rcases (by omega : m = 1 ∨ 2 ≤ m) with rfl | hm2
    · have hK2 : Nat.card K = 2 := by simpa using hK
      by_cases hfix : fixV (quasithinGenFitting (ffJ (autI hU (borelL T L ⊔ H)))) = ⊥
      · exact c.false_of_case1_l32_nofix_ch615 hU hN h1 hK2 e hfix
      · exact c.false_of_case1_l32_fix_ch615_F4 h432 hU hN hK2 e hfix
    · exact c.false_of_case1_sl3_ch615 hU h1 hm2 hK e
  ·
    exfalso
    have hm := EmptyFaithfulMultiple.FFL.one_le_of_card hK
    rcases (by omega : m = 1 ∨ 2 ≤ m) with rfl | hm2
    · exact R3c2.not_isQuasisimple_statedSp_two (by simpa using hK) e hq
    · exact c.false_of_case1_sp4_ch615 hU h1 hm2 hK e
  ·
    exfalso
    have hm := EmptyFaithfulMultiple.FFL.one_le_of_card hK
    rcases (by omega : m = 1 ∨ 2 ≤ m) with rfl | hm2
    · exact R3c2.not_isQuasisimple_quasithinG2_two (by simpa using hK) e hq
    · exact c.false_of_case1_g2_ch615 hU h1 hm2 hK e
  ·
    exfalso
    obtain ⟨e⟩ := h6
    by_cases hfix : fixV (quasithinGenFitting (ffJ (autI hU (borelL T L ⊔ H)))) = ⊥
    · exact c.false_of_case1_alt_six_nofix_ch615 hU hN h1 e hfix
    · exact c.false_of_case1_alt_six_fix_ch615_F4 h432 hU hN e hfix
  ·
    by_cases hfix : fixV (quasithinGenFitting (ffJ (autI hU (borelL T L ⊔ H)))) = ⊥
    · exact hA7 h7 hfix
    · obtain ⟨e⟩ := h7
      exact (c.false_of_case1_alt_seven_fix_ch615_F4 h432 hU hN hq e hfix).elim
  ·
    exact hHat hh
  ·
    exfalso
    by_cases hfix : fixV (quasithinGenFitting (ffJ (autI hU (borelL T L ⊔ H)))) = ⊥
    · exact c.false_of_case1_g2two_nofix_ch615 hU hN h1 hK e hfix
    · exact c.false_of_case1_g2two_fix_ch615_F4 h432 hU hN hK e hfix
  ·
    exfalso
    obtain ⟨e⟩ := h4
    by_cases hfix : fixV (quasithinGenFitting (ffJ (autI hU (borelL T L ⊔ H)))) = ⊥
    · exact c.false_of_case1_l42_nofix_ch615 hU hN h1 e hfix
    · exact c.false_of_case1_binary_linear_fix_ch615_F4 h432 hU hN hq (by norm_num) e hfix
  ·
    exfalso
    obtain ⟨e⟩ := h5
    exact c.false_of_case1_l52_ch615 hU hN hq e

end Cx615C

end CFSG.Quasithin.H13
