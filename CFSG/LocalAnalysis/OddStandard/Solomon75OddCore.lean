module

public import CFSG.LocalAnalysis.OddStandard.Solomon75CoreEndgame
public import CFSG.LocalAnalysis.OddStandard.Solomon75GH71McL
public import CFSG.Milestones.CL_LIT_Aschbacher_proper_two_generated_core

public section

namespace CFSG.OddStandard.Solomon75

open Subgroup CFSG CFSG.GH74.GLS

section Aschbacher


theorem aschbacherProperTwoGeneratedCore : ClassicalInvolution.AschbacherProperTwoGeneratedCore :=
  fun G _ _ _ hnonab S hrank hcore =>
    Milestones.cl_lit_aschbacher_proper_two_generated_core G hnonab S hrank hcore

theorem solomon44OddCore_of_data {n : ℕ} (hn : 8 ≤ n) (hn10 : n ≤ 10) (hD : CoverSylowData n)
    (hB : AlternatingBalanceData n) : Solomon44OddCore n :=
  solomon44OddCore_of_balanced aschbacherProperTwoGeneratedCore hn hn10 hD hB

theorem solomon44OddCore_eight_of_data (hD : CoverSylowData 8) (hB : AlternatingBalanceData 8) :
    Solomon44OddCore 8 :=
  solomon44OddCore_of_data (by norm_num) (by norm_num) hD hB

theorem solomon44OddCore_nine_of_data (hD : CoverSylowData 9) (hB : AlternatingBalanceData 9) :
    Solomon44OddCore 9 :=
  solomon44OddCore_of_data (by norm_num) (by norm_num) hD hB

theorem solomon44OddCore_ten_of_data (hD : CoverSylowData 10) (hB : AlternatingBalanceData 10) :
    Solomon44OddCore 10 :=
  solomon44OddCore_of_data (by norm_num) (by norm_num) hD hB

theorem oddCore_eleven_eq_bot_of_data (hD : CoverSylowData 11)
    (hB : AlternatingBalanceData 11) {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) {t : G} (ht : orderOf t = 2)
    (hcov : IsDoubleCoverOfAlt (CentQuot t) 11)
    (h3 : ¬ 3 ∣ Nat.card (pPrimeCore 2 ↥(centralizer ({t} : Set G)))) :
    pPrimeCore 2 ↥(centralizer ({t} : Set G)) = ⊥ :=
  oddCore_eleven_eq_bot_of_not_three_dvd
    aschbacherProperTwoGeneratedCore hD hB hnonab ht hcov h3


theorem solomon44McL_of_data (hD : CoverSylowData 8) (hB : AlternatingBalanceData 8) :
    Solomon44McL :=
  solomon44McL_of_oddCore (solomon44OddCore_eight_of_data hD hB)

end Aschbacher

end CFSG.OddStandard.Solomon75
