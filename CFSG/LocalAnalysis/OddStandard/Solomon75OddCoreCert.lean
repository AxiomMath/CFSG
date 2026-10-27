module

public import CFSG.LocalAnalysis.OddStandard.Solomon75AhatDataMain
public import CFSG.LocalAnalysis.OddStandard.Solomon75OddCore

public section

namespace CFSG.OddStandard.Solomon75

open Subgroup CFSG CFSG.GH74.GLS

section Aschbacher

theorem solomon44OddCore_nine_of_certificate :
    Solomon44OddCore 9 :=
  solomon44OddCore_nine_of_data coverSylowData_nine_of_certificate
    alternatingBalanceData_nine_of_certificate

theorem solomon44OddCore_ten_of_certificate :
    Solomon44OddCore 10 :=
  solomon44OddCore_ten_of_data coverSylowData_ten_of_certificate
    alternatingBalanceData_ten_of_certificate

theorem oddCore_eleven_eq_bot_of_certificate {G : Type}
    [Group G] [Finite G] [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a) {t : G}
    (ht : orderOf t = 2) (hcov : IsDoubleCoverOfAlt (CentQuot t) 11)
    (h3 : ¬ 3 ∣ Nat.card (pPrimeCore 2 ↥(centralizer ({t} : Set G)))) :
    pPrimeCore 2 ↥(centralizer ({t} : Set G)) = ⊥ :=
  oddCore_eleven_eq_bot_of_data coverSylowData_eleven_of_certificate
    alternatingBalanceData_eleven_of_certificate hnonab ht hcov h3

theorem solomon44McL_of_certificate : Solomon44McL :=
  solomon44McL_of_data coverSylowData_eight_of_certificate
    alternatingBalanceData_eight_of_certificate

end Aschbacher

end CFSG.OddStandard.Solomon75
