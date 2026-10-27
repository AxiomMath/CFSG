module

public import CFSG.LocalAnalysis.OddStandard.GH71.S55Comp5LinV
public import CFSG.LocalAnalysis.OddStandard.GH71.S55Comp5Tr
public import CFSG.LocalAnalysis.OddStandard.GH71.S55Comp5Pair
public import CFSG.LocalAnalysis.OddStandard.GH71.S55Comp5InvP
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55StepH3LNoRC

public section

namespace CFSG.OddStandard.GH71.S55

open Subgroup CFSG CFSG.GH74.GLS.Stage2.Signalizer.Ivk8 Matrix
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag C5

theorem comp5_fL3d : Comp5 FL3d := by
  refine comp5_of fun r p Y _ _ hr hr2 hp hp5 hrp hY y g hy hyr hJ => ?_
  have hR := noR_two_of_fl3d_closed hr hr2 hY
  obtain ⟨f, hf, hLM⟩ := hY
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := LinearCover.exists_mulEquiv_projectiveSL_of_lieModel hLM
  have : Fact p.Prime := ⟨hp⟩
  have : Fact r.Prime := ⟨hr⟩
  have : Fintype K := Fintype.ofFinite K
  have : CharP K r :=
    charP_of_card_eq_prime_pow (f := f) (by rw [← Nat.card_eq_fintype_card]; exact hK)
  have h2 : (2 : K) ≠ 0 := StepH3L.two_ne_zero_of_charP hr hr2
  refine comp5Concl_of_mulEquiv e (fun hy' hyr' hJ' => ?_) hy hyr hJ
  by_cases hdiv : p ∣ (r ^ f) ^ 2 + r ^ f + 1
  · exact absurd hJ' (not_pairSL2_of_no_two_p hp (by omega)
      (fun w => orderOf_ne_two_mul_psl3 hp5 h2 hK hdiv w) ((noR_congr e).mp hR) _ _)
  · refine absurd hyr' (not_rFree_of_not_dvd_index
      (flagSpace_ne_bot (n := 3) (K := K) (k := 1) (by norm_num) (by norm_num))
      (flagSpace_ne_top (n := 3) (K := K) (k := 1) (by norm_num)) ?_ hy')
    rw [index_three_one, hK]
    exact hdiv

end CFSG.OddStandard.GH71.S55
