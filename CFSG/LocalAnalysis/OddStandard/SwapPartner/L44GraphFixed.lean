module

public import CFSG.LocalAnalysis.OddStandard.SwapPartner.L44PSU
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotSwapFactorNormalTypes

public section

namespace CFSG.OddStandard.AltStdSec.SwapPartner

open CFSG.LocalAnalysis.ComponentInitial LinearFlag
open CFSG.LocalAnalysis.ComponentInitial.FourGroupEvenCanonical (matrixIsometryGroup)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.UnbalancedCatalog.NonalternatingRadical (radicalGroup
  card_radicalGroup)
open CFSG.Quasithin (perfectCore perfectCore_le)
open CFSG.SeitzReduction.LinearPilot
open CFSG.ClassicalGroups.UnitaryFlag (unitaryPSU)

variable {K : Type} [Field K]

theorem three_thousand_eight_hundred_forty_dvd_card_matrixIsometryGroup_one
    (hK : Nat.card K = 4) :
    3840 ∣ Nat.card (CFSG.LocalAnalysis.ComponentInitial.FourGroupEvenCanonical.matrixIsometryGroup
      (1 : Matrix (Fin 4) (Fin 4) K)) := by
  have hK2 : Nat.card K = 2 ^ 2 := by rw [hK]; norm_num
  haveI : Finite K := finite_of_card_eq_two_pow hK2
  haveI : CharP K 2 := charP_two_of_card_eq_two_pow hK2
  have hev : Even (3 + 1) := ⟨2, rfl⟩
  have hdvd := card_radicalGroup_mul_dvd (F := K) (m := 3) hev
  rw [card_radicalGroup hev (Fin.last 3),
    card_matrixIsometryGroup_one_of_odd (F := K) (n := 3) (r := 1) (by norm_num),
    SymplecticFlag.card_statedSp (K := K) (r := 1), hK2] at hdvd
  refine dvd_trans ?_ hdvd
  decide

theorem three_thousand_eight_hundred_forty_le_card_fixedSubgroup (hK : Nat.card K = 4)
    {θ : MulAut (projectiveSL 4 K)} (hθ : θ * θ = 1) (hθE : θ ∉ semilinearAutGroup 4 K) :
    3840 ≤ Nat.card (fixedSubgroup θ) := by
  have hK2 : Nat.card K = 2 ^ 2 := by rw [hK]; norm_num
  haveI : Finite K := finite_of_card_eq_two_pow hK2
  haveI : CharP K 2 := charP_two_of_card_eq_two_pow hK2
  obtain ⟨A, ρ, ε, hεle, hθeq⟩ :=
    (automorphism_generation (K := K) (n := 4) (by norm_num)).2 θ
  rcases (by omega : ε = 0 ∨ ε = 1) with hε0 | hε1
  ·
    exfalso
    apply hθE
    rw [hθeq, hε0, pow_zero, mul_one]
    exact mem_semilinearAutGroup_iff.mpr ⟨A, ρ, rfl⟩
  · have hθeq' : θ = conjAut 4 K A * fieldAut 4 K ρ * dualAut 4 K := by
      rw [hθeq, hε1, pow_one]
    by_cases hρ : ρ = 1
    ·
      have hθg : (conjAut 4 K A * dualAut 4 K) * (conjAut 4 K A * dualAut 4 K) = 1 := by
        simpa [hθeq', hρ] using hθ
      obtain ⟨C, hC, hcard, -⟩ :=
        card_fixedSubgroup_graph_eq (e := 2) (by norm_num) hK2 (by norm_num : 3 ≤ 4) A hθg
      have hcard' : Nat.card (fixedSubgroup θ) =
          Nat.card (matrixIsometryGroup (C : Matrix (Fin 4) (Fin 4) K)) := by
        rw [hθeq', hρ, map_one, mul_one, hcard]
      rw [hcard']
      rcases hC with hC1 | ⟨r, hr, hJ⟩
      ·
        rw [hC1]
        exact Nat.le_of_dvd Nat.card_pos
          (three_thousand_eight_hundred_forty_dvd_card_matrixIsometryGroup_one hK)
      ·
        have hr2 : r = 2 := by omega
        rw [hJ, hr2,
          card_matrixIsometryGroup_blockSwapJ (F := K) (n := 4) (r := 2) (by norm_num),
          SymplecticFlag.card_statedSp (K := K) (r := 2), hK2]
        decide
    ·
      have hθgf : (conjAut 4 K A * fieldAut 4 K ρ * dualAut 4 K) *
          (conjAut 4 K A * fieldAut 4 K ρ * dualAut 4 K) = 1 := by
        rw [← hθeq']; exact hθ
      obtain ⟨-, h, hcore⟩ :=
        exists_card_perfectCore_graphField (n := 4) (f := 2) (by norm_num) (by norm_num) hK2 A hρ
          hθgf
      have hle : Nat.card (perfectCore (fixedSubgroup θ)) ≤ Nat.card (fixedSubgroup θ) :=
        Subgroup.card_le_of_le (perfectCore_le (fixedSubgroup θ))
      calc
        3840 ≤ 25920 := by norm_num
        _ = Nat.card (unitaryPSU h 4) := (card_unitaryPSU_four_two (by norm_num) h).symm
        _ = Nat.card (perfectCore
              (fixedSubgroup (conjAut 4 K A * fieldAut 4 K ρ * dualAut 4 K))) := hcore.symm
        _ = Nat.card (perfectCore (fixedSubgroup θ)) := by rw [hθeq']
        _ ≤ Nat.card (fixedSubgroup θ) := hle

end CFSG.OddStandard.AltStdSec.SwapPartner
