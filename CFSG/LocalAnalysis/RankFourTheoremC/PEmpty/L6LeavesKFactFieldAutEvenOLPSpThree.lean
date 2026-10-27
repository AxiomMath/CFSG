module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFactFieldAutEvenSplit
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFactFieldAutEvenOLThreeAdic
public import CFSG.Monster.B.TwoA.Census.PermClasses

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

namespace KFAE

open CFSG.Open (StatedLieTag StatedLieAdmissible StatedClassicalModel StatedProj StatedSp)
open CFSG.Blueprint (LieModel)
open CFSG.ComponentClassification.CatLeaf (lieOrderNumerator lieOrderDivisor)

namespace OLThreeAdic

theorem four_le_padicValNat_numerator_PSp_three :
    4 ≤ padicValNat 3 (lieOrderNumerator .PSp 3 (2 ^ 1)) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h : lieOrderNumerator .PSp 3 (2 ^ 1) = 2 ^ 9 * (3 * 15 * 63) := by decide
  have hne : lieOrderNumerator .PSp 3 (2 ^ 1) ≠ 0 := by rw [h]; norm_num
  exact (padicValNat_dvd_iff_le hne).mp (by rw [h]; norm_num)

end OLThreeAdic

theorem twoLocalWhen_PSp_three : TwoLocalWhen .PSp (fun n f₀ => n = 3 ∧ f₀ = 1) := by
  intro K _ _ hs hab n f f₀ p hP hadm hmodel ht hp hp5 hpK hdiv hf
  obtain ⟨rfl, rfl⟩ := hP
  have hcl0 : StatedClassicalModel K .PSp 3 2 f := by
    rcases hmodel with ⟨-, hcl⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩
    · exact hcl
    · exact absurd ht (by decide)
    · exact absurd ht (by decide)
    · exact absurd ht (by decide)
  have hfp : f = p := by rw [hf, mul_one]
  have hp6 := OLThreeAdic.prime_mod_six hp hp5
  obtain ⟨-, F, hF, hFfin, hFcard, ⟨e⟩⟩ := hcl0
  haveI : Fintype F := Fintype.ofFinite F
  have hFcard' : Fintype.card F = 2 ^ f := by rw [← Nat.card_eq_fintype_card]; exact hFcard
  haveI : CharP F 2 := charP_of_card_eq_prime_pow hFcard'
  have hfin : Fintype.card (Fin 3 ⊕ Fin 3) = 6 := by
    rw [Fintype.card_sum, Fintype.card_fin]
  refine ⟨3, Nat.prime_three, fun R hR2 hR1 => ?_⟩
  have hle := OLThreeAdic.padicValNat_three_card_normalizer_le_of_equiv (ι := Fin 3 ⊕ Fin 3)
    hfin (by rw [hFcard, hfp]) hp6 e R hR2 hR1
  have hd : lieOrderDivisor .PSp 3 (2 ^ 1) = 1 := by decide
  have h4 := OLThreeAdic.four_le_padicValNat_numerator_PSp_three
  rw [hd, padicValNat.one]
  omega

theorem overgroupLocalWhen_PSp_three (hOver : CFSG.Quasithin.AsLieTwoOvergroups) :
    OvergroupLocalWhen .PSp (fun n f₀ => n = 3 ∧ f₀ = 1) :=
  overgroupLocalWhen_of_twoLocalWhen hOver twoLocalWhen_PSp_three

end KFAE

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty
