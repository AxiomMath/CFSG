module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5SStdOrder
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Thm11Inputs
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.L3Rank
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitFixedSimple
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5SStdInputs

public section

namespace CFSG.ComponentClassification.GrSLit.L34Sec5S

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer CFSG.Assembly.LowTwoRank
open CFSG.EvenSporadicStandard.Induction (SolStd Sol78Thm46 Sol78Remark11 Sol78Thm11SuzONan
  EmbedsInPair)

variable {G : Type} [Group G] [Finite G]

theorem pRank_two_le_of_le {T M : Subgroup G} (hTM : T ≤ M) :
    pRank 2 ↥T ≤ pRank 2 ↥M := by
  rw [SectionRank.pRank_eq_open_pRank_top, SectionRank.pRank_eq_open_pRank_top]
  exact SectionRank.pRank_top_le_of_injective (by norm_num) (Subgroup.inclusion hTM)
    (Subgroup.inclusion_injective hTM)

theorem three_le_pRank_of_lieModel_fusionZStar {J : Subgroup G} {m : ℕ} (hm : 2 ≤ m)
    (hL : Blueprint.LieModel (J ⧸ Open.fusionZStar J) .PSL 3 2 m) : 3 ≤ pRank 2 ↥J := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨eS⟩ := nonempty_quotient_center_equiv_fusionZStar ↥J
  have h := EvenSporadicStandard.Induction.three_le_pRank_of_quotient_L3 hm
    (LieType.CurtisTits.lieModel_of_mulEquiv eS.symm hL)
  have hodd : ¬ 2 ∣ Nat.card (pPrimeCore 2 ↥J) := fun hd =>
    (Nat.not_even_iff_odd.mpr (Nat.coprime_two_left.mp pPrimeCore_coprime_card))
      (even_iff_two_dvd.mpr hd)
  rwa [GroupTheory.PRankCoprimeQuotient.pRank_quotient_eq_of_not_dvd Nat.prime_two _ hodd] at h

theorem not_psp4_of_suzONanFieldType
    {X : Type} [Group X] (h : SuzONanFieldType X) :
    ¬ ∃ (K : Type) (_ : Field K) (_ : Finite K), Odd (Nat.card K) ∧
      Nonempty (X ≃* StatedProj (StatedSp 2 K)) := by
  rcases h with hs | ho | ⟨n, hn, -, hL⟩
  · exact not_psp4_of_suz hs
  · exact not_psp4_of_onan ho
  · exact not_psp4_of_lieModel_psl_three (by omega) hL

end CFSG.ComponentClassification.GrSLit.L34Sec5S
