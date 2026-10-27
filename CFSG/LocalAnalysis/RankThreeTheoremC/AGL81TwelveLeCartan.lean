module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TwelveLeCartanPerfect
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TwelveLeCartanSolv
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TwelveLeCartanSp
public import CFSG.LocalAnalysis.ComponentClassification.GoldschmidtTDGriess

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TwelveLe

open CFSG.Open CFSG.AGLEmbedding CFSG.QuasithinUnique Subgroup
open CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree
open scoped commutatorElement

section FromGriess


theorem kFactTwelveLeCartan_of_griess (hGA : GriessAllModelsStatement) (hS : KFactTwelveLeSmall)
    (h3 : KFactTwelveLeSolvThree) : KFactTwelveLeCartan := by
  intro A _ _ Y P β hY hO hcl hP hPY hSyl hna hβ3 hβY hβP hW hrk
  by_cases hcent : ∀ y ∈ Y, β * y = y * β
  · exact Or.inl hcent
  right
  have hZ : OddCenterRest := oddCenterRest_of_griess hGA
  have hβodd : Odd (orderOf β) := by
    rw [hβ3]
    decide
  have hclc := hcl
  rcases hcl with ⟨d, hd, ⟨e⟩⟩ | hsmall | hsmall
  · by_cases hB2 : IsLieOf ParabCensus.IdxBTwo (↥Y ⧸ center ↥Y)
    · exact absurd (centralizes_of_idxBTwo hZ hY hO hB2 hP hβodd hβY hβP hW) hcent
    · have hodd := ParabCensus.not_two_dvd_index_wSup_of_parabolic hGA hY hO hclc hP hB2
      by_cases hJ : ∃ J : Subgroup A, J ≤ P ∧ ⁅J, J⁆ = J ∧ 3 ∣ Nat.card J
      · obtain ⟨J, hJP, hJ, hJ3⟩ := hJ
        exact Or.inl
          (exists_component_of_perfect hY hd e hP.1 hβ3 hβY hβP hW hodd hcent hJP hJ hJ3)
      · have hnoJ : ∀ J : Subgroup A, J ≤ P → ⁅J, J⁆ = J → ¬ 3 ∣ Nat.card J :=
          fun J hJP hJp h3J => hJ ⟨J, hJP, hJp, h3J⟩
        exact solvThree_case hGA h3 hY hO hd e hB2 hP hPY hSyl hβ3 hβY hcent hrk hnoJ
  · exact absurd (hS A Y P β hY hO (Or.inl hsmall) hP hPY hSyl hna hβ3 hβY hβP hW) hcent
  · exact absurd (hS A Y P β hY hO (Or.inr hsmall) hP hPY hSyl hna hβ3 hβY hβP hW) hcent

end FromGriess

section Main


theorem kFactTwelveLeCartan_of (hS : KFactTwelveLeSmall) (h3 : KFactTwelveLeSolvThree) :
    KFactTwelveLeCartan :=
  kFactTwelveLeCartan_of_griess
    CFSG.ComponentClassification.TBLit.griessMultipliersAllModels_holds hS h3

end Main

end CFSG.LocalAnalysis.RankThreeTheoremC.TwelveLe
