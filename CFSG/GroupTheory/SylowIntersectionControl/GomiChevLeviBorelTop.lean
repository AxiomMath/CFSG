module

public import CFSG.GroupTheory.SylowIntersectionControl.GomiChevLeviBorelFields
public import CFSG.GroupTheory.SylowIntersectionControl.GomiChevLeviPackageTop
import CFSG.GroupTheory.SylowIntersectionControl.GomiChevLeviBorelPackage
import CFSG.GroupTheory.SylowIntersectionControl.GomiChevBorelAtoms
import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.MinParND

public section

namespace CFSG.GroupTheory

open CFSG.Open CFSG.ABGLocalTools Subgroup CFSG.LieType.Universal CFSG.LieType.Steinberg
  CFSG.AGLEmbedding.ParabHub CFSG.AGLEmbedding.ParabPrime
  CFSG.AGLEmbeddingD2.ParabLevi CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.MinPar

variable {K Y : Type} [Group K] [Group Y] {D : UniversalRootDatum K} {n : Fin D.rank → K}
  {H : Fin D.rank → Subgroup K} {π : K →* Y} {e : ℕ}

theorem gomiLeviFactorsMap_of_gomiLeviFactors [Finite K] (h : BorelQuotient D n H π e)
    (hfac : GomiLeviFactors D) : GomiLeviFactorsMap D π :=
  fun C hC h2 hne => (hfac C hC h2 hne).map π fun z hz => h.ker_central z hz

theorem gomiLeviFactors_of_rank_le_two (hr : D.rank ≤ 2) : GomiLeviFactors D :=
  fun _ _ h2 hne => absurd (eq_univ_of_two_le_ncard hr h2) hne

theorem gomiLeviPackageTop_of_borelQuotient [Finite K] [Finite Y] (h : BorelQuotient D n H π e)
    (hfac : GomiLeviFactors D) : GomiLeviPackageTop Y := by
  intro U P hU hBP hPL hat
  obtain ⟨π', hπ', hU'⟩ := exists_borelQuotient_map_posUnipotent_eq h hU
  have hfac' : GomiLeviFactorsMap D π' := gomiLeviFactorsMap_of_gomiLeviFactors hπ' hfac
  have hBQ : borel D H ≤ P.comap π' := by
    rw [← Subgroup.map_le_iff_le_comap, ← hπ'.normalizer_map_posUnipotent, hU']
    exact hBP.le
  have hPeq : P = (parJ D H (negIndices D (P.comap π'))).map π' := by
    calc P = (P.comap π').map π' :=
          (Subgroup.map_comap_eq_self_of_surjective hπ'.surj P).symm
      _ = (parJ D H (negIndices D (P.comap π'))).map π' :=
          congrArg (fun A => A.map π') (eq_parJ_negIndices hπ'.ct hπ'.extras hBQ)
  have hJ : negIndices D (P.comap π') ≠ Set.univ := by
    intro hJu
    have htop : parJ D H (negIndices D (P.comap π')) = ⊤ := by
      rw [hJu, parJ]
      simp only [Set.mem_univ, iSup_true]
      rw [iSup_rankOne_eq_top hπ'.ct hπ'.extras, sup_top_eq]
    exact (ne_of_lt hPL) (by rw [hPeq, htop, Subgroup.map_top_of_surjective π' hπ'.surj])
  refine ⟨borelLeviSet D π' (negIndices D (P.comap π')), ?_⟩
  have h1 := isGomiLeviPackage_borelLeviSet hπ' hfac' hJ
  rwa [hU', ← hPeq] at h1

end CFSG.GroupTheory
