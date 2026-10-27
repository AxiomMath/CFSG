module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.ONan.S5Cases
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.ONanProps
public import CFSG.LocalAnalysis.ComponentInitial.KProperPumpUpStatement
public import CFSG.RankThree.PartOne.CTP.OutEmbed
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.ONan.S5Socle

public section

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus.ONan.S5

open Subgroup CFSG.Blueprint CFSG.Blueprint.NativeSporadic

theorem onan77S5_of_catThreeA5
    (hS : CFSG.LocalAnalysis.ComponentInitial.SchreierFor Catalog) (hcat : CatThreeA5) :
    ONan77S5 := by
  intro Y _ _ hK hab P hcomm hcube hcard hcent
  have h : Setting Y P := ⟨hab, hcomm, hcube, hcard, hcent⟩
  obtain ⟨N, hNn, hNs, ⟨x, hx, y, hy, hxy⟩, hNc, h3⟩ := h.exists_simple_normal
  haveI := hNn
  haveI := hNs
  have hnc : ∃ a b : ↥N, a * b ≠ b * a :=
    ⟨⟨x, hx⟩, ⟨y, hy⟩, fun he => hxy (congrArg Subtype.val he)⟩
  have hcatN : Catalog ↥N :=
    CFSG.SectionRank.catalog_of_isKGroupCat_of_surjective hK N (MonoidHom.id ↥N)
      Function.surjective_id
  refine ⟨N, hNn, by rw [hNc]; exact bot_le, ?_⟩
  rcases h.le_or_selfCentralizing hNn h3 with hPN | ⟨c, hcN, hc3, hcC⟩
  · rcases hcat ↥N hNs hnc hcatN (h.factorization_three_of_le hPN)
        (fun z hz => h.threeA5OrS5_of_le hNn hPN z hz) with hHS | hM23 | hSp
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hHS)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inl hM23)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hSp))))))))
  · have hOut := hS ↥N hnc hcatN
    have hsol : Group.IsSolvable (Y ⧸ N) :=
      CFSG.RankThree.PartOne.CTP.solvable_quotient_of_outer N hNc
    exact (h.false_of_selfCentralizing hsol hcN hc3 hcC).elim

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus.ONan.S5
