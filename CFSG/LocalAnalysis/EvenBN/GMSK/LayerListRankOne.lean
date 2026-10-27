module

public import CFSG.LocalAnalysis.EvenBN.GMSK.Statement
public import CFSG.LocalAnalysis.EvenBN.GMSK.Selector
import CFSG.LocalAnalysis.EvenBN.GMSK.CatDispatch
import CFSG.LocalAnalysis.EvenBN.GMSK.FixedRootDatum
import CFSG.LocalAnalysis.EvenBN.GMSK.LayerRankOne

public section

namespace CFSG.LocalAnalysis.EvenBN.GMSK

open Subgroup CFSG.Blueprint CFSG.LocalAnalysis.SteinbergBV

theorem layerOutcome_of_survivors {G : Type} [Group G] {A : Subgroup G} {n : ℕ}
    (h : FixedRootSurvivors (CFSG.layer G) n) : LayerOutcome G A n := by
  rcases h with h | h | h | ⟨rfl, h⟩ | ⟨rfl, h⟩
  · exact .inr (.inl (.inl h))
  · exact .inr (.inl (.inr (.inl h)))
  · exact .inr (.inl (.inr (.inr h)))
  · refine .inr (.inr (.inl ⟨rfl, ?_⟩))
    rcases h with h | h | h | h | h | h
    · exact .inr (.inl h)
    · exact .inl h
    · exact .inr (.inr (.inr (.inr (.inl h))))
    · exact .inr (.inr (.inr (.inr (.inr (.inl h)))))
    · exact .inr (.inr (.inr (.inr (.inr (.inr (.inl h))))))
    · exact .inr (.inr (.inr (.inr (.inr (.inr (.inr h))))))
  · exact .inr (.inr (.inr ⟨rfl, h⟩))

theorem gmsLinearStandardLayerListKRankOne_of_selector
    (h : FixedRootSelector fun D _ => Catalog D) : GMSLinearStandardLayerListKRankOneStatement := by
  intro G _ _ hG hO n A hA hrank
  obtain ⟨t, htA, ht, hsyl⟩ := exists_involution_of_sylow hrank
  obtain ⟨-, -, -, hDE, -, halt, -⟩ := oneOrTwoLayer_of_stdLinearData hO hA ht htA hsyl
  obtain ⟨hCt, -⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.standard_involution_centralizer_normality hA.isStandard
      htA ht
  rcases halt with ⟨⟨hDs, -, hAD, hnt⟩, -⟩ |
    ⟨⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, ψ, -⟩, -⟩
  · obtain ⟨hcat, K, _, _, α, S, d⟩ := exists_fixedRootDatum_of_simple hG hA
      (fun P hPC hP => card_le_two_of_sylow hrank hPC hP) ht htA hCt hAD.le hDs hnt
    have hsurv := h.survivors_of_datum hDs hcat d
    rw [hDE] at hsurv
    exact layerOutcome_of_survivors hsurv
  · exact .inl ⟨(MulEquiv.subgroupCongr hDE).symm.trans ψ⟩

theorem gmsLinearStandardLayerListKRankOne_of_families
    (hAlt : FixedRootSelector fun D _ => ∃ m : ℕ, 5 ≤ m ∧ Nonempty (D ≃* alternatingGroup (Fin m)))
    (hOdd : FixedRootSelector fun D _ => OddLieType D)
    (hEven : FixedRootSelector fun D _ => EvenLieType D)
    (hSpor : FixedRootSelector fun D _ => NativeSporadic.SporadicRep D) :
    GMSLinearStandardLayerListKRankOneStatement :=
  gmsLinearStandardLayerListKRankOne_of_selector (catalog_selector hAlt hOdd hEven hSpor)

end CFSG.LocalAnalysis.EvenBN.GMSK
