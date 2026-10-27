module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.Input
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.StandardCentralizer
public import CFSG.LocalAnalysis.EvenSporadicStandard.M23Std.XbarCentralizer
public import CFSG.FeitThompson.OddOrderTheorem
import CFSG.Goldschmidt.Steps.G37Quot

public section

namespace CFSG.EvenSporadicStandard.M22Std

open Subgroup CFSG.Open CFSG.EvenSporadicStandard.M24Std CFSG.EvenSporadicStandard.M23Std

theorem map_egaLayer_le {G H : Type} [Group G] [Group H] (f : G →* H)
    (hf : Function.Surjective f) : (egaLayer G).map f ≤ egaLayer H := by
  unfold egaLayer
  rw [Subgroup.map_iSup]
  refine iSup_le fun K => ?_
  rw [Subgroup.map_iSup]
  refine iSup_le fun hK => ?_
  by_cases hKf : K ≤ f.ker
  · rw [(Subgroup.map_eq_bot_iff _).2 hKf]
    exact bot_le
  · have hK' : CFSG.GorensteinWalter.IsComponentOf K ⊤ :=
      (CFSG.Adapters.isComponentOf_top_iff K).1 hK
    have h1 := CFSG.Goldschmidt.G37.isComponentOf_map' f hK' hKf
    rw [Subgroup.map_top_of_surjective f hf] at h1
    have h2 : CFSG.Open.IsComponentOf (K.map f) ⊤ := (CFSG.Adapters.isComponentOf_top_iff _).2 h1
    exact le_iSup₂_of_le (f := fun K (_ : IsComponentOf K ⊤) => K) (K.map f) h2 le_rfl

variable {G : Type} [Group G] [Finite G]

theorem le_of_perfect_le_sup_oddCore {U K : Subgroup G} [U.Normal] (hK : commutator K = ⊤)
    (hle : K ≤ U ⊔ fusionOddCore G) : K ≤ U := by
  have hsolv : Group.IsSolvable (fusionOddCore G) :=
    CFSG.FeitThompson.isSolvable_of_odd_natCard _ (natCard_fusionOddCore_odd G)
  have hker : (QuotientGroup.mk' U).ker = U := QuotientGroup.ker_mk' U
  set π := QuotientGroup.mk' U with hπ
  have hT : Group.IsSolvable ((fusionOddCore G).map π) :=
    Group.isSolvable_of_surjective (f := π.subgroupMap (fusionOddCore G))
      (π.subgroupMap_surjective _)
  have hU0 : U.map π = ⊥ := (Subgroup.map_eq_bot_iff _).2 hker.ge
  have hKT : K.map π ≤ (fusionOddCore G).map π := by
    calc K.map π ≤ (U ⊔ fusionOddCore G).map π := Subgroup.map_mono hle
      _ = (fusionOddCore G).map π := by rw [Subgroup.map_sup, hU0, bot_sup_eq]
  have hS : Group.IsSolvable (K.map π) :=
    Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hKT)
  have hSperf : commutator (K.map π) = ⊤ := by
    have h1 := map_derivedSeries_eq (π.subgroupMap_surjective K) 1
    rw [derivedSeries_one, derivedSeries_one, hK, Subgroup.map_top_of_surjective _
      (π.subgroupMap_surjective K)] at h1
    exact h1.symm
  by_contra hne
  have hnt : Nontrivial (K.map π) := by
    rw [Subgroup.nontrivial_iff_ne_bot]
    intro hbot
    exact hne (hker ▸ (Subgroup.map_eq_bot_iff _).1 hbot)
  exact (Group.IsSolvable.commutator_lt_top_of_nontrivial (K.map π)).ne hSperf

theorem egaLayer_eq_of_cover {U : Subgroup G} [U.Normal] [IsSimpleGroup U]
    (hnab : ∃ a b : U, a * b ≠ b * a)
    (hE : egaLayer (G ⧸ fusionOddCore G) ≤ U.map (QuotientGroup.mk' (fusionOddCore G))) :
    egaLayer G = U := by
  apply le_antisymm
  · unfold egaLayer
    refine iSup_le fun K => iSup_le fun hK => ?_
    refine le_of_perfect_le_sup_oddCore ?_ ?_
    · exact hK.2.2.1
    · have h1 : K.map (QuotientGroup.mk' (fusionOddCore G)) ≤
          egaLayer (G ⧸ fusionOddCore G) :=
        (Subgroup.map_mono (le_iSup₂_of_le (f := fun K (_ : IsComponentOf K ⊤) => K) K hK
          le_rfl)).trans (map_egaLayer_le _ (QuotientGroup.mk'_surjective _))
      have h2 := h1.trans hE
      rw [Subgroup.map_le_iff_le_comap, Subgroup.comap_map_eq, QuotientGroup.ker_mk'] at h2
      exact h2
  · obtain ⟨hq, -⟩ := isQuasisimple_center_eq_bot_of_isSimpleGroup hnab
    have hc : IsComponentOf U ⊤ :=
      ⟨le_top, CFSG.Open.IsSubnormal.step le_top inferInstance (CFSG.Open.IsSubnormal.refl _), hq⟩
    exact le_iSup₂_of_le (f := fun K (_ : IsComponentOf K ⊤) => K) U hc le_rfl

end CFSG.EvenSporadicStandard.M22Std
