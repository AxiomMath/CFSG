module

public import CFSG.LocalAnalysis.ComponentClassification.RestrictedSporSmall
public import CFSG.LocalAnalysis.ComponentClassification.RestrictedSporMcLOuter
public import CFSG.LocalAnalysis.ComponentClassification.PSL3FourAlternatingExclusion
public import CFSG.LocalAnalysis.ComponentClassification.RestrictedSporMcL

public section

namespace CFSG.ComponentClassification.RestrictedStd.Spor

open CFSG Subgroup CFSG.Blueprint CFSG.ComponentClassification.GSThmB CFSG.Sporadic.SmallOddCore
open CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.Sporadic.Schreier (fixSub)

theorem not_small_of_mclX {Y : Type} [Group Y] (h : Nonempty (Y ⧸ center Y ≃* mclX)) :
    ¬ SmallCentralQuotient Y := by
  obtain ⟨θ⟩ := h
  have hcard : Nat.card (Y ⧸ center Y) = 20160 := by rw [Nat.card_congr θ.toEquiv, card_mclX]
  rintro (⟨p, f, hp, hp2, -, -, hm⟩ | ⟨⟨e7⟩⟩ | h34)
  · rw [card_of_lieModel_psl_two hp2 hm] at hcard
    exact ordA_one_ne_20160 _ hcard
  · rw [Nat.card_congr e7.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup,
      Fintype.card_fin] at hcard
    norm_num [Nat.factorial] at hcard
  · have hst := statedClassicalModel_of_lieModel_ne_zero (by norm_num) h34
    obtain ⟨-, h64, -⟩ := PSL3Four.excludes_alternating_models_stated.{0} _ hst
    obtain ⟨z, hzX, hz6⟩ := mclX_order_six
    set z' : mclX := ⟨z, hzX⟩
    have hz'6 : orderOf z' = 6 := by rw [Subgroup.orderOf_mk]; exact hz6
    have hu : orderOf (θ.symm (z' ^ 3)) = 2 := by
      rw [MulEquiv.orderOf_eq, orderOf_pow' z' (by norm_num : 3 ≠ 0), hz'6]
      norm_num
    have hv : orderOf (θ.symm (z' ^ 2)) = 3 := by
      rw [MulEquiv.orderOf_eq, orderOf_pow' z' (by norm_num : 2 ≠ 0), hz'6]
      norm_num
    have hvC : θ.symm (z' ^ 2) ∈ centralizer ({θ.symm (z' ^ 3)} : Set (Y ⧸ center Y)) := by
      rw [mem_centralizer_singleton_iff, ← map_mul, ← map_mul, ← pow_add, ← pow_add, add_comm]
    have h3 : 3 ∣ Nat.card (centralizer ({θ.symm (z' ^ 3)} : Set (Y ⧸ center Y))) := by
      have := orderOf_dvd_natCard (⟨_, hvC⟩ : centralizer ({θ.symm (z' ^ 3)} : Set _))
      rwa [Subgroup.orderOf_mk, hv] at this
    rw [h64 _ hu] at h3
    norm_num at h3

theorem not_isSmallOrder_M11 : ¬ IsSmallOrder 7920 :=
  not_isSmallOrder_of_between (q₀ := 25) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sporadicCase_McL : SporadicCase .McL := by
  refine sporadicCase_of_comps (fun G _ _ ⟨e⟩ t ht => ?_)
    (fun G _ _ _ _ ⟨e⟩ α hα2 hα => ?_)
  · exact (mcl_inner_comps e t ht).mono fun Y _ h => not_small_of_mclX h
  · refine (mcl_outer_comps e α hα2 hα).mono fun Y _ h => not_small_of_card_quotient ?_
    rw [Set.mem_singleton_iff.1 h]
    exact not_isSmallOrder_M11

end CFSG.ComponentClassification.RestrictedStd.Spor
