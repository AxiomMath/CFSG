module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.Rbc.NoM12
public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.Rbc.TopOddLie
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Balance.ContainerCore
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.Thm54Reach.CTEvenResidual
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.Thm54Reach.CTEvenSmallLie
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.Thm46FS.ChildrenHered

public section

namespace CFSG.EvenSporadicStandard.M12Std.Rbc

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.NativeSporadic
open CFSG.EvenSporadicStandard.Induction

variable {G : Type} [Group G] [Finite G]

theorem sporadicRep_of_stdHyp
    (hCTE : CTEvenResidualStatement) (hSmall : CTEvenSmallLieStatement)
    (hExc : ∀ (Y : Type) [Group Y], Recognition.Exact.EvenStandardException Y →
      Recognition.Exact.OddStandardType Y)
    (hL34 : ChildL34WHered) (hHe : ChildHeWHered) (hUG : Balance.UHered G)
    (hNo : NoM12List G → False) (hCo3 : IsSporadic G .Co3 → False)
    {X : Subgroup G} (hX : StdHyp G X) (hF : NotF3Five X)
    (hAlt : ∀ {m : ℕ}, 5 ≤ m → Nonempty (↥X ⧸ center ↥X ≃* alternatingGroup (Fin m)) →
      CFSG.OddStandard.OddOutcome G)
    (hOdd : OddLieType (↥X ⧸ center ↥X) →
      ¬ Nonempty (↥X ⧸ center ↥X ≃* alternatingGroup (Fin 5)) →
      ¬ Nonempty (↥X ⧸ center ↥X ≃* alternatingGroup (Fin 6)) →
      ¬ CharThreeLie (↥X ⧸ center ↥X) →
      CFSG.OddStandard.AltOutcome G ∨ OddLieType G ∨
        (IsSporadic G .M12 ∨ IsSporadic G .J1 ∨ IsSporadic G .J2 ∨ IsSporadic G .HS)) :
    SporadicRep (↥X ⧸ center ↥X) := by
  have hq : CFSG.IsQuasisimple ↥X :=
    (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native _).1 hX.standard.1
  have hnonab : ∃ a b : ↥X ⧸ center ↥X, a * b ≠ b * a := hq.2.2
  have hcat : Catalog (↥X ⧸ center ↥X) :=
    Induction.Balance.catalog_center_quotient_of_kProper hX.kProper hX.ne_top hq
  have hA : ∀ {m : ℕ}, 5 ≤ m → Nonempty (↥X ⧸ center ↥X ≃* alternatingGroup (Fin m)) → False :=
    fun hm hAm => hNo (noM12List_of_oddOutcome (hAlt hm hAm))
  have hOdd' : OddLieType (↥X ⧸ center ↥X) → False := by
    intro hlie
    by_cases h5 : Nonempty (↥X ⧸ center ↥X ≃* alternatingGroup (Fin 5))
    · exact hA le_rfl h5
    by_cases h6 : Nonempty (↥X ⧸ center ↥X ≃* alternatingGroup (Fin 6))
    · exact hA (by norm_num) h6
    exact hNo (noM12List_of_oddOutcome (oddOutcome_of_childOddLie (hOdd hlie h5 h6 hF.1)))
  rcases (CFSG.Milestones.ct_catalog_nonabelian_type_partition _ hnonab).1 hcat with
    ⟨m, hm, hAm⟩ | hlie | hEven | hSpor
  · exact (hA hm hAm).elim
  · exact (hOdd' hlie).elim
  · by_cases hexc : Recognition.Exact.EvenStandardException (↥X ⧸ center ↥X)
    · rcases hExc _ hexc with ⟨m, hm, hAm⟩ | hlie | hl34 | hhe
      · exact (hA hm hAm).elim
      · exact (hOdd' hlie).elim
      · exact (hNo (noM12List_of_childL34W (hL34 G hUG X (stdSetting_of_stdHyp hX) hl34))).elim
      · exact (hNo (noM12List_of_childL34W
          (Or.inl (hHe G hUG X (stdSetting_of_stdHyp hX) hhe)))).elim
    · haveI := hX.simple
      obtain ⟨S, hS⟩ := hX.cyclicSylow
      have hres := hCTE G hX.nonabelian hX.kProper X hX.standard hX.oddCore S hS (Or.inl hEven)
        hexc
      have hout : Recognition.EvenSporadicOutcome G → False := fun h => by
        by_cases hC3 : IsSporadic G .Co3
        · exact hCo3 hC3
        · exact hNo (noM12List_of_evenSporadicOutcome h hC3)
      rcases hres.2 with ⟨hsp, -⟩ | hbcd | hbcd | hbcd
      · exact hsp
      · exact (hout (hSmall G hX.nonabelian hX.kProper X hX.standard hX.oddCore S hS (Or.inl hEven)
          hexc hres (Or.inl hbcd))).elim
      · exact (hout (hSmall G hX.nonabelian hX.kProper X hX.standard hX.oddCore S hS (Or.inl hEven)
          hexc hres (Or.inr (Or.inl hbcd)))).elim
      · exact (hout (hSmall G hX.nonabelian hX.kProper X hX.standard hX.oddCore S hS (Or.inl hEven)
          hexc hres (Or.inr (Or.inr hbcd)))).elim
  · exact hSpor

end CFSG.EvenSporadicStandard.M12Std.Rbc
