module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.Defs
public import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineTenDefs
import CFSG.Adapters.LieModelSimple
import CFSG.Adapters.StatedClassicalUnitaryOrders
import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameCaseII205GRow
import CFSG.ClassicalInvolution.Q3.TL4LinkZ2W1
import CFSG.HardMathSupport.Foote.Proving.CoverThree.CentreSL3
import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.ThreeTenDvdP1
import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.BInvCentGeneric
import CFSG.LocalAnalysis.SeitzReduction.F4PilotCatEvenExcOrders
import CFSG.RankThree.PartTwo.Sec15.Item152ExclSL2Tools
import CFSG.Sporadic.Fi24.Simple
import CFSG.Sporadic.Ly
import CFSG.Sporadic.ON
import all CFSG.Blueprint.NativeSporadic
import all CFSG.LocalAnalysis.AGL81TheoremCD.Section12.Defs

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section12

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.RankThreeUC.AGL81C
open CFSG.AGLEmbedding
open scoped MatrixGroups

theorem isSimpleOfOrder_iff {n : ℕ} {X : Type} [Group X] :
    IsSimpleOfOrder n X ↔ IsSimpleGroup X ∧ ¬ Group.IsSolvable X ∧ Nat.card X = n :=
  Iff.rfl

theorem IsSimpleOfOrder.of_mulEquiv {n : ℕ} {X Y : Type} [Group X] [Group Y] (e : X ≃* Y)
    (h : IsSimpleOfOrder n Y) : IsSimpleOfOrder n X := by
  obtain ⟨hY, hns, hc⟩ := h
  haveI : IsSimpleGroup Y := hY
  refine ⟨MulEquiv.isSimpleGroup e, ?_, ?_⟩
  · intro hsolv
    haveI : Group.IsSolvable X := hsolv
    exact hns (Group.isSolvable_of_isSolvable_injective (f := e.symm.toMonoidHom) e.symm.injective)
  · rw [Nat.card_congr e.toEquiv, hc]

theorem isSimpleOfOrder_of_reeTitsModel_tits
    {X : Type} [Group X] (h : CFSG.Blueprint.ReeTitsModel X .Tits 2 1) :
    IsSimpleOfOrder 17971200 X := by
  obtain ⟨e⟩ := CFSG.Sporadic.Schreier.Tits.titsModelEquiv X 2 1 h
  haveI : IsSimpleGroup CFSG.Sporadic.Schreier.Tits.titsD :=
    CFSG.Sporadic.Schreier.Tits.titsD_simple
  have hsimple : IsSimpleGroup X := MulEquiv.isSimpleGroup e
  have hcard : Nat.card X = 17971200 := by
    rw [CFSG.SeitzReduction.F4Pilot.EvenExc.card_of_reeTitsModel_tits h]
    norm_num [ordTits]
  refine ⟨hsimple, ?_, hcard⟩
  exact CFSG.EvenSporadicStandard.Induction.Hyp.not_isSolvable_of_simple_card hsimple
    (by rw [hcard]; norm_num)

theorem isSimpleOfOrder_of_isSporadic_HS {X : Type} [Group X]
    (h : CFSG.Blueprint.NativeSporadic.IsSporadic X .HS) : IsSimpleOfOrder 44352000 X := by
  obtain ⟨e⟩ := h
  haveI : IsSimpleGroup (CFSG.Blueprint.NativeSporadic.Carrier .HS) :=
    CFSG.Sporadic.HS.isSimpleGroup_HS
  have hsimple : IsSimpleGroup X := MulEquiv.isSimpleGroup e
  have hcard : Nat.card X = 44352000 := by
    rw [Nat.card_congr e.toEquiv]
    exact CFSG.Sporadic.HS.card_HS
  refine ⟨hsimple, ?_, hcard⟩
  exact CFSG.EvenSporadicStandard.Induction.Hyp.not_isSolvable_of_simple_card hsimple
    (by rw [hcard]; norm_num)

theorem isSimpleOfOrder_of_isSporadic_Ly {X : Type} [Group X]
    (h : CFSG.Blueprint.NativeSporadic.IsSporadic X .Ly) :
    IsSimpleOfOrder 51765179004000000 X := by
  obtain ⟨e⟩ := h
  haveI : IsSimpleGroup (CFSG.Blueprint.NativeSporadic.Carrier .Ly) :=
    CFSG.Sporadic.Ly.fam_ly_simplicity.2.2
  have hsimple : IsSimpleGroup X := MulEquiv.isSimpleGroup e
  have hcard : Nat.card X = 51765179004000000 := by
    rw [Nat.card_congr e.toEquiv]
    exact CFSG.Sporadic.Ly.card_Ly
  refine ⟨hsimple, ?_, hcard⟩
  exact CFSG.EvenSporadicStandard.Induction.Hyp.not_isSolvable_of_simple_card hsimple
    (by rw [hcard]; norm_num)

theorem isSimpleOfOrder_of_isSporadic_ONan {X : Type} [Group X]
    (h : CFSG.Blueprint.NativeSporadic.IsSporadic X .ONan) : IsSimpleOfOrder 460815505920 X := by
  obtain ⟨e⟩ := h
  haveI : IsSimpleGroup (CFSG.Blueprint.NativeSporadic.Carrier .ONan) :=
    CFSG.Sporadic.ON.fam_on_simplicity.2.2
  have hsimple : IsSimpleGroup X := MulEquiv.isSimpleGroup e
  have hcard : Nat.card X = 460815505920 := by
    rw [Nat.card_congr e.toEquiv]
    exact CFSG.Sporadic.ON.card_ON
  refine ⟨hsimple, ?_, hcard⟩
  exact CFSG.EvenSporadicStandard.Induction.Hyp.not_isSolvable_of_simple_card hsimple
    (by rw [hcard]; norm_num)

theorem isSimpleOfOrder_of_isSporadic_Fi24Prime {X : Type}
    [Group X] (h : CFSG.Blueprint.NativeSporadic.IsSporadic X .Fi24Prime) :
    IsSimpleOfOrder 1255205709190661721292800 X := by
  obtain ⟨e⟩ := h
  haveI : IsSimpleGroup (CFSG.Blueprint.NativeSporadic.Carrier .Fi24Prime) :=
    CFSG.Sporadic.Fi24.isSimpleGroup_Fi24prime
  have hsimple : IsSimpleGroup X := MulEquiv.isSimpleGroup e
  have hcard : Nat.card X = 1255205709190661721292800 := by
    rw [Nat.card_congr e.toEquiv]
    exact CFSG.Sporadic.Fi24.card_Fi24prime
  refine ⟨hsimple, ?_, hcard⟩
  exact CFSG.EvenSporadicStandard.Induction.Hyp.not_isSolvable_of_simple_card hsimple
    (by rw [hcard]; norm_num)

theorem isSimpleOfOrder_of_statedClassicalModel_psu_three_five {X : Type} [Group X]
    (h : CFSG.Open.StatedClassicalModel X .PSU 3 5 1) : IsSimpleOfOrder 126000 X := by
  have hsimple : IsSimpleGroup X := CFSG.Open.StatedAPI.isSimpleGroup_of_statedClassicalModel h
  have hcard : Nat.card X = 126000 :=
    CFSG.Open.StatedAPI.card_of_statedClassicalModel_psu_three_five h
  refine ⟨hsimple, ?_, hcard⟩
  exact CFSG.EvenSporadicStandard.Induction.Hyp.not_isSolvable_of_simple_card hsimple
    (by rw [hcard]; norm_num)

theorem isSimpleOfOrder_of_chevalleyExceptionalModel_g2_five
    {X : Type} [Group X] (h : CFSG.Blueprint.ChevalleyExceptionalModel X .G2 5 1) :
    IsSimpleOfOrder 5859000000 X := by
  have hLie : CFSG.Blueprint.LieModel X .G2 0 5 1 := Or.inr (Or.inl ⟨rfl, by decide, h⟩)
  have hsimple : IsSimpleGroup X :=
    CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf.isSimpleGroup_of_lieModel_g2
      (by norm_num) hLie
  have hcard : Nat.card X = 5859000000 := by
    rw [CFSG.GH74.card_of_lieModel_G2 (by norm_num) hLie]
    norm_num [ordG2]
  refine ⟨hsimple, ?_, hcard⟩
  exact CFSG.EvenSporadicStandard.Induction.Hyp.not_isSolvable_of_simple_card hsimple
    (by rw [hcard]; norm_num)

theorem isSimpleOfOrder_of_isSporadic_He {X : Type} [Group X]
    (h : CFSG.Blueprint.NativeSporadic.IsSporadic X .He) : IsSimpleOfOrder 4030387200 X := by
  obtain ⟨e⟩ := h
  haveI : IsSimpleGroup (CFSG.Blueprint.NativeSporadic.Carrier .He) :=
    CFSG.Sporadic.He.isSimpleGroup_He
  have hsimple : IsSimpleGroup X := MulEquiv.isSimpleGroup e
  have hcard : Nat.card X = 4030387200 := by
    rw [Nat.card_congr e.toEquiv]
    exact CFSG.Sporadic.He.card_He
  refine ⟨hsimple, ?_, hcard⟩
  exact CFSG.EvenSporadicStandard.Induction.Hyp.not_isSolvable_of_simple_card hsimple
    (by rw [hcard]; norm_num)

private theorem card_psl3_seven : Nat.card (PSL(3, ZMod 7)) = 1876896 := by
  have h := CFSG.HardMathSupport.Foote.Proving.natCard_PSL3_mul_gcd (ZMod 7)
  rw [ZMod.card] at h
  rw [show Nat.gcd 3 (7 - 1) = 3 by norm_num,
    CFSG.GroupTheory.card_SL3_zmod (by norm_num : Nat.Prime 7)] at h
  have hR : 7 ^ 3 * ((7 ^ 2 - 1) * (7 ^ 3 - 1)) = 1876896 * 3 := by norm_num
  rw [hR] at h
  exact Nat.eq_of_mul_eq_mul_right (by norm_num : 0 < 3) h

theorem isSimpleOfOrder_of_isPSLType_three_three {X : Type} [Group X]
    (h : IsPSLType 3 (ZMod 3) X) : IsSimpleOfOrder 5616 X := by
  obtain ⟨e⟩ := h
  haveI : IsSimpleGroup (PSL(3, ZMod 3)) :=
    CFSG.BenderSuzuki.External.huppert_II_6_13 3 (by norm_num) (Or.inl (by norm_num))
      (Or.inl (by norm_num))
  have hsimple : IsSimpleGroup X := MulEquiv.isSimpleGroup e
  have hcard : Nat.card X = 5616 := by
    rw [Nat.card_congr e.toEquiv]
    exact CFSG.ClassicalInvolution.Q3.TL4.Z2W.card_psl3_three
  refine ⟨hsimple, ?_, hcard⟩
  exact CFSG.EvenSporadicStandard.Induction.Hyp.not_isSolvable_of_simple_card hsimple
    (by rw [hcard]; norm_num)

theorem isSimpleOfOrder_of_isPSLType_three_seven {X : Type} [Group X]
    (h : IsPSLType 3 (ZMod 7) X) : IsSimpleOfOrder 1876896 X := by
  obtain ⟨e⟩ := h
  haveI : IsSimpleGroup (PSL(3, ZMod 7)) :=
    CFSG.BenderSuzuki.External.huppert_II_6_13 3 (by norm_num) (Or.inl (by norm_num))
      (Or.inl (by norm_num))
  have hsimple : IsSimpleGroup X := MulEquiv.isSimpleGroup e
  have hcard : Nat.card X = 1876896 := by
    rw [Nat.card_congr e.toEquiv]
    exact card_psl3_seven
  refine ⟨hsimple, ?_, hcard⟩
  exact CFSG.EvenSporadicStandard.Induction.Hyp.not_isSolvable_of_simple_card hsimple
    (by rw [hcard]; norm_num)

theorem simple_nonsolvable_three_dvd_of_isPSLType_two {X : Type} [Group X] {p : ℕ}
    [Fact p.Prime] (hp5 : 5 ≤ p) (h : IsPSLType 2 (ZMod p) X) :
    IsSimpleGroup X ∧ ¬ Group.IsSolvable X ∧ 3 ∣ Nat.card X := by
  haveI : IsSimpleGroup (PSL(2, ZMod p)) :=
    CFSG.RankThree.PartTwo.Sec15.isSimpleGroup_PSL2 hp5
  obtain ⟨e⟩ := h
  have hsimple : IsSimpleGroup X := MulEquiv.isSimpleGroup e
  have hnc : ∃ a b : X, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := CFSG.RankThree.PartTwo.Sec15.exists_ne_comm_PSL2 hp5
    exact ⟨e.symm a, e.symm b, fun hcomm => hab (by simpa using congrArg e hcomm)⟩
  refine ⟨hsimple, ?_, ?_⟩
  · intro hsolv
    haveI : IsSimpleGroup X := hsimple
    obtain ⟨a, b, hab⟩ := hnc
    exact hab ((IsSimpleGroup.comm_iff_isSolvable (G := X)).mpr hsolv a b)
  · rw [Nat.card_congr e.toEquiv]
    exact CFSG.RankThree.PartTwo.Sec15.three_dvd_card_PSL2 (by omega)

@[expose] def TwelveThreeOrderFacts : Prop :=
  (∀ (X : Type) [Group X], CFSG.Blueprint.ReeTitsModel X .Tits 2 1 →
      IsSimpleOfOrder 17971200 X) ∧
  (∀ (X : Type) [Group X], CFSG.Blueprint.NativeSporadic.IsSporadic X .HS →
      IsSimpleOfOrder 44352000 X) ∧
  (∀ (X : Type) [Group X], CFSG.Blueprint.NativeSporadic.IsSporadic X .Ly →
      IsSimpleOfOrder 51765179004000000 X) ∧
  (∀ (X : Type) [Group X], CFSG.Blueprint.NativeSporadic.IsSporadic X .ONan →
      IsSimpleOfOrder 460815505920 X) ∧
  (∀ (X : Type) [Group X], CFSG.Blueprint.NativeSporadic.IsSporadic X .Fi24Prime →
      IsSimpleOfOrder 1255205709190661721292800 X) ∧
  (∀ (X : Type) [Group X], CFSG.Blueprint.ChevalleyExceptionalModel X .G2 5 1 →
      IsSimpleOfOrder 5859000000 X) ∧
  (∀ (X : Type) [Group X], CFSG.Blueprint.NativeSporadic.IsSporadic X .He →
      IsSimpleOfOrder 4030387200 X)

theorem twelveThreeOrderFacts_holds :
    TwelveThreeOrderFacts := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro X _
    exact isSimpleOfOrder_of_reeTitsModel_tits
  · intro X _
    exact isSimpleOfOrder_of_isSporadic_HS
  · intro X _
    exact isSimpleOfOrder_of_isSporadic_Ly
  · intro X _
    exact isSimpleOfOrder_of_isSporadic_ONan
  · intro X _
    exact isSimpleOfOrder_of_isSporadic_Fi24Prime
  · intro X _
    exact isSimpleOfOrder_of_chevalleyExceptionalModel_g2_five
  · intro X _
    exact isSimpleOfOrder_of_isSporadic_He

end CFSG.LocalAnalysis.AGL81TheoremCD.Section12
