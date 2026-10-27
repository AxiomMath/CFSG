module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB82CI3Cfg
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit35SporDataA
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit35SporDataB
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog82A10Sym
public import CFSG.Sporadic.SuzOddCore.CTIComponents
import CFSG.Adapters.StatedClassicalSmallOrders
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB7QPUSporSR
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB82CIURowsCom

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.Blueprint
open scoped MatrixGroups

namespace QPUJ6Cl3

theorem card_of_lieModel_psl_four_three {X : Type} [Group X] (h : LieModel X .PSL 4 3 1) :
    Nat.card X = 6065280 :=
  CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl_four_three (h.statedClassicalModel (by decide))

end QPUJ6Cl3

theorem cfQPUJ6ThreeSpor_holds :
    CFQPUJ6ThreeSpor := by
  intro M _ _ p f hcfg hrep
  obtain ⟨s, ⟨e⟩⟩ := hrep
  obtain ⟨hMq, hZ, hp, hp2, hf, ⟨rfl, rfl⟩, _E, L, t, J, _J₀, -, -, -, -, hLmod, -, htt, htZ, hJC,
    hJc, hJmod, -⟩ := hcfg
  have : IsSimpleGroup (M ⧸ center M) := hMq.2.1
  obtain ⟨-, -, -, F, _, _, hF, ⟨eJ⟩⟩ := HarrisLit.exists_psl2_of_lieModel hJmod
  have : IsSimpleGroup (↥J ⧸ pPrimeCore 2 ↥J) := HarrisLit.isSimpleGroup_of_lieModel_psl2 hJmod
  have : IsSimpleGroup (PSL(2, F)) := eJ.symm.isSimpleGroup
  have hna : ∃ a b : PSL(2, F), a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := HarrisLit.nonabelian_of_lieModel_psl2 hJmod
    exact ⟨eJ a, eJ b, fun h => hab (eJ.injective (by rw [map_mul, map_mul, h]))⟩
  have hF9 : Nat.card F = 9 := hF.trans (by norm_num)
  have h360 : Nat.card (PSL(2, F)) = 360 :=
    (SectionRank.OddCover.card_psl_two hp hp2 hF).trans (by norm_num)
  by_cases hsM : s = .M
  · subst hsM
    exact QPUSpor.false_of_components hMq hZ CatalogueU.sporadicOddCoreFree_M e htt htZ hJC hJc
      hna eJ fun u hu B hB => QPUSpor.not_psl2_component_M e hp2 (by omega) hF u hu B hB
  have hL43 : LieModel (↥L ⧸ pPrimeCore 2 ↥L) .PSL 4 3 1 := by
    rcases hLmod with ⟨h, -⟩ | ⟨-, h⟩
    · exact h
    · exact absurd h (by norm_num)
  have hcardL := QPUJ6Cl3.card_of_lieModel_psl_four_three hL43
  have hLZ := QPUSpor.inf_center_eq_bot hZ (QPUJ6.isSimpleGroup hLmod) hp hp2
    (by rw [hcardL]; norm_num)
  have h1 : Nat.card (↥L ⧸ pPrimeCore 2 ↥L) ∣ Nat.card (M ⧸ center M) :=
    (Subgroup.card_quotient_dvd_card _).trans (QPUSpor.card_dvd_card_quotient_center hLZ)
  rw [Nat.card_congr e.toEquiv, QPUSpor.card_carrier_eq_sporOrder s hsM, hcardL] at h1
  have hsmall : ∀ (B : Type) [Group B], (B ⧸ center B ≃* PSL(2, F)) →
      RestrictedStd.SmallCentralQuotient B := fun B _ eB =>
    Or.inl ⟨3, 2 * 1, hp, hp2, by norm_num, by norm_num,
      Catalog82A10.lieModel_of_equiv_psl hp (by norm_num) hF (by omega) (by omega) eB⟩
  have key : ∀ {s' : TauCeti.SporadicName}, HarrisLit.SporCompData s' →
      (M ⧸ center M ≃* NativeSporadic.Carrier s') → False := fun hD e' =>
    QPUSpor.false_of_components hMq hZ hD.oddCore e' htt htZ hJC hJc hna eJ fun u hu B hB =>
      ⟨fun eB => hD.inner (M ⧸ center M) inferInstance hMq.2.2 ⟨e'⟩ u hu B hB (hsmall B eB)⟩
  cases s
  all_goals first | exact absurd rfl hsM | exact absurd h1 (by decide) | skip
  case Suz =>
    refine QPUSpor.false_of_components hMq hZ CatalogueU.sporadicOddCoreFree_Suz e htt htZ hJC
      hJc hna eJ fun u hu B hB => ⟨fun eB => ?_⟩
    have h20160 :=
      Sporadic.SuzOddCore.CTI_Suz_involution_local_components_simple_quotient_order e u hu B hB
    rw [Nat.card_congr eB.toEquiv, h360] at h20160
    exact absurd h20160 (by norm_num)
  case Co1 => exact key HarrisLit.sporCompData_Co1 e
  case Fi22 => exact key HarrisLit.sporCompData_Fi22 e
  case Fi23 => exact key HarrisLit.sporCompData_Fi23 e
  case Fi24Prime => exact key HarrisLit.sporCompData_Fi24Prime e
  case Th => exact key HarrisLit.sporCompData_Th e
  case B => exact key HarrisLit.sporCompData_B e

end CFSG.ComponentClassification.GSThmB
