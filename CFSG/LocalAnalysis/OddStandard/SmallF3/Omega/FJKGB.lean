module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3L34GXHard
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.BridgeZ2
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3L34Q8Pocket
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3L34Syl
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3L34Pocket
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3L34GC1Simp
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3PkL3
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3PkU3
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2G1
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2Q8Plus
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FGPocketM
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FF6MField2

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

theorem fj_exists_q8_of_isI4PlusIn {Y : Type} [Group Y] [Finite Y] {X : Subgroup Y} {b : Y}
    (h : IsI4PlusIn X b) :
    ∃ f : QuaternionGroup 2 →* Y, Function.Injective f ∧ f (QuaternionGroup.a 2) = b := by
  obtain ⟨hb2, K, hbK, -, -, hKsl⟩ := h
  obtain ⟨f, hf, hfb, -⟩ := exists_quaternion_of_isSL23Mod hKsl hbK hb2
  exact ⟨f, hf, hfb⟩

private theorem fj_isOm6M_top {Y : Type} [Group Y] [Finite Y] (h : LieModel Y .PSU 4 3 1) :
    IsOm6M (⊤ : Subgroup Y) := by
  have hSF : SimpleFStarQuotient Y := Or.inl (Or.inr (Or.inr (Or.inl h)))
  obtain ⟨hsimp, hcent⟩ := l34g_simple_of_simpleFStar hSF
  haveI : IsSimpleGroup Y := hsimp
  have hnab : ∃ a b : Y, a * b ≠ b * a := by
    by_contra hcon
    push Not at hcon
    have htop : center Y = ⊤ := by
      rw [eq_top_iff]
      intro x _
      rw [Subgroup.mem_center_iff]
      exact fun g => (hcon x g).symm
    rw [htop] at hcent
    exact bot_ne_top hcent.symm
  have hO : CFSG.oddCore Y = ⊥ :=
    CFSG.ComponentClassification.UnbalancedCatalog.EvenCatalog.oddCore_eq_bot_of_isSimpleGroup
      (CFSG.Walter.even_card_of_isSimpleGroup hnab)
  have hOtop : CFSG.oddCore ↥(⊤ : Subgroup Y) = ⊥ :=
    CFSG.ComponentClassification.UnbalancedCatalog.EvenCatalog.oddCore_eq_bot_of_mulEquiv
      Subgroup.topEquiv.symm hO
  have hq : CFSG.IsQuasisimple Y := l34g_isQuasisimple_of_starQuotient (Or.inl hSF)
  refine ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv Subgroup.topEquiv.symm hq, ?_⟩
  have e : ↥(⊤ : Subgroup Y) ⧸ CFSG.oddCore ↥(⊤ : Subgroup Y) ≃* Y :=
    ((QuotientGroup.quotientMulEquivOfEq hOtop).trans QuotientGroup.quotientBot).trans
      Subgroup.topEquiv
  exact LieModel.of_mulEquiv e.symm h

theorem fj_isI4PlusIn_top_psu43 {Y : Type} [Group Y] [Finite Y] (h : LieModel Y .PSU 4 3 1)
    {z : Y} (hz : orderOf z = 2) : IsI4PlusIn (⊤ : Subgroup Y) z := by
  have hΩ := fj_isOm6M_top h
  obtain ⟨-, hcent⟩ := l34g_simple_of_simpleFStar
    (show SimpleFStarQuotient Y from Or.inl (Or.inr (Or.inr (Or.inl h))))
  have hN : z ∈ normalizer ((⊤ : Subgroup Y) : Set Y) :=
    Subgroup.le_normalizer (Subgroup.mem_top z)
  have hin : InnerOn (⊤ : Subgroup Y) z := Subgroup.mem_sup_left (Subgroup.mem_top z)
  have hnc : z ∉ centralizer ((⊤ : Subgroup Y) : Set Y) := by
    intro hzc
    have hzC : z ∈ center Y := Subgroup.mem_center_iff.mpr fun g =>
      Subgroup.mem_centralizer_iff.mp hzc g (Subgroup.mem_top g)
    rw [hcent, Subgroup.mem_bot] at hzC
    rw [hzC, orderOf_one] at hz
    exact absurd hz (by norm_num)
  exact (fg_pocket_M Y ⊤ hΩ z (Subgroup.mem_top z)).mpr
    ⟨hz, (ff6m_inner_iff Y ⊤ hΩ z hz hN).mp ⟨hin, hnc⟩⟩

theorem fj_isI4PlusIn_top_of_q8 (hS : Asc82SchurU43) {Y : Type} [Group Y] [Finite Y]
    (hY : L34GStarQuotient Y) {f : QuaternionGroup 2 →* Y} (hf : Function.Injective f) :
    IsI4PlusIn (⊤ : Subgroup Y) (f (QuaternionGroup.a 2)) := by
  have hz : orderOf (f (QuaternionGroup.a 2)) = 2 :=
    (orderOf_injective f hf _).trans orderOf_quaternion_a_two
  rcases hY with ((h5 | h6p | h6m | h7 | h8p | h8m) | (hl9 | hl81 | hl33 | hu33)) | ⟨hqs, htwo⟩
  · exact isI4PlusIn_top_of_isOmegaStar asc82PocketCover_holds (isOmegaStar_of_lieModel_psp h5)
      (Or.inl (by norm_num)) (by decide) hf
  · exact isI4PlusIn_top_of_isOmegaStar asc82PocketCover_holds (isOmegaStar_of_lieModel_psl h6p)
      (Or.inl (by norm_num)) (by decide) hf
  · exact fj_isI4PlusIn_top_psu43 h6m hz
  · exact isI4PlusIn_top_of_isOmegaStar asc82PocketCover_holds (isOmegaStar_of_lieModel_odd h7)
      (Or.inl (by norm_num)) (by decide) hf
  · exact asc82Omega8PlusPocket_holds Y h8p f hf
  · exact isI4PlusIn_top_of_isOmegaStar asc82PocketCover_holds (isOmegaStar_of_lieModel_minus h8m)
      (Or.inr ⟨rfl, rfl⟩) (by decide) hf
  · exact absurd hf (asc82NoQ8InL2_holds Y (Or.inl hl9) f)
  · exact absurd hf (asc82NoQ8InL2_holds Y (Or.inr hl81) f)
  · exact isI4PlusIn_top_of_lieModel_psl33 hl33 hz
  · exact isI4PlusIn_top_of_lieModel_psu33 hu33 hz
  · exact isI4PlusIn_top_of_isOmegaCover asc82PocketCover_holds
      ((isOmegaCover_iff_isTwoU43 hS hqs).mpr htwo) (Or.inl (by norm_num)) hf

theorem asc82CoreKGB_holds (hS : Asc82SchurU43) : Asc82CoreKGB := by
  intro Y _ _ hY σ _ J _ b _ hI
  obtain ⟨f, hf, hfb⟩ := fj_exists_q8_of_isI4PlusIn hI
  rw [← hfb]
  exact fj_isI4PlusIn_top_of_q8 hS hY hf

theorem asc82CoreKGBHard_holds (hS : Asc82SchurU43) : Asc82CoreKGBHard := by
  intro Y _ _ hY _ σ hσ _ J hJ b hb hI
  exact asc82CoreKGB_holds hS Y hY σ hσ J hJ b hb hI

end CFSG.OddStandard.SmallF3.Omega
