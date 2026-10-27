module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I2023Facts
public import CFSG.LocalAnalysis.GLTheoremA.CatA.YS09TD4G2A

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I2023

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S10

section TD4

set_option linter.unusedSectionVars false


variable {G : Type} [Group G] [Finite G]

theorem td4_package {X L : Subgroup G} (hL : GLAPComponent 3 X L)
    (hchev : IsChevSimple 2 (PSimple 3 L)) (hTD4 : IsTD4 3 L) :
    ∃ q : TauCeti.PrimePower, q.p = 2 ∧ Subgroup.center (PQuot 3 L) = ⊥ ∧
      catalogIs (PQuot 3 L) (isTD4Of q) ∧ card2 3 L = 2 ^ (12 * q.exponent) := by
  have hp3 : Nat.Prime 3 := Nat.prime_three
  obtain ⟨d, hv, hP, ⟨eS⟩⟩ := CFSG.LocalAnalysis.GLTheoremA.CatB.exists_lieIndex hTD4
  cases d with
  | trialityD4 q =>
    have hq2 : q.p = 2 := td4g2_p_two hv eS hchev
    have hQ : CFSG.Open.IsQuasisimple (PQuot 3 L) := isQuasisimple_pQuot_of_glaPComponent hp3 hL
    have hm : CFSG.Models.LieModel (PQuot 3 L ⧸ Subgroup.center (PQuot 3 L)) .trialityD4 0 q.p
        q.exponent :=
      CFSG.Models.lieModel_of_namesTag ⟨q.prime_p, q.exponent_pos, rfl⟩ ⟨_, hv⟩ ⟨rfl, rfl⟩ eS
    have hGA : CFSG.Open.GriessAllModelsStatement :=
      CFSG.Milestones.cl_lit_griess_schur_multipliers_all_models_statement
    have hdvd := card_center_dvd_of_table hGA hQ hm (a := 1) (b := 1) (c := 1) (d := 1) rfl rfl
      (by norm_num)
    have hc1 : Nat.card (Subgroup.center (PQuot 3 L)) = 1 := Nat.dvd_one.1 (by simpa using hdvd)
    have hcenter : Subgroup.center (PQuot 3 L) = ⊥ := Subgroup.eq_bot_of_card_eq _ hc1
    have eQS : PQuot 3 L ≃* PSimple 3 L :=
      ((QuotientGroup.quotientMulEquivOfEq hcenter).trans QuotientGroup.quotientBot).symm
    obtain ⟨-, hfac⟩ := td4g2_order hv eS
    rw [hq2] at hfac
    refine ⟨q, hq2, hcenter, ⟨.lie ⟨.trialityD4 q, hv⟩, rfl, ⟨eQS.trans eS⟩⟩, ?_⟩
    unfold card2 twoPart
    rw [Nat.card_congr eQS.toEquiv, hfac]
  | _ => exact hP.elim

end TD4

end CFSG.LocalAnalysis.GLTheoremA.I2023

end
