module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpSmSp1Wit
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicM22Model
public import CFSG.Sporadic.Schreier.MathieuOddCoreM22Outer
public import Certificates.Certificate397505

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp.Small.SP1

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Q3
open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.RankThree.Native
open CFSG.CGT.PushingUpLit.SolKNA.R4.Check (qGens)
open CFSG.ComponentClassification.RankTwoSporadic.M22
open Certificates.TwinPerpSmSp1

set_option linter.unusedSectionVars false

theorem m22SmallAutModel :
    CFSG.Sporadic.SmallOddCore.AutModel (CFSG.Monster.B.TwoA.P0in.map iota) iota.range :=
  smallAutModel_of_rankTwo m22AutModel iota iota_injective

theorem m22Syl_le :
    Subgroup.closure (permsA 24 (qGens m22Wit.syl)) ≤ iota.range :=
  syl_le_of_q8WitCheck m22Wit Certificates.certificate397505.1.1 _ fun _ hl =>
    mem_range_of_pairA (allLt_spec Certificates.certificate397505.1.2.2 hl)


theorem leaf_m22 {n : ℕ} :
    NoTwinS n (fun F _ => CFSG.Blueprint.NativeSporadic.IsSporadic F .M22) := by
  have h := Certificates.certificate397505.1.1
  have hcardR : 2 ^ 8 * 3465 = Nat.card ↥iota.range := by
    rw [← Nat.card_congr (MonoidHom.ofInjective iota_injective).toEquiv,
      CFSG.Monster.B.TwoA.natCard_Ppair]
    norm_num
  refine noTwinS_of_q8Wit m22SmallAutModel (Subgroup.closure (permsA 24 (qGens m22Wit.syl)))
    m22Syl_le (k := 8) (m := 3465) (card_syl_of_q8WitCheck m22Wit h) (by decide) hcardR
    (hwit_of_q8WitCheck m22Wit rfl h _ fun l hl => ?_) ?_
  · exact m22_hin _ (xg_valid_of_q8WitCheck m22Wit h l hl)
      (allLt_spec Certificates.certificate397505.1.2.1 hl)
  · intro Y _ _ R' S t hP hF
    obtain ⟨ψ₀⟩ := hF
    have ψ : ↥(genFittingFStar Y) ≃* ↥CFSG.Blueprint.NativeSporadic.M22 := ψ₀
    haveI := hP.core.simple
    haveI : (genFittingFStar Y).Normal := genFittingFStar_normal Y
    obtain ⟨e₀⟩ := m22AutModel.nonempty_mulEquiv
    refine ⟨⟨ψ₀.trans (e₀.symm.trans (Subgroup.equivMapOfInjective _ iota iota_injective))⟩, ?_⟩
    exact isPGroup_core_of_oddCore hP
      (CFSG.Sporadic.Schreier.oddCore_centralizer_eq_bot_of_normal
        CFSG.Sporadic.Schreier.m22_inner_oddCore CFSG.Sporadic.Schreier.m22_mulAut_card
        CFSG.Sporadic.Schreier.m22_outer_oddCore (genFittingFStar Y) ψ
        (Nobq.centralizer_genFittingFStar_eq_bot hP.core.nonab) t hP.core.datum.order)

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp.Small.SP1
