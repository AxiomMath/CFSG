module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic.Split
public import CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic.RouteBGlue
public import CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic.GaloisSevenThree
public import CFSG.Sporadic.ON
public import CFSG.Sporadic.ONOddCore.OuterOrder
public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.ONCoverCert
public import Certificates.Certificate129009

public section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic

open CFSG.Blueprint CFSG.F3.Native CFSG.Sporadic.ON CFSG.Sporadic.ON.Native
  CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.Quasithin CFSG.QuasithinUnique.Setup.X1 CFSG.QuasithinUnique.Setup.Family
open CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit

theorem on_heisCfg :
    ∃ x y z g : NativeSporadic.ON,
      HeisCfg 7 1 (fun _ => x) (fun _ => y) z ∧ y ^ 7 = 1 ∧ g * z * g⁻¹ = z⁻¹ :=
  Certificates.certificate129009

theorem on_index_inner_dvd :
    (inner NativeSporadic.ON).index ∣ 4 :=
  CFSG.Sporadic.ONOddCore.r3e_on_outer_order_divides_four.1

noncomputable def onCarrierEquiv : NativeSporadic.ON ≃* NativeSporadic.Carrier .ONan :=
  MulEquiv.refl _

theorem on_center_dvd
    (L : Type) [Group L] [Finite L] (hq : CFSG.IsQuasisimple L)
    (e : L ⧸ Subgroup.center L ≃* NativeSporadic.ON) :
    Nat.card (Subgroup.center L) ∣ 3 := by
  have h := CFSG.GH74.Generic.card_center_dvd_hopfMultiplier hq (e.trans onCarrierEquiv)
  have hM : Nat.card (CFSG.RankThree.PerfectCover.hopfMultiplier (NativeSporadic.Carrier .ONan)) =
      3 := CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.ONCover.nativeRow_ONan
  rwa [hM] at h

theorem noIrrFFOffender_ONan_native :
    NoIrrFFOffender NativeSporadic.ON := by
  intro W _ _ hW L E hq hirr ⟨e⟩ hEN hE hel _
  obtain ⟨_, y, _, _, h, hy, hg⟩ := on_heisCfg
  have hy' : ∀ _ : Fin 1, y ^ 7 = 1 := fun _ => hy
  have hOut := fun (B : Subgroup (MulAut NativeSporadic.ON)) (_ : ∀ x ∈ B, ∀ y ∈ B,
      x * y = y * x) (_ : ∀ x ∈ B, x * x = 1) =>
    card_le_mul_card_inf_inner_of_index_dvd (by norm_num) on_index_inner_dvd B
  have hZ3 := on_center_dvd ↥L hq e
  rcases (Nat.dvd_prime Nat.prime_three).1 hZ3 with h1 | h3
  · refine exclusion_of_heisCfg_of_outer_of_inv_seven hW hq hirr hEN hE hel e hOut
      (by rw [h1]; norm_num) h hy' hg ?_
    rw [h1, card_ON]
    norm_num
  · have hb := two_pow_le_card_of_heisCfg_centerQuotient_of_inv_seven_of_three hW hirr e
      (by rw [h3]; norm_num) (by rw [h3]) h hy' hg
    refine exclusion_of_card_lt_of_outer hW hq hirr hEN hE hel e hOut (lt_of_lt_of_le ?_ hb)
    rw [h3, card_ON]
    norm_num

theorem noIrrFFOffender_ONan :
    NoIrrFFOffender (TauCeti.CFSGIndex.sporadic .ONan).Group :=
  noIrrFFOffender_transfer noIrrFFOffender_ONan_native
    CFSG.Sporadic.Bridge.ON.nonempty_mulEquiv

theorem gf2NoFFSporadicFor_ONan :
    GF2NoFFSporadicFor .ONan :=
  gf2NoFFSporadicFor_of_noIrrFFOffender noIrrFFOffender_ONan

end CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic
