module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinDisc15E2
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinDiscSecHyp
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf12Coprime

public section

set_option linter.unusedSectionVars false

namespace CFSG.CGT.PushingUpLit.SolKNA.R4.Disc15

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.Thompson
open CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinFrame
open CFSG.ClassicalInvolution.Q3.Q3NL CFSG.ClassicalInvolution.Balance.Bootstrap


section SecD2

variable {r n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t₀ : Y}
  {K K' J W : Subgroup Y} {z u t : Y}

theorem sec_omegaStarNbr (hr : 4 ≤ r) (h4 : Thm4RTwinBelow r n) (hT : Thm1RTwinInO2 r n)
    (s : SettingR r n R S t₀ K K' z u J t W) {M₁ M₂ : Subgroup Y}
    (hM₁ : M₁ ∈ tqMembers3 (CoreAssembly.conjClass (tightCore R)) z)
    (hM₂ : M₂ ∈ tqMembers3 (CoreAssembly.conjClass (tightCore R)) z)
    (hne : secImg (CoreAssembly.conjClass (tightCore R)) z M₂ ≠
      secImg (CoreAssembly.conjClass (tightCore R)) z M₁) :
    secImg (CoreAssembly.conjClass (tightCore R)) z M₂ ∈
      omegaStarNbr (TwinDisc.secFam (CoreAssembly.conjClass (tightCore R)) z)
        (secImg (CoreAssembly.conjClass (tightCore R)) z M₁) := by
  classical
  set Ω := CoreAssembly.conjClass (tightCore R) with hΩdef
  have hΩ : HypOmegaGen Ω := s.core.hyp
  have hf := s.data.frame
  have hc2 : IsPGroup 2 (Subgroup.zpowers z) := isPGroup_zpowers_of_uniqueInvolution hf.hz
  obtain ⟨h2mod, hq, hA⟩ := setup_membersR s
  have hΦ : HypOmegaGen (TwinDisc.secFam Ω z) := hypOmegaGen_secFam hΩ hc2
  have hinO2 := hinO2_sec h4 hT s
  have hodd := (oddCore_quot_eq_bot : classicalInvolutionOddCore
    (↥(coreHull Ω z) ⧸ classicalInvolutionOddCore ↥(coreHull Ω z)) = ⊥)
  have h2Φmod := secFam_twoGroup (c := z) h2mod
  have hqΦ := secFam_quat hc2 hq
  have hAΦ := secFam_aEmpty hΩ hA hc2
  have h2Φ : ∀ L ∈ TwinDisc.secFam Ω z, IsPGroup 2 ↥L := by
    intro L hL
    obtain ⟨z', hz'⟩ := Sec6Gen.exists_uniqueInvolution hΦ hL
    obtain ⟨Q, hQn, hQ2, hzQ⟩ := hinO2 L hL z' hz'
    have hθ := TwinExitPf12.oddCoreIn_centralizer_eq_bot_of_mem_normal hodd hQn hQ2 hzQ
    exact isPGroup_of_oddCent hΦ hL hz' hθ (h2Φmod L hL)
  have h8Φ : ∀ L ∈ TwinDisc.secFam Ω z, Nat.card ↥L = 2 ^ r := by
    intro L hL
    obtain ⟨e⟩ := hqΦ L hL L ⟨le_rfl, h2Φ L hL, fun V' hV'J _ hJV' => le_antisymm hV'J hJV'⟩
    rw [Nat.card_congr e.toEquiv]
    exact card_quaternion_pow (by omega)
  have hL₁ := secImg_mem_secFam hM₁
  have hL₂ := secImg_mem_secFam hM₂
  obtain ⟨v, hv⟩ := Sec6Gen.exists_uniqueInvolution hΦ hL₁
  have hvJ := mem_normalizer_of_four_le hr hΦ h2Φ h8Φ hinO2 hL₂ hL₁ hv
  exact mem_omegaStarNbr_of_normalizes hΦ h2Φ h8Φ hAΦ hodd hinO2 hL₁ hL₂ hne hv hvJ

end SecD2

end CFSG.CGT.PushingUpLit.SolKNA.R4.Disc15
