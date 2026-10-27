module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscPf10Frame
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscPf11Twin
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinDiscClaims
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinDiscModel
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinDiscSecHyp
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscPf9U

public section

set_option linter.unusedSectionVars false

namespace CFSG.CGT.PushingUpLit.SolKNA.R4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.Thompson
open CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc
open CFSG.ClassicalInvolution.Q3.Q3NL CFSG.ClassicalInvolution.Balance.Bootstrap
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinFrame
open scoped commutatorElement


section U

variable {r n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t₀ : Y}
  {K K' J W : Subgroup Y} {z u t : Y}

theorem secConnUR (hr : 4 ≤ r) (h4 : Thm4RTwinBelow r n) (hT : Thm1RTwinInO2 r n)
    (s : SettingR r n R S t₀ K K' z u J t W) :
    SecConnU (CoreAssembly.conjClass (tightCore R)) u := by
  set Ω := CoreAssembly.conjClass (tightCore R) with hΩdef
  have hf := s.data.frame
  have hΩ : HypOmegaGen Ω := s.core.hyp
  have hc2 : IsPGroup 2 (Subgroup.zpowers u) :=
    CFSG.ClassicalInvolution.Asc77.ExactLayer.isPGroup_zpowers_of_sq_eq_one hf.hu2
  obtain ⟨h2, hq, hA⟩ := setup_membersR s
  have htr : ∀ M ∈ Ω, ∀ N ∈ Ω, ∃ g : Y, conjSub g M = N := TwinFrame.trans_conjClass _
  obtain ⟨J', R₁, R₂, T, T', x, y, hJ'tw, hJ'ne, hJ't, hF⟩ := exists_frame hΩ htr h2 s.data
  have hJtq : J ∈ tqMembers3 Ω u := mem_tqMembers_u_J hΩ htr h2 s.data
  have hJ'tq : J' ∈ tqMembers3 Ω u :=
    ⟨hJ'tw.1, TwinADescent3.mem_tq_of_sylCent hΩ h2 hJ'tw.1 ⟨T', hF.hT', hF.le_centralizer_u.2⟩⟩
  have hT'J : T' ≤ Subgroup.normalizer (J : Set Y) :=
    hF.hT'.1.trans (Sec6Gen.le_normalizer_of_twin hΩ hJ'tw.1 hf.hJ.1 hJ'ne hJ't hf.ht)
  have hedge := omegaNbr_secImg hΩ hc2 hJtq hJ'tq hF.hT hF.hT' hF.le_centralizer_u.1
    hF.le_centralizer_u.2 hF.cTT' hT'J
  obtain ⟨htC, htY, hJt⟩ := isUniqueInvolution_secImg hΩ hc2 hJtq hf.ht
  obtain ⟨htC', htY', hJ't'⟩ := isUniqueInvolution_secImg hΩ hc2 hJ'tq hJ't
  have htw : ∃ K₁ ∈ TwinDisc.secFam Ω u, ∃ K₁' ∈ twinSet (TwinDisc.secFam Ω u) K₁, K₁' ≠ K₁ :=
    ⟨secImg Ω u J, secImg_mem_secFam hJtq, secImg Ω u J',
      ⟨secImg_mem_secFam hJ'tq, _, hJt, hJ't'⟩, hedge.2.1⟩
  have hlt : Nat.card (↥(coreHull Ω u) ⧸ classicalInvolutionOddCore ↥(coreHull Ω u)) < n :=
    s.core.card ▸ card_secQuot_lt (not_mem_center_of_ne_oneR s hf.hu1)
  rcases dichotomy_secFamR h4 hlt hΩ hc2 h2 hq hA hJtq with hconn | horb
  · exact T3.dstarConnected_of_pivot (secImg_mem_secFam hJtq) hconn
  · have htrans : ∀ K₁ ∈ TwinDisc.secFam Ω u, ∀ L ∈ TwinDisc.secFam Ω u,
        ∃ g : ↥(coreHull Ω u) ⧸ classicalInvolutionOddCore ↥(coreHull Ω u), conjSub g K₁ = L := by
      intro K₁ hK₁ L hL
      obtain ⟨y₁, hy₁⟩ := horb K₁ hK₁
      obtain ⟨y₂, hy₂⟩ := horb L hL
      exact ⟨y₂ * y₁⁻¹, by rw [conjSub_mul, ← hy₁, conjSub_inv_conjSub, hy₂]⟩
    have hgen : omegaGen (TwinDisc.secFam Ω u) = ⊤ :=
      omegaGen_quotFamily_eq_top _ _
        (omegaGen_restrictFamily_eq_top (cFam Ω u) (coreHull Ω u) rfl)
    exact dstarConnected_of_inO2_R hr hT hlt (hypOmegaGen_secFam hΩ hc2)
      (secFam_twoGroup h2) (secFam_quat hc2 hq) oddCore_quot_eq_bot (secFam_aEmpty hΩ hA hc2)
      hgen htrans htw

theorem discTqUR_of (hr : 4 ≤ r) (h4 : Thm4RTwinBelow r n) (hT : Thm1RTwinInO2 r n) :
    DiscTqUR r n := by
  intro Y _ _ R S t₀ K K' z u J t W s hα M hM
  set Ω := CoreAssembly.conjClass (tightCore R) with hΩdef
  have hf := s.data.frame
  have hΩ : HypOmegaGen Ω := s.core.hyp
  obtain ⟨h2, hq, hA⟩ := setup_membersR s
  have hc2 : IsPGroup 2 (Subgroup.zpowers u) :=
    CFSG.ClassicalInvolution.Asc77.ExactLayer.isPGroup_zpowers_of_sq_eq_one hf.hu2
  have hconnU := secConnUR hr h4 hT s
  obtain ⟨g₀, -, hJ₀nbr, hJ₀⟩ := exists_sylCent_u hΩ hf
  have hJ₀tq : conjSub g₀ J ∈ tqMembers3 Ω u :=
    ⟨hJ₀.1, TwinADescent3.mem_tq_of_sylCent hΩ h2 hJ₀.1 hJ₀.2⟩
  have hJ₀d : conjSub g₀ J ∈ dComp Ω K :=
    T7A.mem_dComp_of_mem_omegaNbr (hJ₀nbr.2 K (mem_twinSet_self hf.mem hf.hz))
  have hJ₀ds : conjSub g₀ J ∈ dstarComp Ω K := mem_dstarComp_of_mem_dComp_gen hΩ hJ₀d
  have hMtq : M ∈ tqMembers3 Ω u :=
    ⟨hM.1, TwinADescent3.mem_tq_of_sylCent hΩ h2 hM.1 hM.2⟩
  obtain ⟨m, hm, J', -, hJ'd, hMeq⟩ := exists_conj_tq_of_connected hΩ hc2 hJ₀tq
    (fun M' hM' => hconnU _ (secImg_mem_secFam hJ₀tq) M' hM') M hMtq
  have hmz : m * z = z * m :=
    oddCore_comm_of_alpha hα (Subgroup.subset_closure (by simp)) hf.hu1
      (Subgroup.subset_closure (by simp)) hm
  have hmσ : m ∈ sigmaStarNorm Ω K :=
    centralizer_le_sigmaStarNorm_z hΩ hf.mem hf.hz (Subgroup.mem_centralizer_singleton_iff.mpr hmz)
  have hJ'ds : J' ∈ dstarComp Ω K := by
    rw [T7A.dstarComp_eq_of_mem hf.mem hJ₀ds] at hJ'd
    exact hJ'd
  rw [hMeq]
  exact ((mem_sigmaStarNorm_iff.mp hmσ) J').mp hJ'ds

end U

end CFSG.CGT.PushingUpLit.SolKNA.R4
