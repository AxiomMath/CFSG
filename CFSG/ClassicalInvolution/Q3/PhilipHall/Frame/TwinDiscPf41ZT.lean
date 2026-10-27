module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscPf10Final
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscExitUAE5
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscBaseProved
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscExitE4Model
public import CFSG.ClassicalInvolution.Q3.PhilipHall.InductionBridge.Ih8
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf15Odd
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinMuSetting
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscExitU
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscExitUGen
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical

public section

set_option linter.unusedSectionVars false

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.Thompson
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinFrame
  CFSG.ClassicalInvolution.Uniform
open CFSG.ClassicalInvolution.Q3.Q3NL CFSG.ClassicalInvolution.Balance.Bootstrap

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

namespace TwinMu

section DataAt

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem exists_data_thompson_at (hΩ : HypOmegaGen Ω) {K K' J : Subgroup G} {z t : G} (hK : K ∈ Ω)
    (hz : IsUniqueInvolution K z) (hK' : K' ∈ twinSet Ω K) (hne : K' ≠ K)
    (hJ : J ∈ omegaOfSet Ω (twinSet Ω K)) (ht : IsUniqueInvolution J t) :
    ∃ (u : G) (W : Subgroup G), TwinDisc.Data Ω K K' z u J t W ∧ ThompsonWitness Ω K K' z u J := by
  classical
  have hK'Ω : K' ∈ Ω := hK'.1
  have hzK' : IsUniqueInvolution K' z := isUniqueInvolution_of_mem_twinSet hz hK'
  obtain ⟨S, R, R', T, hRsyl, hR'syl, hTsyl, hRS, hR'S, hTS, -, -, -⟩ :=
    Hat2A7S.exists_twinSylow hΩ hK hz hK' hne hJ
  obtain ⟨W, hW, hWD⟩ := Q3T8.Asc77.exists_W_of_isPGroup hΩ S.isPGroup'
  have hcW := Q3CL.Thompson.commutes_of_mem_WSet hΩ hW
  obtain ⟨ρa, hρaK, -⟩ := Q3T8.Asc77.T7D.exists_rep hΩ hW hK hRsyl
    (hWD R (mem_RSet_of_isSylow2In hK hRsyl) hRS)
  obtain ⟨ρb, hρbK, -⟩ := Q3T8.Asc77.T7D.exists_rep hΩ hW hK'Ω hR'syl
    (hWD R' (mem_RSet_of_isSylow2In hK'Ω hR'syl) hR'S)
  obtain ⟨ρc, hρcK, -⟩ := Q3T8.Asc77.T7D.exists_rep hΩ hW hJ.1 hTsyl
    (hWD T (mem_RSet_of_isSylow2In hJ.1 hTsyl) hTS)
  obtain ⟨w, hw, hw4⟩ := Q3T8.Asc77.Thompson.exists_orderOf_four hΩ hW ρa.hR
  obtain ⟨v, hv, hv4⟩ := Q3T8.Asc77.Thompson.exists_orderOf_four hΩ hW ρb.hR
  obtain ⟨wc, hwc, hwc4⟩ := Q3T8.Asc77.Thompson.exists_orderOf_four hΩ hW ρc.hR
  have hwK : w ∈ K ⊓ W := ⟨by rw [← hρaK]; exact ρa.hRK.1 hw.1, hw.2⟩
  have hvK : v ∈ K' ⊓ W := ⟨by rw [← hρbK]; exact ρb.hRK.1 hv.1, hv.2⟩
  have hwcJ : wc ∈ J ⊓ W := ⟨by rw [← hρcK]; exact ρc.hRK.1 hwc.1, hwc.2⟩
  have hw2 : w * w = z := sq_eq_involution_of_orderOf_four hz hwK.1 hw4
  have hv2 : v * v = z := sq_eq_involution_of_orderOf_four hzK' hvK.1 hv4
  have hwc2 : wc * wc = t := sq_eq_involution_of_orderOf_four ht hwcJ.1 hwc4
  have hzW : z ∈ W := hw2 ▸ W.mul_mem hwK.2 hwK.2
  have htW : t ∈ W := hwc2 ▸ W.mul_mem hwcJ.2 hwcJ.2
  have hwvW : w * v ∈ W := W.mul_mem hwK.2 hvK.2
  have hwv : w * v = v * w := hcW _ hwK.2 _ hvK.2
  have hu2 : (w * v) * (w * v) = 1 := by
    calc (w * v) * (w * v) = w * (v * w) * v := by simp only [mul_assoc]
      _ = w * (w * v) * v := by rw [← hwv]
      _ = (w * w) * (v * v) := by simp only [mul_assoc]
      _ = 1 := by rw [hw2, hv2]; exact hz.sq
  have hu1 : w * v ≠ 1 := by
    intro h
    have hwi : w = v⁻¹ := eq_inv_of_mul_eq_one_left h
    exact Hat2A7S.T7X.not_mem_inf_of_orderOf_four hΩ hK hK'Ω hne hw4 hwK.1
      (by rw [hwi]; exact K'.inv_mem hvK.1)
  have huz : w * v ≠ z := by
    intro h
    have hwi : w = z * v⁻¹ := by rw [← h]; group
    exact Hat2A7S.T7X.not_mem_inf_of_orderOf_four hΩ hK hK'Ω hne hw4 hwK.1
      (by rw [hwi]; exact K'.mul_mem hzK'.mem (K'.inv_mem hvK.1))
  have htu : t * (w * v) = (w * v) * t := hcW _ htW _ hwvW
  refine ⟨w * v, W, ⟨?_, hW, hzW, htW⟩, ?_⟩
  swap
  · unfold ThompsonWitness
    exact ⟨W, hW, ρa, ρb, ρc, w, v, hρaK, hρbK, hρcK, hwK, hvK, hw2, hv2, rfl⟩
  exact
    { mem := hK
      hz := hz
      hK' := hK'
      hne := hne
      hu := Subgroup.mul_mem _ (Subgroup.mem_sup_left hwK.1) (Subgroup.mem_sup_right hvK.1)
      hu2 := hu2
      hu1 := hu1
      huz := huz
      hJ := hJ
      ht := ht
      htu := htu }

end DataAt

end TwinMu

namespace TwinDisc

@[expose] def DiscUOddD (n : ℕ) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t₀ : Y)
    (K K' : Subgroup Y) (z u : Y) (J : Subgroup Y) (t : Y) (W : Subgroup Y),
    Setting n R S t₀ K K' z u J t W →
      ¬ SecConnU (CoreAssembly.conjClass (tightCore R)) u →
        ∀ M ∈ secFam (CoreAssembly.conjClass (tightCore R)) u,
          ∀ zb : ↥(coreHull (CoreAssembly.conjClass (tightCore R)) u) ⧸
              classicalInvolutionOddCore ↥(coreHull (CoreAssembly.conjClass (tightCore R)) u),
            IsUniqueInvolution M zb → oddCoreImg (Subgroup.centralizer ({zb} : Set _)) = ⊥

theorem discUOddD_of_oddCentEdge {n : ℕ} (hcit : CIT3Below n) (hP : TL4.TightBelowRPlus 3 n)
    (h4 : Thm4RTwinBelow 3 n) (hOE : OddCentEdge n) : DiscUOddD n := by
  intro Y _ _ R S t₀ K K' z u J t W s hdisc
  set Ω := CoreAssembly.conjClass (tightCore R) with hΩdef
  have hf := s.data.frame
  have hΩ : HypOmegaGen Ω := s.core.hyp
  obtain ⟨h2, hq, hA⟩ := setup_members s
  have hc2 : IsPGroup 2 (Subgroup.zpowers u) :=
    CFSG.ClassicalInvolution.Asc77.ExactLayer.isPGroup_zpowers_of_sq_eq_one hf.hu2
  have htr : ∀ M ∈ Ω, ∀ N ∈ Ω, ∃ g : Y, conjSub g M = N := TwinFrame.trans_conjClass _
  obtain ⟨J', R₁, R₁', T, T', x, y, hJ'tw, hJ'ne, hJ't, hF⟩ := exists_frame hΩ htr h2 s.data
  have hJΩ : J ∈ Ω := hf.hJ.1
  have hJtq : J ∈ tqMembers3 Ω u :=
    ⟨hJΩ, TwinADescent3.mem_tq_of_sylCent hΩ h2 hJΩ ⟨T, hF.hT, hF.le_centralizer_u.1⟩⟩
  have hlt : Nat.card (↥(coreHull Ω u) ⧸ classicalInvolutionOddCore ↥(coreHull Ω u)) < n :=
    s.core.card ▸ card_secQuot_lt (not_mem_center_of_ne_one s hf.hu1)
  have hS := q8Section_secFam hΩ hc2 h2 hq hA
  have htrans : ∀ M ∈ secFam Ω u, ∀ N ∈ secFam Ω u, ∃ g, conjSub g M = N := by
    rcases dichotomy_secFam h4 hlt hΩ hc2 h2 hq hA hJtq with hd | hd
    · exact absurd (fun M hM N hN =>
        (reflTransGen_dstarAdj_symm (secImg_mem_secFam hJtq) (hd M hM)).trans (hd N hN)) hdisc
    · intro M hM N hN
      obtain ⟨a, ha⟩ := hd M hM
      obtain ⟨b, hb⟩ := hd N hN
      refine ⟨b * a⁻¹, ?_⟩
      rw [← hb, ← ha, ← conjSub_mul]
      congr 1
      group
  intro M hM zb hzb
  exact hOE hcit hP _ hlt _ hS htrans (section_edge s) M hM zb hzb

theorem discUNoExitAE5_of_oddD {n : ℕ} (hmodel : ExitE4.E4ModelDStar)
    (hP : TL4.TightBelowRPlus 3 n) (h4 : Thm4RTwinBelow 3 n) (hOdd : DiscUOddD n) :
    DiscUNoExitAE5 n := by
  intro Y _ _ R S t₀ K K' z u J t W s hdisc
  set Ω := CoreAssembly.conjClass (tightCore R) with hΩdef
  have hf := s.data.frame
  have hΩ : HypOmegaGen Ω := s.core.hyp
  obtain ⟨h2, hq, hA⟩ := setup_members s
  have hc2 : IsPGroup 2 (Subgroup.zpowers u) :=
    CFSG.ClassicalInvolution.Asc77.ExactLayer.isPGroup_zpowers_of_sq_eq_one hf.hu2
  have htr : ∀ M ∈ Ω, ∀ N ∈ Ω, ∃ g : Y, conjSub g M = N := TwinFrame.trans_conjClass _
  obtain ⟨J', R₁, R₁', T, T', x, y, hJ'tw, hJ'ne, hJ't, hF⟩ := exists_frame hΩ htr h2 s.data
  have hJΩ : J ∈ Ω := hf.hJ.1
  have hJtq : J ∈ tqMembers3 Ω u :=
    ⟨hJΩ, TwinADescent3.mem_tq_of_sylCent hΩ h2 hJΩ ⟨T, hF.hT, hF.le_centralizer_u.1⟩⟩
  have hlt : Nat.card (↥(coreHull Ω u) ⧸ classicalInvolutionOddCore ↥(coreHull Ω u)) < n :=
    s.core.card ▸ card_secQuot_lt (not_mem_center_of_ne_one s hf.hu1)
  have hS := q8Section_secFam hΩ hc2 h2 hq hA
  have htrans : ∀ M ∈ secFam Ω u, ∀ N ∈ secFam Ω u, ∃ g, conjSub g M = N := by
    rcases dichotomy_secFam h4 hlt hΩ hc2 h2 hq hA hJtq with hd | hd
    · exact absurd (fun M hM N hN =>
        (reflTransGen_dstarAdj_symm (secImg_mem_secFam hJtq) (hd M hM)).trans (hd N hN)) hdisc
    · intro M hM N hN
      obtain ⟨a, ha⟩ := hd M hM
      obtain ⟨b, hb⟩ := hd N hN
      refine ⟨b * a⁻¹, ?_⟩
      rw [← hb, ← ha, ← conjSub_mul]
      congr 1
      group
  exact ExitU.noExit_or_ae5 hmodel hP.thmD.d2 hlt hS htrans (section_edge s)
    (fun M hM zb hzb => hOdd Y R S t₀ K K' z u J t W s hdisc M hM zb hzb) hdisc

theorem discZT_proved {n : ℕ} (hcit : CIT3Below n) (hP : TL4.TightBelowRPlus 3 n)
    (h4 : Thm4RTwinBelow 3 n) : DiscZT n :=
  discZT_of_cases hcit (InductionBridge.ih8T_of_cit3Below hcit) hP
    (discUNoExitAE5_of_oddD ExitE4.e4ModelDStar_of_certs hP h4
      (discUOddD_of_oddCentEdge hcit hP h4 (oddCentEdge_proved n)))
    (discUAE5_of_cert h4)

@[expose] def DiscNormCentT (n : ℕ) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t₀ : Y)
    (K K' : Subgroup Y) (z u : Y) (J : Subgroup Y) (t : Y) (W : Subgroup Y),
    Setting n R S t₀ K K' z u J t W →
      TwinMu.ThompsonWitness (CoreAssembly.conjClass (tightCore R)) K K' z u J →
      alphaOf (Subgroup.closure ({u, z} : Set Y)) = ⊥ →
        ¬ rLayer (CoreAssembly.conjClass (tightCore R)) (t * z) ≤
            sigmaGen (CoreAssembly.conjClass (tightCore R)) K →
          Subgroup.normalizer (K : Set Y) ≤ Subgroup.centralizer ({t * z} : Set Y)

theorem discNormCent_of_normCentT {n : ℕ} (I : TwinDiscBase n) (h : DiscNormCentT n) :
    DiscNormCent n := by
  intro Y _ _ R S t₀ K K' z u J t W s hα hD
  have hf := s.data.frame
  obtain ⟨u'', W'', d'', hw⟩ :=
    TwinMu.exists_data_thompson_at s.core.hyp hf.mem hf.hz hf.hK' hf.hne hf.hJ hf.ht
  have s'' : Setting n R S t₀ K K' z u'' J t W'' := ⟨s.core, s.disc, d''⟩
  have hα'' : alphaOf (Subgroup.closure ({u'', z} : Set Y)) = ⊥ := by
    rw [← (alphaStepsBase I s'').alpha_zt d''.frame, (alphaStepsBase I s).alpha_zt hf, hα]
  exact h Y R S t₀ K K' z u'' J t W'' s'' hw hα'' hD

theorem twinCoreDiscPerp_of_inputsPf35 {n : ℕ} (hE : TwinThmE n) (hN : DiscNormCent n)
    (h4 : Thm4RTwinBelow 3 n) (hcit : CIT3Below n) (hP : TL4.TightBelowRPlus 3 n) :
    TwinCoreDiscPerp n :=
  twinCoreDiscPerp_of_inputsPf10
    { thmE := hE
      base := twinDiscBase_of_thm4 h4
      normCent := hN
      zt := discZT_proved hcit hP h4
      thm4 := h4
      cit := hcit
      pkg := hP
      exit := dstarExitQ8_proved ExitE4.e4ModelDStar_of_certs hcit hP }

theorem discNormCent_of_disc15 {n : ℕ} (hT : DiscTqTz n) (h15 : Disc15 n) : DiscNormCent n := by
  intro Y _ _ R S t₀ K K' z u J t W s hα hD
  have hP : Q3CL.PartIHypG (CoreAssembly.conjClass (tightCore R)) := TwinPerp.partIHypG s.core
  have hne : dComp (CoreAssembly.conjClass (tightCore R)) K ≠
      dstarComp (CoreAssembly.conjClass (tightCore R)) K :=
    fun heq => hD (Pf2.rLayer_tz_le_sigmaGen_of_eq hT s hα heq)
  exact normalizer_le_centralizer_tz hP s.data hne (h15 Y R S t₀ K K' z u J t W s hα hD)

theorem twinCoreDiscPerp_of_inputsPf36 {n : ℕ} (hE : TwinThmE n) (h15 : Disc15 n)
    (h4 : Thm4RTwinBelow 3 n) (hcit : CIT3Below n) (hP : TL4.TightBelowRPlus 3 n) :
    TwinCoreDiscPerp n :=
  twinCoreDiscPerp_of_inputsPf35 hE
    (discNormCent_of_disc15
      (discTqTz_of_conn (twinDiscBase_of_thm4 h4)
        (discSecConnTz_of h4 (dstarConnectedTwinQ8Below_of_exit hcit hP
          (dstarExitQ8_proved ExitE4.e4ModelDStar_of_certs hcit hP)))) h15)
    h4 hcit hP

@[expose] def Disc15T (n : ℕ) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t₀ : Y)
    (K K' : Subgroup Y) (z u : Y) (J : Subgroup Y) (t : Y) (W : Subgroup Y),
    Setting n R S t₀ K K' z u J t W →
      TwinMu.ThompsonWitness (CoreAssembly.conjClass (tightCore R)) K K' z u J →
      alphaOf (Subgroup.closure ({u, z} : Set Y)) = ⊥ →
        ¬ rLayer (CoreAssembly.conjClass (tightCore R)) (t * z) ≤
            sigmaGen (CoreAssembly.conjClass (tightCore R)) K →
          ∀ M ∈ dComp (CoreAssembly.conjClass (tightCore R)) K,
            M ≤ Subgroup.centralizer ({t * z} : Set Y)

theorem disc15_of_disc15T {n : ℕ} (I : TwinDiscBase n) (h : Disc15T n) : Disc15 n := by
  intro Y _ _ R S t₀ K K' z u J t W s hα hD
  have hf := s.data.frame
  obtain ⟨u'', W'', d'', hw⟩ :=
    TwinMu.exists_data_thompson_at s.core.hyp hf.mem hf.hz hf.hK' hf.hne hf.hJ hf.ht
  have s'' : Setting n R S t₀ K K' z u'' J t W'' := ⟨s.core, s.disc, d''⟩
  have hα'' : alphaOf (Subgroup.closure ({u'', z} : Set Y)) = ⊥ := by
    rw [← (alphaStepsBase I s'').alpha_zt d''.frame, (alphaStepsBase I s).alpha_zt hf, hα]
  exact h Y R S t₀ K K' z u'' J t W'' s'' hw hα'' hD

end TwinDisc

