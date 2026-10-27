module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23FusMain
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23FusExit
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23FusPair
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23FusW

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Q3.Q3NL CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge CFSG.ClassicalInvolution.Disconnected
open scoped commutatorElement


section E6NE

variable {n : ℕ}

@[expose] def P23E6NE' (n : ℕ) : Prop :=
  CIT3Below n → TL4.TightBelowRPlus 3 n →
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y) (K' W : Subgroup Y)
    (u e g : Y), P23Cfg n Y R S t K' W u e g → SecNoExit R u → YOrth R u → SecNoExit R e

theorem p23E6NE'_proved (hT : TwinThmE.T4Supply)
    (hmodel : TwinDisc.ExitE4.E4ModelDStar) (hD4 : TwinCentRes.ModelFactD42) (hMu : P23E4Mu n) :
    P23E6NE' n := by
  intro hcit hP Y _ _ R S t K' W u e g hc hnoU _
  by_contra hno
  obtain ⟨Q, Q', hTu, hTe⟩ := Fus.layerTwins_both hc
  obtain ⟨x, hxu, hxodd, hxQ, hxQ', ⟨q, hq, hxq⟩, hmove⟩ :=
    Fus.lie_fusion_at hcit hP hc.std.perp hTu hnoU
  have hΩ : HypOmegaGen (Om R) := (CoreData.of_S hc.std.perp.core).hyp
  have hwQ' : u * e ∈ Q' := involution_mem_sylow hΩ hTu.hJ'.1 hTu.hw' hTu.hQ'
  have hxe := Fus.mem_cent_e_of_cent_u hc hxu (hxQ' _ hwQ')
  rcases Fus.p23E4ExitCases_of_mu hT hmodel hD4 hMu hcit hP Y R S t K' W u e g hc hno with
    hpair | ⟨hV, h2⟩ | h5 | h6
  · exact Fus.pair_impossible hc hpair
  · exact Fus.wshape_false hc.std.perp hTe h2 hV hxe hxQ hmove
  · obtain ⟨I⟩ := h5
    exact hxq (Fus.nside_ae hc.std.perp hTe (Or.inl rfl) I hxe hxodd hxQ hxQ' q hq)
  · obtain ⟨I⟩ := h6
    exact hxq (Fus.nside_ae hc.std.perp hTe (Or.inr rfl) I hxe hxodd hxQ hxQ' q hq)

end E6NE

section YType

variable {n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {K' W : Subgroup Y} {u e g : Y}

theorem p23_yType' (hx : P23Y5Exit n) (hi : P23Y5Ident n) (hmem : P23Members n)
    (hcit : CIT3Below n) (hP : TL4.TightBelowRPlus 3 n) (hc : P23Cfg n Y R S t K' W u e g) :
    (u * e ∈ zStarOf (rLayer (Om R) u) ∨ SecAE R u 5) ∨ (SecNoExit R u ∧ YOrth R u) := by
  by_cases hno : SecNoExit R u
  · have hu1 : u ≠ 1 := hc.data.hu1
    obtain ⟨D⟩ := secDecomp_of_noExit hcit hP hc.std.perp hc.data.hu2 hu1
      (hmem Y R S t K' W u e g hc).2 hno
    rcases hi hcit hP Y R S t K' W u e g hc hno D with h | h
    · exact Or.inr ⟨hno, Or.inl ⟨D, h⟩⟩
    · exact Or.inr ⟨hno, Or.inr ⟨D, h⟩⟩
  · rcases hx hcit hP Y R S t K' W u e g hc hno with h | h
    · exact Or.inl (Or.inl h)
    · exact Or.inl (Or.inr h)

theorem yType_of_exit' (hNE : P23E6NE' n) (hcit : CIT3Below n) (hP : TL4.TightBelowRPlus 3 n)
    (hc : P23Cfg n Y R S t K' W u e g) (hno : ¬ SecNoExit R e)
    (hY : (u * e ∈ zStarOf (rLayer (Om R) u) ∨ SecAE R u 5) ∨ (SecNoExit R u ∧ YOrth R u)) :
    u * e ∈ zStarOf (rLayer (Om R) u) ∨ SecAE R u 5 := by
  rcases hY with h | ⟨hnoU, hYo⟩
  · exact h
  · exact absurd (hNE hcit hP Y R S t K' W u e g hc hnoU hYo) hno

end YType

section Assembly

open CFSG.ClassicalInvolution.Q8P.P24 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinVtx
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinCentRes
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinEdge
open CFSG.ClassicalInvolution.Balance

theorem twinPerp233E_of_exits' {n : ℕ} (hE : TwinThmE.TwinThmEP n) (hcit : CIT3Below n)
    (hP : TL4.TightBelowRPlus 3 n) (hT : TwinThmE.T4Supply) (hD4 : TwinCentRes.ModelFactD42)
    (hM12 : TwinCentRes.ModelFactM12) (hE4x : P23E4Exit n) (hY5x : P23Y5Exit n)
    (hE6NE : P23E6NE' n) (hE7Y : P23E7Y n) (hE8Z : P23E8Z n) (hE8A : P23E8A n)
    (hYX : P23YExitNE' n) (hCent : P23LiftCentF n) :
    TwinPerp233E n := by
  have hAlpha := p23Alpha_proved hD4 hM12 hT hcit hP
  have hTwo := p23TwoN_of_fuseN hE hcit hP (p23FuseN hP)
  have hE4i := p23E4Ident_of_trans_type (p23E4Trans_of_t4 hT)
    (p23E4Type_of_dim (p23E4Dim n) (p23E4Trans_of_t4 hT))
  have hY5i := p23Y5Ident_of_trans_type (p23Y5Trans_of_t4 hT)
    (p23Y5Type_of_dimC (p23Y5DimC n) (p23Y5Trans_of_t4 hT))
  intro Y _ _ R S t hPerp h2 W hW htW hS4
  by_cases hc : WCentralNontrivial W
  swap
  · exact Or.inl hc
  by_cases hex : TwinE4 Y
  · exact Or.inr (Or.inl hex)
  right; right
  obtain ⟨K', hK', hne⟩ := hPerp.core.twin
  have hstd : P23Std n Y R S t K' W := ⟨hPerp, h2, hK', hne, hW, htW, hS4, hc, hex⟩
  obtain ⟨u, e, g, hd⟩ := p23Setup n Y R S t K' W hstd
  have hcfg : P23Cfg n Y R S t K' W u e g := ⟨hstd, hd⟩
  have hY := p23_yType hY5x hY5i (p23Members n) hcit hP hcfg
  have hY' := p23_yType' hY5x hY5i (p23Members n) hcit hP hcfg
  obtain ⟨hno, hEorth⟩ : SecNoExit R e ∧ SecOrthLift R e 6 (piSign 3 1) := by
    rcases p23_e4X hE4x hE4i (p23Members n) hcit hP hcfg with ⟨hnx, h | h⟩ | h
    · exact absurd h (hE7Y hcit hP Y R S t K' W u e g hcfg hnx
        (yType_of_exit' hE6NE hcit hP hcfg hnx hY'))
    · rcases yType_of_exit' hE6NE hcit hP hcfg hnx hY' with hz | h5
      · exact absurd (hE8Z hcit hP Y R S t K' W u e g hcfg hnx hz h) hex
      · exact absurd (hE8A hcit hP Y R S t K' W u e g hcfg hnx h5 h) hex
    · exact h
  obtain ⟨hnoU, hYo⟩ : SecNoExit R u ∧ YOrth R u := by
    by_cases hnoU : SecNoExit R u
    · refine ⟨hnoU, ?_⟩
      obtain ⟨D⟩ := secDecomp_of_noExit hcit hP hPerp hcfg.data.hu2 hcfg.data.hu1
        (p23Members n Y R S t K' W u e g hcfg).2 hnoU
      rcases hY5i hcit hP Y R S t K' W u e g hcfg hnoU D with h | h
      · exact Or.inl ⟨D, h⟩
      · exact Or.inr ⟨D, h⟩
    · exact absurd (hYX hcit hP Y R S t K' W u e g hcfg hnoU hno hEorth) id
  obtain ⟨hodd, halpha⟩ := hAlpha Y R S t K' W u e g hcfg hY
  have hΓz := gamma_t hP hcfg hno
  have hΓu := gamma_u (hT n hcit hP) hP hcfg hnoU hYo
  have hα1 : alphaOf (Subgroup.closure ({u, t} : Set Y)) = ⊥ :=
    alpha_eq_bot_of_gamma (CoreData.of_S hPerp.core).oddFree
      (hTwo Y R S t K' W u e g hcfg hno) hΓz hΓu hodd halpha
  have hTwo' := hTwo Y R S t K' W u e g hcfg hno
  have hOddC := p23_oddCent_eq_bot₂ hD4 hT hcit hP hcfg hno hα1 halpha hTwo'
  obtain ⟨Λ, h1, h2⟩ := (p23LiftLF_of_subF hE hT hD4 hM12 (p23LiftSubF_of_centF hCent)) hcit hP
    Y R S t K' W u e g hcfg hα1 hno hnoU hEorth hYo hOddC
  have hC' := CoreData.of_S hPerp.core
  have hz : IsUniqueInvolution (tightCore R) t := Inner.isUniqueInvolution_core hC'.datum
  exact TwinPerpV3.longFundSetE3_of_lifts hC'.hyp hz hOddC Λ h1 h2

theorem twinPerp233E_of_steps₃₄ {n : ℕ} (hE : TwinThmE.TwinThmEP n) (hcit : CIT3Below n)
    (hP : TL4.TightBelowRPlus 3 n) (hT : TwinThmE.T4Supply)
    (hmodel : TwinDisc.ExitE4.E4ModelDStar) (hD4 : TwinCentRes.ModelFactD42)
    (hM12 : TwinCentRes.ModelFactM12)
    (hE4m : P23E4Mu n) (hMu : P23Y5SecMuE4Ex n)
    (hE6NE : P23E6NE' n) (hE7Y : P23E7Y n) (hE8Z : P23E8Z n) (hE8A : P23E8A n)
    (hYX : P23YExitNE' n) (hCent : P23LiftCentF n) :
    TwinPerp233E n :=
  twinPerp233E_of_exits' hE hcit hP hT hD4 hM12
    (p23E4Exit_of_mu hT hmodel hD4 (TwinPerp23.W.p23E4Ae5_proved n)
      (TwinPerp23.W.p23E4W_of_img (p23E4WImg_proved n)) hE4m)
    (p23Y5Exit_of_secMuE4Ex hT hmodel hD4 hMu) hE6NE hE7Y hE8Z hE8A hYX hCent

theorem p23YExitNE'_of_ctDec' {n : ℕ}
    (hE : TwinThmE.TwinThmEP n) (hT : TwinThmE.T4Supply) (hD4 : TwinCentRes.ModelFactD42)
    (hM12 : TwinCentRes.ModelFactM12) (hY5x : P23Y5Exit n) (hCt : R56.P23CtDec n) :
    P23YExitNE' n :=
  R56.p23YExitNE'_of_split hE hT hD4 hM12 hY5x (R56.p23YExitZC_of_ctDec hCt)
    (Fus.p23YExitAE_proved n)

theorem twinPerp233E_of_steps₃₅ {n : ℕ}
    (hE : TwinThmE.TwinThmEP n) (hcit : CIT3Below n)
    (hP : TL4.TightBelowRPlus 3 n) (hT : TwinThmE.T4Supply)
    (hmodel : TwinDisc.ExitE4.E4ModelDStar) (hD4 : TwinCentRes.ModelFactD42)
    (hM12 : TwinCentRes.ModelFactM12)
    (hE4m : P23E4Mu n) (hMu : P23Y5SecMuE4Ex n) (hE7Y : P23E7Y n) (hE8Z : P23E8Z n)
    (hE8A : P23E8A n) (hCt : R56.P23CtDec n) (hCent : P23LiftCentF n) :
    TwinPerp233E n :=
  twinPerp233E_of_steps₃₄ hE hcit hP hT hmodel hD4 hM12 hE4m hMu
    (p23E6NE'_proved hT hmodel hD4 hE4m) hE7Y hE8Z hE8A
    (p23YExitNE'_of_ctDec' hE hT hD4 hM12 (p23Y5Exit_of_secMuE4Ex hT hmodel hD4 hMu) hCt) hCent

end Assembly

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23
