module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8YCfgFin
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8S12Syl8
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8S12Small
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8S12Ly
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8S12J1
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8S12M23
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8S12Bender
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8S12M12
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8S12M22
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8S12J2
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8S12J3
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8S12L34
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8S12McL
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67LyAllInnerThm

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Subgroup CFSG CFSG.Blueprint CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Signalizer.Odd87
  CFSG.GH74.GLS.Stage2.Bender.Thm1.LyOut

variable {A : Type} [Group A] [Finite A] {zb : A} {Sb Vb J : Subgroup A}

theorem AFrame.false_of_J3
    (hfr : AFrame A zb Sb Vb) (hJ : IsComponent J)
    (hnc : ¬ Vb ≤ centralizer (J : Set A))
    (h : NativeSporadic.IsSporadic (↥J ⧸ center ↥J) .J3) : False := by
  have hN := card_of_isSporadic_J3 h
  have hY : ¬ KindFactorAll Kind.ly (↥J ⧸ center ↥J) := fun hK =>
    (by decide : ¬ 50232960 ∣ Nat.factorial 11) (hN ▸ hK.card_dvd (Or.inr rfl))
  obtain ⟨T, W, hcfg, hT⟩ := hfr.sylCfg_syl8 hJ hnc hY
  exact not_sylCfg8_J3 h hcfg hT

theorem cellAbs_FSpor :
    CellAbs FSpor := by
  intro A _ _ zb Sb Vb J hfr hJ hnc hF
  exfalso
  unfold FSpor at hF
  rcases hF with h | h | h | h | h | h | h
  · exact hfr.false_of_M11 hJ h
  · exact not_sylCfgOf_M12 h (hfr.sylCfg hJ hnc).2
  · exact not_sylCfgOf_M22 h (hfr.sylCfg hJ hnc).2
  · exact hfr.false_of_M23 hJ h
  · exact hfr.false_of_J1 hJ h
  · exact not_sylCfgOf_J2 h (hfr.sylCfg hJ hnc).2
  · exact hfr.false_of_J3 hJ hnc h

theorem cellAbs_FMcLy :
    CellAbs FMcLy := by
  intro A _ _ zb Sb Vb J hfr hJ hnc hF
  unfold FMcLy at hF
  rcases hF with h | h
  · exact absurd (hfr.sylCfg hJ hnc).2 (not_sylCfgOf_McL h)
  · exact Or.inr (hfr.isSporadic_ly_of_comp lyAllInner_thm hJ h)

theorem cellAbs_FTwo :
    CellAbs FTwo := by
  intro A _ _ zb Sb Vb J hfr hJ hnc hF
  exfalso
  unfold FTwo at hF
  rcases hF with h | h | h | h | h
  · exact hfr.false_of_L28 hJ h
  · exact hfr.false_of_L216 hJ h
  · exact not_sylCfgOf_L34 h (hfr.sylCfg hJ hnc).2
  · exact hfr.false_of_U34 hJ h
  · exact hfr.false_of_Sz8 hJ h

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
