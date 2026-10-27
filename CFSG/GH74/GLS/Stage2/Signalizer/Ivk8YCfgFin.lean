module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8YCfgThm
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8Gen2

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Subgroup CFSG

theorem AFrame.sylCfg {A : Type} [Group A] [Finite A] {zb : A} {Sb Vb J : Subgroup A}
    (hfr : AFrame A zb Sb Vb) (hJ : IsComponent J) (hnc : ¬ Vb ≤ centralizer (J : Set A)) :
    IsSimpleGroup (↥J ⧸ center ↥J) ∧ SylCfgOf (↥J ⧸ center ↥J) :=
  hfr.sylCfg_of_comps (fun _ _ _ h₁ h₂ h₃ => hfr.comps_le_two h₁ h₂ h₃) hJ hnc

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
