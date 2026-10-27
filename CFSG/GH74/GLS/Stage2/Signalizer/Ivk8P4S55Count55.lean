module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55BridgeParts
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87L31Stmt
import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55BrData
import CFSG.GH74.GLS.Stage2.Signalizer.Odd87SubSec31Two

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Stage2.Signalizer.Odd87

theorem count55_of (hL : Lemma31Narrow) : Count55 := by
  intro G _ _ z k S T Tstar p H P g X Y h J₁ J₂ J₃ h₁ h₂ h₃ h12 h13 h23
  have hzT : z ∈ T := by
    rw [h.T_eq]
    exact h.ctx.z_mem
  have hzH : z ∈ H := h.T_le hzT
  have hodd : Odd (Nat.card ↥(pPrimeCore 2 ↥H)) :=
    Nat.coprime_two_left.mp pPrimeCore_coprime_card
  exact sec31_two hL h.ctx (SecOfG.of_sec hzH h.H_ne_top hodd) h₁ h₂ h₃ h12 h13 h23

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
