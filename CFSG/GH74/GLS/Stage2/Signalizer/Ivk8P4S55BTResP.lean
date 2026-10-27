module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55BTRes
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55BTResD

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT

theorem diagSolv_proved : DiagSolv := by
  intro G _ _ z k S T Tstar p H P g X Y h t q I Q₁ hd w hw W hWw hWI
  exact diag_solvable h hd hw hWw hWI

theorem diagSwap_proved : DiagSwap := by
  intro G _ _ z k S T Tstar p H P g X Y h t q I Q₁ hd w hw y hyH hy2 hyz hyw hne hyI
  exact diag_swap h hd hw hyH hy2 hyz hyw hne hyI

theorem resB_proved : ResB :=
  resB_of_diag diagSolv_proved diagSwap_proved

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT
