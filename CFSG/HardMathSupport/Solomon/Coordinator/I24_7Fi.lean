module

public import CFSG.HardMathSupport.Solomon.Coordinator.I24_7Defs
public import CFSG.HardMathSupport.Solomon.Coordinator.I24_7FiCover
public import CFSG.HardMathSupport.Solomon.Coordinator.I24_7FiData
public import CFSG.Monster.B.Fischer.Fi22Faithful
public import CFSG.HardMathSupport.Solomon.Coordinator.I24_7FiMain

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Blueprint CFSG.Monster.B.Fischer CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.LocalBalance.CaseThreeNs

theorem fi22WeakCore3_holds :
    Fi22WeakCore3 := by
  intro Y _ _ hY N _ hNc hF P hP hPc
  have hNP := card_N_inf_P_le_three Y hY N hNc hF P hP
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.Fi22.nonempty_mulEquiv
  obtain ⟨e0⟩ := hF
  let e : (Y ⧸ N) ≃* ↥fi22P := (e0.trans b.symm).trans fi22PermEquiv
  exact weakCore_of_coverData fi22CoverData_holds hY N hNc e P hP hPc hNP

end CFSG.HardMathSupport.Solomon.Coordinator
