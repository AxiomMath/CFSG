module

public import CFSG.LocalAnalysis.GL83PartI.I713.Sporadic
public import CFSG.LocalAnalysis.GL83PartI.I713.SporadicJ4
public import CFSG.LocalAnalysis.GL83PartI.I713.SporadicON

public section

namespace GL83.I713

open CFSG.Blueprint

theorem outClauseFor_sporadicRep
    {S : Type} [Group S] [Finite S] [IsSimpleGroup S]
    (h : NativeSporadic.SporadicRep S) : OutClauseFor S := by
  obtain ⟨s, ⟨e⟩⟩ := h
  have : Finite (NativeSporadic.Carrier s) := Finite.of_equiv S e.toEquiv
  refine OutClauseFor.of_mulEquiv e ?_
  cases s with
  | M11 => exact outClauseFor_sporadic_M11
  | M12 => exact outClauseFor_sporadic_M12
  | M22 => exact outClauseFor_sporadic_M22
  | M23 => exact outClauseFor_sporadic_M23
  | M24 => exact outClauseFor_sporadic_M24
  | J1 => exact outClauseFor_sporadic_J1
  | J2 => exact outClauseFor_sporadic_J2
  | J3 => exact outClauseFor_sporadic_J3
  | J4 => exact outClauseFor_sporadic_J4
  | HS => exact outClauseFor_sporadic_HS
  | McL => exact outClauseFor_sporadic_McL
  | He => exact outClauseFor_sporadic_He
  | Ru => exact outClauseFor_sporadic_Ru
  | Suz => exact outClauseFor_sporadic_Suz
  | ONan => exact outClauseFor_sporadic_ONan
  | Co1 => exact outClauseFor_sporadic_Co1
  | Co2 => exact outClauseFor_sporadic_Co2
  | Co3 => exact outClauseFor_sporadic_Co3
  | Fi22 => exact outClauseFor_sporadic_Fi22
  | Fi23 => exact outClauseFor_sporadic_Fi23
  | Fi24Prime => exact outClauseFor_sporadic_Fi24Prime
  | HN => exact outClauseFor_sporadic_HN
  | Ly => exact outClauseFor_sporadic_Ly
  | Th => exact outClauseFor_sporadic_Th
  | B => exact outClauseFor_sporadic_B
  | M =>
    have : IsSimpleGroup (NativeSporadic.Carrier .M) := e.symm.isSimpleGroup
    exact outClauseFor_sporadic_M

end GL83.I713
