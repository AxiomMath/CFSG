module

public import CFSG.LocalAnalysis.ComponentClassification.Foote5EndKGSporA
public import CFSG.LocalAnalysis.ComponentClassification.Foote5EndKGSporB
public import CFSG.LocalAnalysis.ComponentClassification.Foote5EndKGSporC
public import CFSG.LocalAnalysis.ComponentClassification.Foote5EndKGSporD

public section

namespace CFSG.ComponentClassification.Foote5

open CFSG Blueprint

theorem endKnownGroupsInputOn_sporadic
    : EndKnownGroupsInputOn fun X _ => NativeSporadic.SporadicRep X := by
  intro X _ _ hX hS
  obtain ⟨s, hs⟩ := hS
  cases s with
  | M11 => exact endKnownGroupsInputOn_M11 X hX hs
  | M12 => exact endKnownGroupsInputOn_M12 X hX hs
  | M22 => exact endKnownGroupsInputOn_M22 X hX hs
  | M23 => exact endKnownGroupsInputOn_M23 X hX hs
  | M24 => exact endKnownGroupsInputOn_M24 X hX hs
  | J1 => exact endKnownGroupsInputOn_J1 X hX hs
  | J2 => exact endKnownGroupsInputOn_J2 X hX hs
  | J3 => exact endKnownGroupsInputOn_J3 X hX hs
  | J4 => exact endKnownGroupsInputOn_J4 X hX hs
  | Co1 => exact endKnownGroupsInputOn_Co1 X hX hs
  | Co2 => exact endKnownGroupsInputOn_Co2 X hX hs
  | Co3 => exact endKnownGroupsInputOn_Co3 X hX hs
  | Fi22 => exact endKnownGroupsInputOn_Fi22 X hX hs
  | Fi23 => exact endKnownGroupsInputOn_Fi23 X hX hs
  | Fi24Prime => exact endKnownGroupsInputOn_Fi24Prime X hX hs
  | HS => exact endKnownGroupsInputOn_HS X hX hs
  | McL => exact endKnownGroupsInputOn_McL X hX hs
  | He => exact endKnownGroupsInputOn_He X hX hs
  | Ru => exact endKnownGroupsInputOn_Ru X hX hs
  | Suz => exact endKnownGroupsInputOn_Suz X hX hs
  | ONan => exact endKnownGroupsInputOn_ONan X hX hs
  | HN => exact endKnownGroupsInputOn_HN X hX hs
  | Ly => exact endKnownGroupsInputOn_Ly X hX hs
  | Th => exact endKnownGroupsInputOn_Th X hX hs
  | B => exact endKnownGroupsInputOn_B X hX hs
  | M => exact endKnownGroupsInputOn_M X hX hs

end CFSG.ComponentClassification.Foote5
