module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitN36SporA
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitN36SporB
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitN36SporHS
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitN36SporX

public section

namespace CFSG.ComponentClassification.HarrisLit.N36

theorem rowFor_sporadicRep
    (hHe : TBLit.HeldTrivialMultiplier) (hmult : HSJ3TwoMultiplierFact) (h2B : TwoHSTwoBFact)
    (h2C : HS2CNormalFact) (hON : SolMax.ONOuterComponentsInput) :
    RowFor Blueprint.NativeSporadic.SporadicRep := by
  intro G _ _ p m τ K h ⟨s, hs⟩
  cases s with
  | M11 => exact rowFor_spor_M11 G p m τ K h hs
  | M12 => exact rowFor_spor_M12 G p m τ K h hs
  | M22 => exact rowFor_spor_M22 G p m τ K h hs
  | M23 => exact rowFor_spor_M23 G p m τ K h hs
  | M24 => exact rowFor_spor_M24 G p m τ K h hs
  | J1 => exact rowFor_spor_J1 G p m τ K h hs
  | J2 => exact rowFor_spor_J2 G p m τ K h hs
  | J3 => exact rowFor_spor_J3 hmult G p m τ K h hs
  | J4 => exact rowFor_spor_J4 G p m τ K h hs
  | HS => exact rowFor_spor_HS hmult h2B h2C G p m τ K h hs
  | McL => exact rowFor_spor_McL G p m τ K h hs
  | Suz => exact rowFor_spor_Suz G p m τ K h hs
  | Co1 => exact rowFor_spor_Co1 G p m τ K h hs
  | Co2 => exact rowFor_spor_Co2 G p m τ K h hs
  | Co3 => exact rowFor_spor_Co3 G p m τ K h hs
  | He => exact rowFor_spor_He hHe G p m τ K h hs
  | Ly => exact rowFor_spor_Ly G p m τ K h hs
  | ONan => exact rowFor_spor_ONan hON G p m τ K h hs
  | Ru => exact rowFor_spor_Ru G p m τ K h hs
  | Fi22 => exact rowFor_spor_Fi22 G p m τ K h hs
  | Fi23 => exact rowFor_spor_Fi23 G p m τ K h hs
  | Fi24Prime => exact rowFor_spor_Fi24Prime G p m τ K h hs
  | HN => exact rowFor_spor_HN G p m τ K h hs
  | Th => exact rowFor_spor_Th G p m τ K h hs
  | B => exact rowFor_spor_B G p m τ K h hs
  | M => exact rowFor_spor_M G p m τ K h hs

end CFSG.ComponentClassification.HarrisLit.N36
