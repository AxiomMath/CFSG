module

public import CFSG.LocalAnalysis.AGLEmbedding.SporadicBeta
public import CFSG.LocalAnalysis.AGLEmbedding.SporadicBetaSmall2
public import CFSG.LocalAnalysis.AGLEmbedding.SporadicBetaSmall3
public import CFSG.LocalAnalysis.AGLEmbedding.SporadicBetaSmall

public section

namespace CFSG.AGLEmbedding

@[expose] def SporadicBetaRemaining : Prop :=
  ∀ s : TauCeti.SporadicName, s ∈ ({.J3, .McL, .Suz, .ONan, .Co1, .Co2, .Co3, .Fi22, .Fi23,
    .Fi24Prime, .HN, .Ly, .Th, .B} : Finset TauCeti.SporadicName) →
      SporadicBetaData (Blueprint.NativeSporadic.Carrier s)


theorem kFactBetaSpor_of_remaining
    (hbr : ∀ s : TauCeti.SporadicName,
      Nonempty (Blueprint.NativeSporadic.Carrier s ≃* (TauCeti.CFSGIndex.sporadic s).Group))
    (hrem : SporadicBetaRemaining) (hM : MonsterBetaData) : KFactBetaSpor := by
  refine kFactBetaSpor_of_data hbr (fun s hs => ?_) hM
  cases s with
  | M11 => exact sporadicBetaData_M11
  | M12 => exact sporadicBetaData_M12
  | M22 => exact sporadicBetaData_M22
  | M23 => exact sporadicBetaData_M23
  | M24 => exact sporadicBetaData_M24
  | J1 => exact sporadicBetaData_J1
  | J2 => exact sporadicBetaData_J2
  | J4 => exact sporadicBetaData_J4
  | HS => exact sporadicBetaData_HS
  | He => exact sporadicBetaData_He
  | Ru => exact sporadicBetaData_Ru
  | M => exact (hs rfl).elim
  | _ => exact hrem _ (by decide)

end CFSG.AGLEmbedding
