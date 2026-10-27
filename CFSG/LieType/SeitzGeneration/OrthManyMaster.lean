module

public import CFSG.LieType.SeitzGeneration.OrthManyParabolic
public import CFSG.LieType.SeitzGeneration.OrthManyBig
public import CFSG.LieType.SeitzGeneration.OrthManyTwo

public section

namespace CFSG.LieType.SeitzGeneration

theorem orthMasterNoSingular : OrthMasterNoSingular := by
  intro K V _ _ _ _ _ Q hQ hT hdim p hp hp5 hpl E hcomm hexp hcard hNS
  obtain ⟨h2, k, hk⟩ := noSingular_ord hQ hp (by omega) hpl E hcomm hexp hcard hNS
  by_cases h4 : 4 ≤ orderOf ((Nat.card K : ℕ) : ZMod p)
  · exact closure_eq_top_of_noSingular_big Q hQ hT hdim hp hp5 hpl E hcomm hexp hcard hNS h4
  · exact closure_eq_top_of_noSingular_two Q hQ hT hdim hp hp5 hpl E hcomm hexp hcard hNS
      (by omega)

theorem orthMaster : OrthMaster :=
  orthMaster_of_parabolic_noSingular orthMasterParabolic orthMasterNoSingular

theorem orthogonalOddPlanes : OrthogonalOddPlanes := orthogonalOddPlanes_of_master orthMaster

theorem orthogonalPlusPlanes : OrthogonalPlusPlanes := orthogonalPlusPlanes_of_master orthMaster

theorem orthogonalMinusPlanes : OrthogonalMinusPlanes := orthogonalMinusPlanes_of_master orthMaster

end CFSG.LieType.SeitzGeneration
