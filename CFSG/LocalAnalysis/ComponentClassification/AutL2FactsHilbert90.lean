module

import CFSG.Adapters.QiuzhenLegacy.GorensteinWalter.PGammaL2ProjectiveHilbert90
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGammaL2

public noncomputable section

namespace CFSG.ComponentClassification.AutL2Facts

open CFSG GorensteinWalter

universe u

theorem exists_conj_inr_of_involution {K : Type u} [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K)) (x : PGammaL2 K) (hx : orderOf x = 2)
    (hfield : x.right ≠ 1) :
    ∃ C : PGL2 K, (SemidirectProduct.inl C)⁻¹ * x * SemidirectProduct.inl C =
      SemidirectProduct.inr x.right :=
  pGammaL2_involution_conj_inr hK x hx hfield

end CFSG.ComponentClassification.AutL2Facts
