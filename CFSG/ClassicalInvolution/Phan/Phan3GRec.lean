module

public import CFSG.ClassicalInvolution.Phan.Phan3GDecomp
public import CFSG.ClassicalInvolution.Phan.Phan3GSimply

public section

namespace CFSG.ClassicalInvolution.Phan.Q3G

open CFSG.ClassicalGroups.Unitary CFSG.ClassicalInvolution.Phan.TitsChamber

variable {K : Type} [Field K] {σ : K ≃+* K}

theorem frameSystem_simplyConnectedOn3_of_card (hσ : IsUnitaryInvolution σ) [Finite K]
    (hK : Nat.card K = 3 ^ 2) (n : ℕ) : SimplyConnectedOn (frameSystem σ n) (J3 n) :=
  frameSystem_simplyConnectedOn3 hσ hK n fun {_} hW hd {_} w => collinear_decomp3 hσ hK hW hd w

end CFSG.ClassicalInvolution.Phan.Q3G
