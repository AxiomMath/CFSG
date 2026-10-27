module

public import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.E6BadTorus

public section

namespace CFSG.HardMathSupport.Dickson.Sec6.I1431

open CFSG CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Steinberg.TwistedE6
  CFSG.LieType.Steinberg.CentralExt.MinusculeClosed

@[expose] def twB1 : Fin Tag.E6.rank → ℤ := Pi.single (nd 3) 1

@[expose] def twB2 : Fin Tag.E6.rank → ℤ :=
  Pi.single (nd 2) 1 + Pi.single (nd 3) 1 + Pi.single (nd 4) 1

@[expose] def twB3 : Fin Tag.E6.rank → ℤ :=
  Pi.single (nd 0) 1 + Pi.single (nd 2) 1 + Pi.single (nd 3) 1 + Pi.single (nd 4) 1 +
    Pi.single (nd 5) 1

@[expose] def twTheta : Fin Tag.E6.rank → ℤ := ![1, 2, 2, 3, 2, 1]

@[expose] def vE0a : Fin Tag.E6.rank → ZMod 3 := ![1, 0, 0, 0, 0, 2]

@[expose] def vE0b : Fin Tag.E6.rank → ZMod 3 := ![0, 0, 1, 0, 2, 0]

@[expose] def vT1 : Fin Tag.E6.rank → ZMod 3 := ![0, 0, 0, 1, 0, 0]

@[expose] def vT2 : Fin Tag.E6.rank → ZMod 3 := ![0, 0, 1, 1, 1, 0]

@[expose] def vT3 : Fin Tag.E6.rank → ZMod 3 := ![1, 0, 1, 1, 1, 1]

section Group

variable (K : Type) [Field K]

@[expose] noncomputable def rootPair (γ : Fin Tag.E6.rank → ℤ) : Subgroup (e6Data_valid.minGroup K) :=
  e6Data_valid.rootGroup K γ ⊔ e6Data_valid.rootGroup K (-γ)

@[expose] noncomputable def rankOneThree (b : Fin Tag.E6.rank) : e6Data_valid.minGroup K :=
  e6Data_valid.xm K (Pi.single b 1) 1 * e6Data_valid.xm K (-Pi.single b 1) (-3)

@[expose] noncomputable def torusZ (ζ : Kˣ) (hζ : orderOf ζ = 3) (x : Fin Tag.E6.rank → ZMod 3) :
    e6Data_valid.minGroup K :=
  minTorus e6Data_valid K (zeta3Pi ζ hζ (Multiplicative.ofAdd x))

end Group

end CFSG.HardMathSupport.Dickson.Sec6.I1431
