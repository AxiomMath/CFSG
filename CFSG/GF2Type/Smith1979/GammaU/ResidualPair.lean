
module

public import CFSG.GF2Type.Smith1979.GammaU.ResidualPairBase
import all CFSG.GF2Type.Smith1979.GammaU.ResidualPairBase

public import Certificates.Certificate16980

public section

namespace CFSG.GF2Type.Smith1979.GammaU.ResPair

open CFSG.GF2Type.Smith1979.GammaU CFSG.GF2Type.Smith1979.GammaU.StepA
open CFSG.GF2Type.Smith1979.GammaU.Viol

theorem residualPair {i : ℕ} (hi : i = 0 ∨ i = 1)
    {c : Array ℕ} (hc : c ∈ resConj i) (hc1 : c ≠ idR) :
    ∃ (h1 : mulR c (invR c) = idR) (h2 : mulR (invR c) c = idR),
      Violation (n2 i ⊔ (n2 i).map (MulAut.conj (eqvOf c (invR c) h1 h2)).toMonoidHom)
        (compOf i) (idR :: hyp10 i) :=
  Certificates.certificate16980 i hi c hc hc1

end CFSG.GF2Type.Smith1979.GammaU.ResPair
