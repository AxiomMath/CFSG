module

public import CFSG.Quasithin.Recognition.HSTypeModels
public import CFSG.LocalAnalysis.ComponentClassification.GHarrisSCertInputs

public section

namespace CFSG.ComponentClassification.GHarris.SCert.SE

open CFSG.Quasithin.HSType

@[expose] def pauliE (p : Pauli2) : SE :=
  gen 1 ^ p.a.val * (⟨0, 0, 0, 2⟩ : SE) ^ p.b.val * (⟨1, 0, 0, 0⟩ : SE) ^ p.c.val *
    (⟨0, 0, 2, 0⟩ : SE) ^ p.d.val * (⟨3, 0, 0, 0⟩ : SE) ^ p.e.val

end CFSG.ComponentClassification.GHarris.SCert.SE
