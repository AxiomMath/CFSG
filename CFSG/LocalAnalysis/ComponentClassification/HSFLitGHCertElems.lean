module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitGHCertCheckInputs
public import CFSG.Sporadic.HS.Chain

public section

namespace CFSG.ComponentClassification.HSFLit.GHCert

open CFSG.Sporadic.SmallF2 CFSG.Sporadic.Th
open CFSG.Sporadic.HS.Native (hsData)

@[expose] noncomputable def ghG (i : ℕ) : J hsData := wordG (genG hsData) (abWords.getD i [])

@[expose] noncomputable def gensG9 (c : ℤ) : J hsData :=
  if 0 < c then ghG (c - 1).toNat else (ghG (-c - 1).toNat)⁻¹

@[expose] noncomputable def nfG (k : ℕ) : J hsData := wordG gensG9 (nfCodes k)

end CFSG.ComponentClassification.HSFLit.GHCert

end
