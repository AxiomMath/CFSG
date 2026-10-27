module

public import Certificates.Certificate2332

public section

namespace CFSG.ComponentClassification.HSFLit.GHCert

open CFSG.CosetTable

theorem presentation_bound :
    Finite (PG 9 ghWordsD) ∧ Nat.card (PG 9 ghWordsD) ≤ 512 :=
  Certificates.certificate2332.1

theorem ghG_rels :
    ∀ r ∈ ghWordsD, FreeGroup.lift (fun i : Fin 9 => ghG i.val) (FreeGroup.mk r) = 1 :=
  Certificates.certificate2332.2.1

theorem nfG_inj :
    ∀ k < 512, ∀ k' < 512, nfG k = nfG k' → k = k' :=
  Certificates.certificate2332.2.2

end CFSG.ComponentClassification.HSFLit.GHCert
