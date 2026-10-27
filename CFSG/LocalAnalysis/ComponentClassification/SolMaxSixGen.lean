
module


public import Certificates.Certificate22257
public import Certificates.Data.SolMaxSixGen
public import CFSG.LocalAnalysis.ComponentClassification.PSL3FourEnumSpec

public section

namespace CFSG.ComponentClassification.SolMax

open CFSG Subgroup Equiv
open CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four

theorem alternatingGroup_le_sup_centralizer_of_six
    {u v : Perm (Fin 9)} (hu2 : u * u = 1) (hv2 : v * v = 1) (huv : u * v = v * u)
    (hu6 : u.support.card = 6) :
    alternatingGroup (Fin 9) ≤ (centralizer {u} ⊓ alternatingGroup (Fin 9)) ⊔
      (centralizer {v} ⊓ alternatingGroup (Fin 9)) ⊔
      (centralizer {u * v} ⊓ alternatingGroup (Fin 9)) :=
  Certificates.certificate22257 hu2 hv2 huv hu6

end CFSG.ComponentClassification.SolMax
