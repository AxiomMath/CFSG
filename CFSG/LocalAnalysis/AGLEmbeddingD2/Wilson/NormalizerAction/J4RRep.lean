
module


public import Certificates.Certificate12609

public noncomputable section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.AGLEmbeddingD2.Wilson.NormalizerAction

open CFSG.Sporadic.J4 CFSG.Sporadic.J4Schreier CFSG.Sporadic.J4.Native CFSG.Quasithin.J4M2
  CFSG.Quasithin.J4Loc
  CFSG.Sporadic.J4.QT

theorem exists_rRep_of_mem_Qgrp :
    ∀ p ∈ CFSG.Quasithin.J4M2.Qgrp, p ∉ Coordinator.Q8set →
      ∃ i : Fin 7, ∃ w ∈ Coordinator.C0p, ∃ q ∈ Coordinator.Q8set,
        w * p * w⁻¹ = Coordinator.rRep i * q :=
  Certificates.certificate12609

end CFSG.AGLEmbeddingD2.Wilson.NormalizerAction
