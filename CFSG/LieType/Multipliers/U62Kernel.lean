module

public import Certificates.Certificate10017

public section

namespace CFSG.LieType.Multipliers.U62

open CFSG.CosetTable

theorem kernel_index :
    (genSub {r : FreeGroup (Fin 5) | r ∈ coverWs.map FreeGroup.mk} (subsetOf 5 [0, 1, 2, 3])).FiniteIndex ∧
      (genSub {r : FreeGroup (Fin 5) | r ∈ coverWs.map FreeGroup.mk}
        (subsetOf 5 [0, 1, 2, 3])).index ≤ 8064 :=
  Certificates.certificate10017.1

theorem kernel_hom :
    ∃ (E : Type) (_ : Group E) (ψ : PG 5 coverWs →* E),
      (∀ u ∈ fixWords, ψ (PresentedGroup.mk _ (FreeGroup.mk u)) = 1) ∧
        ∀ u ∈ moveWords, ψ (PresentedGroup.mk _ (FreeGroup.mk u)) ≠ 1 :=
  Certificates.certificate10017.2

end CFSG.LieType.Multipliers.U62
