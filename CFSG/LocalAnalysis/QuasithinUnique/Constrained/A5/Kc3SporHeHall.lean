module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3SporPermCode
public import Certificates.Certificate4049

public section

namespace CFSG.QuasithinUnique.A5.Kc3SporHeChk

open CFSG.QuasithinUnique.K1.SporadicPerm CFSG.QuasithinUnique.A5.Kc3SporPerm
  CFSG.QuasithinUnique.A5.Kc3SporLine

theorem he_hall
    : ∀ E : Subgroup CFSG.Sporadic.He.J,
    E ≤ CFSG.QuasithinUnique.A5.Kc3SporHe.heR → (∀ x ∈ E, ∀ y ∈ E, x * y = y * x) →
      (∀ x ∈ E, x * x = 1) → Nat.card E = 16 → ¬ PairFibersAllowed (Fin 8330) E :=
  Certificates.certificate4049 CFSG.QuasithinUnique.A5.Kc3SporHe.he_ta
    CFSG.QuasithinUnique.A5.Kc3SporHe.he_tb he_base_property

end CFSG.QuasithinUnique.A5.Kc3SporHeChk
