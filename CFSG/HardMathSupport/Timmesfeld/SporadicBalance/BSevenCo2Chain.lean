module

public import Certificates.Certificate17103
public import CFSG.Assembly.Defs

public section

namespace CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BSeven

open CFSG.Blueprint

theorem co2Seven_of_certificate :
    ∀ s : NativeSporadic.Co2, orderOf s = 7 → ∀ M : Subgroup NativeSporadic.Co2,
      M ≤ Subgroup.centralizer ({s} : Set NativeSporadic.Co2) → Odd (Nat.card M) →
        ¬ 7 ∣ Nat.card M → M = ⊥ :=
  Certificates.certificate17103

end CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BSeven
