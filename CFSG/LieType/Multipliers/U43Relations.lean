module

public import Certificates.Certificate10014

public section

namespace CFSG.LieType.Multipliers.U43

open CFSG.CosetTable

theorem kernel_model :
    ∃ (E : Type) (_ : Group E) (ψ : PG 2 coverWs →* E)
      (τ : Multiplicative (ZMod 12 × ZMod 3) →* E), Function.Injective τ ∧
        ψ (zk 5) = τ (Multiplicative.ofAdd (4, 0)) ∧ ψ (zk 6) = τ (Multiplicative.ofAdd (9, 1)) :=
  Certificates.certificate10014

theorem generate_twelve_three :
    ∀ x : ZMod 12 × ZMod 3, ∃ i < 3, ∃ j < 12, x = i • ((4, 0) : ZMod 12 × ZMod 3) + j • (9, 1) := by
  decide

end CFSG.LieType.Multipliers.U43
