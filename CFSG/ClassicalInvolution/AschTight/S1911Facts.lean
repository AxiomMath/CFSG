module

public import CFSG.ClassicalInvolution.Asc77.AscL62Aut

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.S1911

open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.AscL62
open scoped MatrixGroups

@[expose] def FactF0 : Prop :=
  ∀ (p e : ℕ) [Fact p.Prime], p ≠ 2 → 0 < e →
    ∀ σ : GaloisField p (2 * e) ≃+* GaloisField p (2 * e), σ ≠ 1 → σ * σ = 1 →
      ∀ G : GL (Fin 2) (GaloisField p (2 * e)),
        (∀ b, semilinHom G σ (semilinHom G σ b) = b) →
          Nonempty (↥(MonoidHom.eqLocus (semilinHom G σ)
            (MonoidHom.id SL(2, GaloisField p (2 * e)))) ≃* SL(2, GaloisField p e))

end CFSG.ClassicalInvolution.Disconnected.AschTight.S1911
