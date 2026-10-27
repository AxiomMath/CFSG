module

public import Certificates.Certificate17200

public section

namespace CFSG.HardMathSupport.Dickson.Sec6.Gen3D4

open CFSG.Open

namespace Realization

variable {X : Type} [Group X] [Finite X] (R : Realization X)

theorem Eg_facts {c : ℕ} (hc : c < 4) :
    IsElemAbelian 3 (R.Eg c) ∧ Nat.card (R.Eg c) = 27 :=
  (Certificates.certificate17200 R).1 c hc

end Realization

theorem sylow_spec {X : Type} [Group X] [Finite X]
    (R : Realization X) :
    ∃ P : Subgroup X, Nat.card P = 3 ^ 5 ∧ ∀ B : Subgroup X, B ≤ P → IsElemAbelian 3 B →
      ∃ c : ℕ, c < 4 ∧ ∃ g : X, B.map (MulAut.conj g).toMonoidHom ≤ R.Eg c :=
  (Certificates.certificate17200 R).2

end CFSG.HardMathSupport.Dickson.Sec6.Gen3D4
