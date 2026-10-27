module

public import CFSG.ClassicalInvolution.Phan.Defs

public section

namespace CFSG.ClassicalInvolution.Q3.Q3W

open CFSG.ClassicalInvolution.Phan (Su)

@[expose] def PhanA3Completion3 : Prop :=
  ∀ {X : Type} [Group X] {U : Fin 3 → Subgroup X} {W : Fin 3 → Fin 3 → Subgroup X},
    Phan.WeakPhanA (GaloisField 3 2) 3 1 3 U W →
    ∃ (E : Type) (_ : Group E) (p : E →* Su (GaloisField 3 2) 3 1 4) (ε : E →* X)
      (V : Fin 3 → Subgroup E), Function.Surjective p ∧
        (∀ e ∈ p.ker, e ∈ Subgroup.center E ∧ ∃ k : ℕ, e ^ 3 ^ k = 1) ∧
        (∀ a : Fin 3, (V a).map p = (Phan.blockEmb2 (GaloisField 3 2) 3 1 3 a).range) ∧
        (∀ a : Fin 3, (V a).map ε = U a)

end CFSG.ClassicalInvolution.Q3.Q3W
