module

public import CFSG.RankThree.PartTwo.NotationBlocks

public section

namespace CFSG.CGT.Foote82

open CFSG.RankThree.PartTwo CFSG.PGLModel

@[expose] def OmegaMinusSixNormalizer : Prop :=
  ∀ T : GL (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (ZMod 2), T * T = 1 →
    (∀ x ∈ omegaMinusTwo 2, T * x * T⁻¹ ∈ omegaMinusTwo 2) → T ∈ orthogonalMinus 2 (ZMod 2) 1 1

@[expose] def OmegaMinusSixA6Centralizer : Prop :=
  ∀ A : Subgroup (GL (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (ZMod 2)), A ≤ omegaMinusTwo 2 →
    Nonempty (↥A ≃* alternatingGroup (Fin 6)) →
    ∀ t ∈ orthogonalMinus 2 (ZMod 2) 1 1, t ≠ 1 → (∀ a ∈ A, t * a = a * t) →
      Module.finrank (ZMod 2) ↥(LinearMap.range (Matrix.mulVecLin
        ((t : Matrix (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (ZMod 2)) - 1))) = 1

end CFSG.CGT.Foote82
