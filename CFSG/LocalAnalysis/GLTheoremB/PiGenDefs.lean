module

public import CFSG.Assembly.Defs
public import CFSG.LocalAnalysis.GLTheoremB.UniqDefs

public section

namespace CFSG.LocalAnalysis.GLTheoremB

open CFSG.Open

@[expose] def IsAltType (p : ℕ) (K : Type*) [Group K] : Prop :=
  (∃ k : ℕ, Nonempty ((K ⧸ Subgroup.center K) ≃* alternatingGroup (Fin (k * p + 2)))) ∨
    (p = 3 ∧ Nonempty ((K ⧸ Subgroup.center K) ≃* alternatingGroup (Fin 7)))

@[expose] def IsOrthType (p : ℕ) (K : Type*) [Group K] : Prop :=
  ∃ (n : ℕ) (ε : Bool), 1 ≤ n ∧ IsOmegaTwo ε (n + 1) (K ⧸ Subgroup.center K) ∧
    HasFixedPointFreeOrder ε n p

@[expose] def InputPiGenOrth : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (p : ℕ), p.Prime → p ≠ 2 →
    ∀ K : Subgroup X, IsComponentOf K ⊤ → IsPiGroup p ↥K → IsOrthType p ↥K →
      ¬ IsAltType p ↥K →
      ∀ B : Subgroup X, IsElemAbelian p B → GLATwoLocalRank p X ≤ pRank p B →
        K ≤ GLBCore p (pRank p B - 1) B

end CFSG.LocalAnalysis.GLTheoremB
