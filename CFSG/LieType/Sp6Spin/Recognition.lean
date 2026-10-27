module

public import CFSG.LieType.Sp6Spin.CaseAB
public import CFSG.LieType.Sp6Spin.Frame
public import CFSG.LieType.Sp6Spin.FrameModel
public import CFSG.LieType.Sp6Spin.RecognitionAux
public import CFSG.HardMathSupport.Kantor79.LongRoot

public section

namespace CFSG.LieType.Sp6Spin

open CFSG.LieType.TorusWeights CFSG.LieType.Universal.Symplectic CFSG.Assembly.LowTwoRank
  TauCeti.GLSymplecticFin QuadraticMap CFSG.StandardType CFSG.StandardType.Triality
  CFSG.LieType.D4Small CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  CFSG.HardMathSupport
open scoped Matrix

theorem spinRecognition :
    ∀ (K : Type) [Field K] [Finite K] [CharP K 2], 4 ≤ Nat.card K →
      ∀ (V : Type) [AddCommGroup V] [Module K V], Module.finrank K V = 8 →
      ∀ (Q : QuadraticForm K V), (QuadraticMap.polarBilin Q).Nondegenerate →
      ∀ (ψ : StatedSp 3 K →* (V ≃ₗ[K] V)), (∀ g v, Q (ψ g v) = Q v) →
      (∀ W : Submodule K V, (∀ g, ∀ w ∈ W, ψ g w ∈ W) → W = ⊥ ∨ W = ⊤) →
      (∀ r : RootSubgroupIndex 3, IsShortIndex r → ∀ c : K, c ≠ 0 →
        Kantor79.IsLongRootElement Q (ψ (SpExtras.elt r c))) →
      ∃ e : V ≃ₗ[K] (Fin (2 * 4) → K), (∀ v, coordinateQuadPlus 4 K (e v) = Q v) ∧
        (∀ g, ∃ M ∈ spinSeven K, ∀ v,
          ((M : GL (Fin (2 * 4)) K) : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) *ᵥ e v = e (ψ g v)) ∧
        ∀ M ∈ spinSeven K, ∃ g, ∀ v,
          ((M : GL (Fin (2 * 4)) K) : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) *ᵥ e v =
            e (ψ g v) := by
  intro K _ _ _ hK V _ _ hV Q hQ ψ hψQ hirred _
  exact SpinSetting.exists_spinEquiv (S :=
    { card_le := hK, finrank_eq := hV, Q := Q, nondeg := hQ, ψ := ψ, map_Q := hψQ,
      irred := hirred })

end CFSG.LieType.Sp6Spin
