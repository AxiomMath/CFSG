module

public import CFSG.ClassicalInvolution.Models.SymplecticPairs.Intrinsic
public import CFSG.ClassicalInvolution.Q3.ModelOddCentralizerGaussUnitary
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.ClassicalInvolution.Q3.Q3V

open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank
open CFSG.ClassicalInvolution.Models.SymplecticPairs (planeGroup IsHyperbolicPlane stdPlane)

structure IsLocLift (m : ℕ) {G : Type} [Group G] (Ω : Set (Subgroup G)) (L : Subgroup G)
    (Θ : StatedSp m (GaloisField 3 1) →* G) : Prop where
  ker_le : Θ.ker ≤ Subgroup.center (StatedSp m (GaloisField 3 1))
  comm : Commutes Θ.range L
  plane_mem : ∀ P, IsHyperbolicPlane P → (planeGroup P).map Θ ∈ Ω
  members : ∀ M ∈ Ω, M ≠ L → Commutes M L →
    ∃ P, IsHyperbolicPlane P ∧ M = (planeGroup P).map Θ

structure IsMemberFrame {G : Type} [Group G] (Ω : Set (Subgroup G)) {m : ℕ}
    (K : Fin (m + 1) → Subgroup G) : Prop where
  mem : ∀ i, K i ∈ Ω
  comm : ∀ i j, i ≠ j → Commutes (K i) (K j)

structure IsLabLift (m : ℕ) {G : Type} [Group G] (Ω : Set (Subgroup G))
    (K : Fin (m + 1) → Subgroup G) (l : Fin (m + 1))
    (Θ : StatedSp m (GaloisField 3 1) →* G) : Prop where
  loc : IsLocLift m Ω (K l) Θ
  lab : ∀ j : Fin m,
    (planeGroup (stdPlane (GaloisField 3 1) m j)).map Θ = K (l.succAbove j)

@[expose] def layerSub {G : Type} [Group G] (Ω : Set (Subgroup G)) {m : ℕ}
    (K : Fin (m + 1) → Subgroup G) (a b : Fin (m + 1)) : Subgroup G :=
  ⨆ (M : Subgroup G) (_ : M ∈ Ω ∧ ∀ c, c ≠ a → c ≠ b → Commutes M (K c)), M

end CFSG.ClassicalInvolution.Q3.Q3V
