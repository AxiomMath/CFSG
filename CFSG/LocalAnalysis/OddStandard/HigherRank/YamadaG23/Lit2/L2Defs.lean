module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.G2Three.FrameDefs
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.OddStandard.HigherRank.G2Three CFSG.OddStandard.HigherRank.G2Three.Sec1
open scoped commutatorElement

@[expose] def L2Pauli {H Γ : Type} [Group H] [Group Γ] (ρ : H →* Γ) (A : Subgroup Γ) : Prop :=
  ∃ z ∈ center H, orderOf z = 2 ∧
    (∀ x y : H, ρ x ∈ A → ρ y ∈ A → ⁅x, y⁆ = 1 ∨ ⁅x, y⁆ = z) ∧
    (∀ x : H, ρ x ∈ A → ρ x ≠ 1 → ∃ y : H, ρ y ∈ A ∧ ⁅x, y⁆ = z) ∧
    (∀ e ∈ A, ∃ x : H, ρ x = e ∧ (x ^ 2 = 1 ∨ x ^ 2 = z))

@[expose] def L2Z4Type (M : Type) [Group M] : Prop :=
  CFSG.Blueprint.NativeSporadic.IsSporadic M .M22 ∨ CFSG.Blueprint.LieModel M .PSL 3 2 2 ∨
    (∃ n p f : ℕ, 4 ∣ n ∧ 4 ∣ p ^ f - 1 ∧ CFSG.Blueprint.LieModel M .PSL n p f) ∨
    (∃ n p f : ℕ, 4 ∣ n ∧ 4 ∣ p ^ f + 1 ∧ CFSG.Blueprint.LieModel M .PSU n p f) ∨
    (∃ n p f : ℕ, Odd n ∧ 4 ∣ p ^ f - 1 ∧ CFSG.Blueprint.LieModel M .POmegaPlus n p f) ∨
    (∃ n p f : ℕ, Odd n ∧ 4 ∣ p ^ f + 1 ∧ CFSG.Blueprint.LieModel M .POmegaMinus n p f)

@[expose] def L2NoPauliPSL : Prop :=
  ∀ (S : Type) [Group S] [Finite S] (H : Type) [Group H] [Finite H] (ρ : H →* S)
    (A : Subgroup S), Function.Surjective ρ → CFSG.IsQuasisimple H → ρ.ker = center H →
    IsPGroup 2 ↥(center H) → IsE 4 ↥A → L2Pauli ρ A → IsSylowIn 2 (centIn ⊤ A) A →
    ∀ n p f : ℕ, 8 ≤ n → 4 ∣ n → 4 ∣ p ^ f - 1 → CFSG.Blueprint.LieModel S .PSL n p f → False

@[expose] def L2NoPauliPSU : Prop :=
  ∀ (S : Type) [Group S] [Finite S] (H : Type) [Group H] [Finite H] (ρ : H →* S)
    (A : Subgroup S), Function.Surjective ρ → CFSG.IsQuasisimple H → ρ.ker = center H →
    IsPGroup 2 ↥(center H) → IsE 4 ↥A → L2Pauli ρ A → IsSylowIn 2 (centIn ⊤ A) A →
    ∀ n p f : ℕ, 8 ≤ n → 4 ∣ n → 4 ∣ p ^ f + 1 → CFSG.Blueprint.LieModel S .PSU n p f → False

@[expose] def L2NoPauliPOmega : Prop :=
  ∀ (S : Type) [Group S] [Finite S] (H : Type) [Group H] [Finite H] (ρ : H →* S)
    (A : Subgroup S), Function.Surjective ρ → CFSG.IsQuasisimple H → ρ.ker = center H →
    IsPGroup 2 ↥(center H) → IsE 4 ↥A → L2Pauli ρ A → IsSylowIn 2 (centIn ⊤ A) A →
    ∀ n p f : ℕ, 5 ≤ n → Odd n →
      ((4 ∣ p ^ f - 1 ∧ CFSG.Blueprint.LieModel S .POmegaPlus n p f) ∨
        (4 ∣ p ^ f + 1 ∧ CFSG.Blueprint.LieModel S .POmegaMinus n p f)) → False

end CFSG.OddStandard.HigherRank.YamadaG23
