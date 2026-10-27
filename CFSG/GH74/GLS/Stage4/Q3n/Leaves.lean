module

public import CFSG.CharacterTheory.BrauerThirdMainTheorem.DefectDefinitions
public import CFSG.Adapters.ProjectiveSpecialLinear

public section

namespace CFSG.GH74.GLS.Stage4.Q3n

open CFSG CFSG.BrauerThirdMainTheorem.Helpers Subgroup

@[expose] def LG33_1 : Prop :=
  ∀ (p : ℕ), p.Prime → ∀ (m : Ideal BlocksAlgInt), m.IsMaximal → (p : BlocksAlgInt) ∈ m →
    ∀ (G : Type) [Group G] [Finite G] (D : Subgroup G) (χ : G → ℂ), χ ∈ BlocksIrr G →
      blockDefect p m χ D →
        ∃ d : ℕ, χ 1 = d ∧
          p ^ ((Nat.card G).factorization p - (Nat.card D).factorization p) ∣ d

@[expose] def KleinFourConclusion (m : Ideal BlocksAlgInt) (G : Type) [Group G] [Finite G]
    (U : Subgroup G) (ω : ↥(Subgroup.centralizer (U : Set G)) → ℂ) (z : G) : Prop :=
  ∃ (B : Set (G → ℂ)) (b : Fin 3 → Set (↥(Subgroup.centralizer ({z} : Set G)) → ℂ))
    (f : ℕ) (fb : Fin 3 → ℕ),
    BlocksIsBlock m G B ∧ (∀ χ ∈ B, blockDefect 2 m χ U) ∧ (∀ χ ∈ B, χ 1 = (f : ℂ)) ∧
    (∀ i, BlocksIsBlock m ↥(Subgroup.centralizer ({z} : Set G)) (b i) ∧
      (∀ ψ ∈ b i, blockDefect 2 m ψ (U.subgroupOf (Subgroup.centralizer ({z} : Set G)))) ∧
      ∀ ψ ∈ b i, ψ 1 = (fb i : ℂ)) ∧
    (Nat.card G : ℂ) * (Nat.card ↥(Subgroup.centralizer (U : Set G)) : ℂ) ^ 2 *
        ((fb 0 : ℂ) * fb 1 * fb 2) =
      (Nat.card ↥(Subgroup.centralizer ({z} : Set G)) : ℂ) ^ 3 * ω 1 ^ 2 * f

end CFSG.GH74.GLS.Stage4.Q3n
