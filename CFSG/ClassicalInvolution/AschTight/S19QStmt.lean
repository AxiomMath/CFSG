module

public import CFSG.ClassicalInvolution.Asc77.AscIH8Model

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.S19Q

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77

@[expose] def FactFG0 : Prop :=
  ∀ (p e : ℕ) [Fact p.Prime], p ≠ 2 → 5 ≤ p ^ e →
    ∀ (E : Type) [Group E] [Finite E] [IsSimpleGroup E] (Ω : Set (Subgroup E))
      (t : CFSG.Assembly.LowTwoRank.StatedLieTag) (k e' : ℕ),
        ((t = .G2 ∧ k = 0) ∨ (t = .trialityD4 ∧ k = 0)) → Nonempty (Ih8Model p e Ω t k e') →
        ∀ L ∈ Ω, ∀ z : E, IsUniqueInvolution L z →
          (∀ y ∈ Subgroup.centralizer (L : Set E), y * y = 1 → y = 1 ∨ y = z) ∧
          z ∈ ⁅⁅Subgroup.centralizer (L : Set E), Subgroup.centralizer (L : Set E)⁆,
            ⁅Subgroup.centralizer (L : Set E), Subgroup.centralizer (L : Set E)⁆⁆ ∧
          ∀ φ : MulAut E, IsPGroup 2 (Subgroup.zpowers φ) → (∀ x ∈ L, φ x = x) →
            ∃ y ∈ Subgroup.centralizer (L : Set E), φ = MulAut.conj y

@[expose] def FactFG2 : Prop :=
  ∀ (p e : ℕ) [Fact p.Prime], p ≠ 2 → 5 ≤ p ^ e →
    ∀ (E : Type) [Group E] [Finite E] [IsSimpleGroup E] (Ω : Set (Subgroup E))
      (t : CFSG.Assembly.LowTwoRank.StatedLieTag) (k e' : ℕ),
        ((t = .PSL ∧ k = 3) ∨ (t = .PSU ∧ k = 3)) → Nonempty (Ih8Model p e Ω t k e') →
        ∀ L ∈ Ω,
          ⁅⁅fixingSubgroup (MulAut E) (L : Set E), fixingSubgroup (MulAut E) (L : Set E)⁆,
            ⁅fixingSubgroup (MulAut E) (L : Set E), fixingSubgroup (MulAut E) (L : Set E)⁆⁆ = ⊥

end CFSG.ClassicalInvolution.Disconnected.AschTight.S19Q
