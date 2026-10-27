module

public import CFSG.LocalAnalysis.GLTheoremA.S12.Compl123

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T123C

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S10
open scoped commutatorElement

@[expose] def ParityFact : Prop :=
  ∀ (p : ℕ) (Ω : Type) [Group Ω] [Finite Ω] (S B K₁ : Subgroup Ω) (x y : Ω),
    p.Prime → p ≠ 2 → S.Normal → CFSG.Open.IsQuasisimple ↥S → IsChevSimple 2 (PSimple p S) →
    GLAPComponent p (S ⊓ cx x) K₁ → Type167J p K₁ →
    IsElemAbelian p B → B ≤ Subgroup.normalizer (S : Set Ω) → x ∈ B → x ≠ 1 → y ∈ B →
    B ⊓ cs S = Subgroup.zpowers y → Nat.card (Subgroup.zpowers y) = p →
    Subgroup.closure ({x, y} : Set Ω) = B ⊓ cs K₁ →
    GLATwoLocalRank p Ω ≤ CFSG.Open.pRank p B →
    ∀ g ∈ Subgroup.centralizer (B : Set Ω), orderOf g = p → g ∈ B

@[expose] def I167Univ : Prop :=
  ∀ (Ω : Type) [Group Ω] [Finite Ω], I167At Ω

@[expose] def BlockFact : Prop :=
  ∀ (p : ℕ) (Ω : Type) [Group Ω] [Finite Ω] (S B K₁ D₁ D : Subgroup Ω) (x y : Ω),
    p.Prime → p ≠ 2 → S.Normal → CFSG.Open.IsQuasisimple ↥S → Type167 p S K₁ →
    GLAPComponent p (S ⊓ cx x) K₁ →
    IsElemAbelian p B → B ≤ Subgroup.normalizer (S : Set Ω) →
    (∀ g ∈ Subgroup.centralizer (B : Set Ω), orderOf g = p → g ∈ B) →
    x ∈ B → x ≠ 1 → y ∈ B → B ⊓ cs S = Subgroup.zpowers y → Nat.card (Subgroup.zpowers y) = p →
    Subgroup.closure ({x, y} : Set Ω) = D₁ → B ⊓ cs K₁ = D₁ →
    IsE2 p B D → x ∈ D → IsE3 p B (D ⊔ D₁) → GLAPLayer p (S ⊓ cs D) ≠ ⊥ →
    ∃ x' ∈ D, x' ∉ Subgroup.zpowers x ∧ ∃ P M : Subgroup Ω,
      GLAPComponent p (S ⊓ cs D) P ∧ GLAPComponent p (S ⊓ cx x') M ∧ P ≤ M ∧ ¬ CentMod p M x

end CFSG.LocalAnalysis.GLTheoremA.T123C

end
