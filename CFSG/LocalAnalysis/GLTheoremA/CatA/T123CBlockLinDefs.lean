module

public import CFSG.Foundations.Basic

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T123CB

@[expose] def SLInnerBlockAt (p n : ℕ) (K : Type) [Field K] : Prop :=
  ∀ E0 : Subgroup (Matrix.SpecialLinearGroup (Fin n) K), CFSG.IsElementaryAbelian p E0 →
    Nat.card E0 = p ^ 2 → ∀ a ∈ E0, a ≠ 1 →
    ¬ Group.IsSolvable ↥(Subgroup.centralizer (E0 : Set (Matrix.SpecialLinearGroup (Fin n) K))) →
    ∃ a' ∈ E0, a' ∉ Subgroup.zpowers a ∧ ∃ P M : Subgroup (Matrix.SpecialLinearGroup (Fin n) K),
      P ≤ Subgroup.centralizer (E0 : Set (Matrix.SpecialLinearGroup (Fin n) K)) ∧
      (∀ g ∈ Subgroup.centralizer (E0 : Set (Matrix.SpecialLinearGroup (Fin n) K)),
        ∀ x ∈ P, g * x * g⁻¹ ∈ P) ∧ CFSG.IsQuasisimple ↥P ∧
      M ≤ Subgroup.centralizer ({a'} : Set (Matrix.SpecialLinearGroup (Fin n) K)) ∧
      (∀ g ∈ Subgroup.centralizer ({a'} : Set (Matrix.SpecialLinearGroup (Fin n) K)),
        ∀ x ∈ M, g * x * g⁻¹ ∈ M) ∧ CFSG.IsQuasisimple ↥M ∧ P ≤ M ∧
      p ∣ Nat.card (↥P ⧸ Subgroup.center ↥P) ∧
      a ∉ Subgroup.centralizer (M : Set (Matrix.SpecialLinearGroup (Fin n) K))

end CFSG.LocalAnalysis.GLTheoremA.T123CB

end
