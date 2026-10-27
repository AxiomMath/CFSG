module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Blueprint.Catalog
public import CFSG.ClassicalGroups.UnitaryFlag.GramForm
public import CFSG.LocalAnalysis.ComponentInitial.LinearFlagElation

public noncomputable section

namespace CFSG.LocalAnalysis.ComponentInitial

open CFSG.Blueprint CFSG.Assembly.LowTwoRank LinearFlag CFSG.ClassicalGroups.UnitaryFlag

variable (X : Type) [Group X]

theorem lieModel_twistedB2_iff (a : ℕ) :
    LieModel X .twistedB2 0 2 (2 * a + 1) ↔ 1 ≤ a ∧ ∃ (K : Type) (_ : Field K) (_ : Finite K),
      Nat.card K = 2 ^ (2 * a + 1) ∧ Nonempty (X ≃* suzukiGroup a K) := by
  constructor
  · rintro (⟨ht, -⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩ | ⟨-, -, -, b, hb, K, hK, hfin, hab, hcard, he⟩)
    · exact absurd ht (by decide)
    · exact absurd ht (by decide)
    · exact absurd ht (by decide)
    · obtain rfl : b = a := by omega
      exact ⟨hb, K, hK, hfin, hcard, he⟩
  · rintro ⟨ha, K, hK, hfin, hcard, he⟩
    exact Or.inr (Or.inr (Or.inr ⟨rfl, rfl, rfl, a, ha, K, hK, hfin, rfl, hcard, he⟩))

end CFSG.LocalAnalysis.ComponentInitial
