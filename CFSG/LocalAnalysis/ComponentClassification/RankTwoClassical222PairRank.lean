module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofSplit

public section

namespace CFSG.ComponentClassification.RankTwoClassical

open Subgroup CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.RankTwoStandard

section Rank

variable {G : Type} [Group G] {A : Subgroup G} {ι K : Type} [Fintype ι] [DecidableEq ι]
  [Field K] {H : Subgroup (GL ι K)} {e : rankTwoQuot A ≃* StatedProj H}

theorem Represents.fix_of_commRank_ne {p u g : G} {M U X : GL ι K} (hpM : Represents e p M)
    (huU : Represents e u U) (hgX : Represents e g X) (hu2 : u * u = 1)
    (hrk : ∀ c : Kˣ, commRank (M * X * Matrix.GeneralLinearGroup.scalar ι c) ≠ commRank X)
    (horb : g * u * g⁻¹ = u ∨ g * u * g⁻¹ = u * p) : g * u * g⁻¹ = u := by
  rcases horb with h | h
  · exact h
  exfalso
  have hui : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu2
  have hgu : g * u = u * p * g := by rw [← h]; group
  have h1 : u * g * u⁻¹ = p * g := by
    rw [hui, mul_assoc, hgu, ← mul_assoc, ← mul_assoc, hu2, one_mul]
  have hr1 : Represents e (u * g * u⁻¹) (U * X * U⁻¹) := (huU.mul hgX).mul huU.inv
  rw [h1] at hr1
  obtain ⟨c, hc⟩ := (hpM.mul hgX).exists_scalar hr1
  apply hrk c
  rw [← hc, commRank_conj]

end Rank

end CFSG.ComponentClassification.RankTwoClassical
