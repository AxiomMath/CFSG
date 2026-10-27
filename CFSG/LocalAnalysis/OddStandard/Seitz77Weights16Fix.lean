module

public import CFSG.LocalAnalysis.OddStandard.Seitz77Weights16Field

public section

namespace CFSG.OddStandard.Seitz77

namespace Weights16

open CFSG.GH74.KGroups

theorem exists_eq_add_semilinear_gf16 (μ : GF16) (hμ : μ * μ ^ 4 = 1) (x : GF16)
    (hx : μ * x ^ 4 = x) : ∃ y, x = y + μ * y ^ 4 := by
  revert μ x
  decide +kernel

section Field

variable {F : Type*} [Field F]

theorem exists_eq_add_semilinear (hF : Nat.card F = 16) {μ : F} (hμ : μ * μ ^ 4 = 1) {x : F}
    (hx : μ * x ^ 4 = x) : ∃ y, x = y + μ * y ^ 4 := by
  obtain ⟨φ⟩ := exists_ringEquiv hF
  obtain ⟨μ', rfl⟩ := φ.surjective μ
  obtain ⟨x', rfl⟩ := φ.surjective x
  have hμ' : μ' * μ' ^ 4 = 1 := φ.injective (by simpa using hμ)
  have hx' : μ' * x' ^ 4 = x' := φ.injective (by simpa using hx)
  obtain ⟨y, hy⟩ := exists_eq_add_semilinear_gf16 μ' hμ' x' hx'
  exact ⟨φ y, by rw [← map_pow, ← map_mul, ← map_add, ← hy]⟩

end Field

end Weights16

end CFSG.OddStandard.Seitz77
