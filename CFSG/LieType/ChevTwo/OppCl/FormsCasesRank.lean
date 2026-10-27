module

public import CFSG.LieType.ChevTwo.OppCl.Defs

public section

namespace CFSG.LieType.ChevTwo.OppCl

open CFSG.Open CFSG.LieType.BorelTits

namespace FormsCases

section RankDecomp

variable {F : Type} [Field F] {V : Type} [AddCommGroup V] [Module F V]

theorem exists_rank_decomp [FiniteDimensional F V] (g : V →ₗ[F] V) :
    ∃ (ι : Type) (_ : Fintype ι) (x : ι → V) (φ : ι → (V →ₗ[F] F)),
      (∀ j, x j ∈ LinearMap.range g) ∧ (∀ j v, g v = 0 → φ j v = 0) ∧
        g = ∑ j, (φ j).smulRight (x j) := by
  let b := Module.finBasis F (↥(LinearMap.range g))
  refine ⟨Fin (Module.finrank F (↥(LinearMap.range g))), inferInstance, fun j => (b j : V),
    fun j => b.coord j ∘ₗ g.rangeRestrict, ?_, ?_, ?_⟩
  · intro j
    exact (b j).2
  · intro j v hv
    have h0 : g.rangeRestrict v = 0 := Subtype.ext hv
    simp [h0]
  · apply LinearMap.ext
    intro v
    have hsum : ∑ j, b.repr (g.rangeRestrict v) j • (b j : V) = g v := by
      have h := congrArg Subtype.val (b.sum_repr (g.rangeRestrict v))
      rw [Submodule.coe_sum] at h
      simp only [Submodule.coe_smul] at h
      exact h
    simp only [LinearMap.sum_apply, LinearMap.smulRight_apply, LinearMap.comp_apply,
      Module.Basis.coord_apply]
    exact hsum.symm

end RankDecomp

end FormsCases

end CFSG.LieType.ChevTwo.OppCl
