module

public import CFSG.HardMathSupport.Timmesfeld.Steinberg.ThreeCentralizer
import CFSG.LieType.AlgebraicGroups.ConvolutionPoints

public noncomputable section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQ3

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley WithConv Topology
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Timmesfeld.Steinberg

open scoped CFSG.ConvolutionPoints

set_option linter.unusedSectionVars false

variable {τ : Tag} {k : Type} [Field k]

theorem toralRootGroup_lang (p : ℕ) [Fact p.Prime] [CharP k p] [IsAlgClosed k]
    (a : Fin τ.rank → kˣ) (e : ℕ) (he : 1 ≤ e)
    (hstab : ∀ g ∈ toralRootGroup τ k a, entrywiseFrobGL τ k p e g ∈ toralRootGroup τ k a) :
    ∀ c ∈ toralRootGroup τ k a, ∃ z ∈ toralRootGroup τ k a,
      z⁻¹ * entrywiseFrobGL τ k p e z = c := by
  obtain ⟨nI, κ, m, α, v, j, ω, hκ, hα, hαr, hvj, hω⟩ := exists_toralCoverData (rootCharHom a)
  obtain ⟨-, -, -, -, -, -, -, -, -, hirr, hcons⟩ :=
    toral_root_subgroup_regular_cover_gen τ k a κ hκ α hα hαr v j hvj ω hω
  obtain ⟨-, hM, -⟩ := isConnectedAlgebraicSubgroup_map (modGLPoint τ k)
    (toralRootGroup τ k a) hcons hirr
  have hQ : ∀ g ∈ toralRootGroup τ k a, frobTwistGL τ k p e 1 g ∈ toralRootGroup τ k a :=
    fun g hg => by
      rw [frobTwistGL_apply, one_mul, inv_one, mul_one]
      exact hstab g hg
  obtain ⟨-, -, -, hlang⟩ := exists_frobTwist_restriction p hM he 1 hQ
  intro c hc
  obtain ⟨z, hz, hzc⟩ := hlang c hc
  refine ⟨z, hz, ?_⟩
  rw [frobTwistGL_apply, one_mul, inv_one, mul_one] at hzc
  exact hzc

end CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQ3

end
