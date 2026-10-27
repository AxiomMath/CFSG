module

public import CFSG.LocalAnalysis.GLTheoremB.I2810.Defs
import CFSG.LocalAnalysis.GLTheoremB.I2810.InducedAux
import CFSG.LocalAnalysis.GLTheoremB.I2810.OmegaAux
import CFSG.LocalAnalysis.GLTheoremB.I2810.OmegaSmall
import CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.SmallOmegaFour

public section

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremB.Prop95Iv
open scoped commutatorElement

namespace CFSG.LocalAnalysis.GLTheoremB.Prop95Iv.I2810.OmegaOne

variable {X : Type} [Group X] [Finite X] {W K S : Subgroup X} [W.Normal]

theorem false_of_n_one (h : Setup28 W K S) (hR : Red28 W K S) (h1 : Hyp28One W K S) {a : X}
    {U₁ U₂ : Subgroup X} (hΩ : OmegaAny W K a U₁ U₂ 1) : False := by
  rcases hΩ with hp | hmi
  · obtain ⟨θ, t, hθs, hθW, -⟩ := hp
    haveI := OmegaSmall.solvable_plus_two
    haveI := OmegaSmall.nontrivial_plus_two
    exact not_subsingleton _
      (OmegaSmall.subsingleton_of_perfect_solvable (InducedAux.commutator_K h) θ hθs)
  · obtain ⟨θ, t, hθs, hθW, -⟩ := hmi
    let e := CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.statedOmega_quadMinus_two_mulEquiv_alt5
    refine OmegaAux.false_of_alt_quotient hR h1 (m := 5) le_rfl (e.toMonoidHom.comp θ)
      (e.surjective.comp hθs) fun k hk => ?_
    simp only [MonoidHom.comp_apply, hθW k hk, map_one]

end CFSG.LocalAnalysis.GLTheoremB.Prop95Iv.I2810.OmegaOne
