module

public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.Sec4S7O
public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.Sec4S7P
public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.Sec7Main
public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.Sec4S7N

public section

set_option linter.unusedSectionVars false

namespace CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo

open Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {d : Data G} {K₀ : Subgroup G}

section Final



variable (h : d.Hyp) (hKU : d.KUnitary) (hf : d.IsUnitaryFactor K₀)

include h hKU in
theorem Data.Hyp.hBu : ∀ x ∈ Data.B₁ h hKU hf, d.u * x * d.u⁻¹ ∈ Data.B₁ h hKU hf :=
  h.hBu_of_eq hKU hf (h.B₁_eq_commutator_g hKU hf)

include h hKU hf in
theorem Data.Hyp.commutation :
    ⁅d.nclL K₀, (d.nclL K₀).map (MulAut.conj d.t).toMonoidHom⁆ = ⊥ :=
  h.commutation_of_hBu hKU hf (h.hBu hKU hf)

end Final

section Top



theorem unitaryCommutation_holds : UnitaryCommutation := by
  intro G _ _ d h hKU K₀ hf
  exact h.commutation hKU hf

theorem u52UnitaryCaseExclusion_holds :
    CFSG.Yardstones.M41b0c98b3153.U52UnitaryCaseExclusion :=
  u52UnitaryCaseExclusion_of_commutation unitaryCommutation_holds

end Top

end CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo
