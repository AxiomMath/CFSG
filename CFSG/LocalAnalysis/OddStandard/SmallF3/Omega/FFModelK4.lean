module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFModelK4Split
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFModelK4III
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFModelK4IV

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

theorem ff_K4_layerModel (hQ : Q.Nondegenerate) (hdim : Module.finrank (ZMod 3) V = 6)
    (hsgn : quadSign Q = 1) {x : ProjSim Q} (hx2 : x * x = 1) (hx : KM4 x) :
    LayerModel ↥(ffFix hQ (by omega) x) .PSL 3 1 ∨
      LayerModel ↥(ffFix hQ (by omega) x) .PSL 2 2 := by
  obtain ⟨ρ, hρx, hρ, h1 | h2⟩ := ff_K4_split hQ hdim hsgn hx2 hx
  · subst hρx
    exact Or.inl (ff_K4III_layerModel hQ hdim hsgn hρ h1)
  · subst hρx
    exact Or.inr (ff_K4IV_layerModel hQ hdim hsgn hρ h2)

theorem ff_K4_cover (hQ : Q.Nondegenerate) (hdim : Module.finrank (ZMod 3) V = 6)
    (hsgn : quadSign Q = 1) {x : ProjSim Q} (hx2 : x * x = 1) (hx : KM4 x) :
    ∃ w : ↥(omegaProj hQ), w ∈ twoPrimeRes (twoRes (ffFix hQ (by omega) x)) ∧ w * w = 1 ∧
      KM0 (projOrthToProjSim Q (w : ProjOrth Q)) ∧
      ∃ a : ↥(omegaProj hQ), ffSimOmegaAct hQ (by omega) x a * a⁻¹ = w := by
  obtain ⟨ρ, hρx, hρ, h1 | h2⟩ := ff_K4_split hQ hdim hsgn hx2 hx
  · subst hρx
    exact ff_K4III_cover hQ hdim hsgn hρ h1
  · subst hρx
    exact ff_K4IV_cover hQ hdim hsgn hρ h2

end CFSG.OddStandard.SmallF3.Omega
