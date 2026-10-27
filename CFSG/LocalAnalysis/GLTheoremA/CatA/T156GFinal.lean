module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T156GTwE6Main
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T156GExcE6Three
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T156GExcTD4Three

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T156

open CFSG.Assembly CFSG.StandardType

section Core


theorem t156Rest₆_holds : T156Rest₆ := by
  intro p hp hp2 lab hlab hr
  obtain ⟨t, l, n⟩ := lab
  unfold RestLabel₆ at hr
  dsimp only at hr
  rcases hr with ⟨rfl, rfl, heven⟩ | ⟨rfl, rfl⟩
  · have hl : l = 0 := hlab.2
    subst hl
    exact cAll_geomBody_e6_three hlab.1 heven
  · have hl : l = 0 := hlab.2
    subst hl
    exact cAll_geomBody_td4_three hlab.1

theorem t156FactOmega_holds (p : ℕ) : T156FactOmega p :=
  t156FactOmega_of_rest₆ t156Rest₆_holds p

end Core

end CFSG.LocalAnalysis.GLTheoremA.T156

end
