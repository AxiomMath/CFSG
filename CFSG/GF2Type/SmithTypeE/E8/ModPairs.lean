module

public import CFSG.GF2Type.SmithTypeE.E8.ModW0

public section

namespace CFSG.GF2Type.SmithTypeE.E8

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg.Minuscule
  CFSG.HardMathSupport.Cooperstein.Coordinator.Survivors CFSG.SmithE8M CFSG.SeitzReduction

@[expose] def M1n (t : ℤ) : ℕ := if t = 3 then 0 else if t = 1 then 1 else if t = -1 then 10 else 27

theorem m1_counts : ∀ a : Fin e7Data.d,
    (Finset.univ.filter fun k : Fin 126 =>
      e7Data.wt 0 ⬝ᵥ e8mRoot k = 1 ∧ e7Data.wt a ⬝ᵥ e8mRoot k = -1).card = M1n (wgrade a) := by
  decide +kernel

end CFSG.GF2Type.SmithTypeE.E8
