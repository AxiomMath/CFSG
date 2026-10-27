module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171SmallTypeIso
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.Basic

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T171S

open CFSG.Open
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)

variable {S₀ S₁ : Type} [Group S₀] [Group S₁]

theorem noSmall_of_mulEquiv (e : S₀ ≃* S₁) (h : HStdExcl.NoSmall S₁) :
    HStdExcl.NoSmall S₀ := by
  intro α hα3 hα1 I hI hsmall
  have hβ3 : MulAut.congr e α ^ 3 = 1 := by rw [← map_pow, hα3, map_one]
  have hβ1 : MulAut.congr e α ≠ 1 := by
    intro h1
    exact hα1 ((MulAut.congr e).injective (h1.trans (map_one (MulAut.congr e)).symm))
  have hI' : CFSG.Open.IsComponentOf (I.map e.toMonoidHom) (fixSubgroup (MulAut.congr e α)) := by
    rw [CFSG.HardMathSupport.Solomon.Coordinator.LieComp.fixSubgroup_congr]
    exact CFSG.SignalizerFunctorTheorem.TransportA.isComponentOf_map e hI
  exact h _ hβ3 hβ1 _ hI' (smallOrd_map e hsmall)

end CFSG.LocalAnalysis.GLTheoremA.T171S

end
