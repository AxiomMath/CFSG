module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I167Exc3CoreWSound
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I167Exc3CoreWChkE6

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I167

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Dickson.Sec6.Up34Exc


theorem exc3core_wobs_E6 {L : Type} [Field L] (a : Fin Tag.E6.rank → Lˣ) (ha : ∀ j, a j ^ 3 = 1)
    (i : KernelComponent (rootCharHom a))
    (hn : (componentRoots (rootCharHom a) i).ncard = 20 ∨
      (componentRoots (rootCharHom a) i).ncard = 40) :
    exc3core_WObs Tag.E6 (rootCharHom a) (componentRoots (rootCharHom a) i) ∧
      ∀ i' : KernelComponent (rootCharHom a),
        (componentRoots (rootCharHom a) i').ncard = (componentRoots (rootCharHom a) i).ncard →
          i' = i := by
  have hu : exc3core_dngE6 (componentRoots (rootCharHom a) i).ncard = true := by
    rcases hn with h | h <;> simp [exc3core_dngE6, h]
  have hcap : Tag.E6.artifactRoots.length < 73 := by decide +kernel
  exact ⟨exc3core_wobs_of_check RD.noG2_E6 73 exc3core_dngE6 exc3core_dngE6 hcap
      exc3core_eCheck_E6 a ha i hu hu,
    exc3core_unique_of_ker_lt (rootCharHom a) i
      (exc3core_ker_lt_of_check RD.noG2_E6 73 exc3core_dngE6 exc3core_dngE6 hcap
        exc3core_eCheck_E6 a ha i hu)⟩

end CFSG.LocalAnalysis.GLTheoremA.I167

end
