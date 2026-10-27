module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I167Exc3CoreWSound
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I167Exc3CoreWChkE7

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I167

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Dickson.Sec6.Up34Exc


theorem exc3core_wobs_E7 {L : Type} [Field L] (a : Fin Tag.E7.rank → Lˣ) (ha : ∀ j, a j ^ 3 = 1)
    (i : KernelComponent (rootCharHom a))
    (hn : (componentRoots (rootCharHom a) i).ncard = 40 ∨
      (componentRoots (rootCharHom a) i).ncard = 42 ∨
      (componentRoots (rootCharHom a) i).ncard = 72) :
    exc3core_WObs Tag.E7 (rootCharHom a) (componentRoots (rootCharHom a) i) ∧
      ∀ i' : KernelComponent (rootCharHom a),
        (componentRoots (rootCharHom a) i').ncard = (componentRoots (rootCharHom a) i).ncard →
          i' = i := by
  have hu : exc3core_uniE7 (componentRoots (rootCharHom a) i).ncard = true := by
    rcases hn with h | h | h <;> (rw [h]; decide)
  have hw : exc3core_dngE7 (componentRoots (rootCharHom a) i).ncard = true := by
    rcases hn with h | h | h <;> (rw [h]; decide)
  have hcap : Tag.E7.artifactRoots.length < 127 := by decide +kernel
  refine ⟨?_, ?_⟩
  · exact exc3core_wobs_of_check RD.noG2_E7 127 exc3core_uniE7 exc3core_dngE7 hcap
      exc3core_eCheck_E7 a ha i hu hw
  · exact exc3core_unique_of_ker_lt (rootCharHom a) i
      (exc3core_ker_lt_of_check RD.noG2_E7 127 exc3core_uniE7 exc3core_dngE7 hcap
        exc3core_eCheck_E7 a ha i hu)

theorem exc3core_uniq_E7_D6 {L : Type} [Field L] (a : Fin Tag.E7.rank → Lˣ) (ha : ∀ j, a j ^ 3 = 1)
    (i : KernelComponent (rootCharHom a)) (hn : (componentRoots (rootCharHom a) i).ncard = 60) :
    ∀ i' : KernelComponent (rootCharHom a),
      (componentRoots (rootCharHom a) i').ncard = (componentRoots (rootCharHom a) i).ncard →
        i' = i := by
  have hu : exc3core_uniE7 (componentRoots (rootCharHom a) i).ncard = true := by
    rw [hn]; decide
  have hcap : Tag.E7.artifactRoots.length < 127 := by decide +kernel
  exact exc3core_unique_of_ker_lt (rootCharHom a) i
    (exc3core_ker_lt_of_check RD.noG2_E7 127 exc3core_uniE7 exc3core_dngE7 hcap
      exc3core_eCheck_E7 a ha i hu)

end CFSG.LocalAnalysis.GLTheoremA.I167

end
