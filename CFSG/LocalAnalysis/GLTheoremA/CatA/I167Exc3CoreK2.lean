module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I167Exc3CoreK2Sound
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I167Exc3CoreK2W
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I167Exc3CoreK2Chk

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I167

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Dickson.Sec6.Up34Exc
  CFSG.HardMathSupport.Timmesfeld.LangTorus


theorem exc3core_inner_E7_D6 {L : Type} [Field L] (a : Fin Tag.E7.rank → Lˣ) (ha : ∀ j, a j ^ 3 = 1)
    (i : KernelComponent (rootCharHom a)) (hn : (componentRoots (rootCharHom a) i).ncard = 60)
    (w : WeylGroup Tag.E7)
    (hw : (fun γ => w • γ) '' componentRoots (rootCharHom a) i = componentRoots (rootCharHom a) i) :
    twistInner (componentRoots (rootCharHom a) i) (fun γ => w • γ) := by
  obtain ⟨β, hβ, hΨ, hβΨ⟩ := exc3core_k2_of_check RD.noG2_E7 127 (by decide +kernel) exc3core_uD6
    exc3core_k2Check_E7' a ha i (by simp [exc3core_uD6, hn])
  exact exc3core_inner_of_orth hβ (fun α hα => hα.1.1) hΨ hβΨ w hw


end CFSG.LocalAnalysis.GLTheoremA.I167

end
