module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10FBase

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10GInnLin

open CFSG.Open CFSG.Assembly CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.Y10F

theorem largeEvenProj_equiv_statedProj {a : ℕ} {E : Type} [Field E]
    {H : Subgroup (GL (Fin a) E)} (hH : H = StatedSL a E) :
    Nonempty (LargeEvenProj H ≃* StatedProj (StatedSL a E)) :=
  ⟨by subst hH; exact MulEquiv.refl _⟩

end CFSG.LocalAnalysis.GLTheoremA.Y10GInnLin

end
