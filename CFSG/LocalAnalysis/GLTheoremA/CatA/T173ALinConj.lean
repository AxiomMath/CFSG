module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173ALinDefs

import CFSG.LocalAnalysis.StandardType.GGTableBLinear

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T173A

open CFSG.Open CFSG.Assembly CFSG.LocalAnalysis.GLTheoremA
open scoped MatrixGroups

theorem lin_conj_psl {d : ℕ} {F : Type} [Field F] (g : GL (Fin d) F) :
    ∃ φ : MulAut (LinPSL d F), ∀ s s' : ↥(LinSL d F),
      (s' : GL (Fin d) F) = g * s * g⁻¹ → φ (LinMk d F s) = LinMk d F s' := by
  refine ⟨CFSG.StandardType.TableB.linConjAut (Fin d) F g, fun s s' hs => ?_⟩
  change CFSG.StandardType.TableB.linConjAut (Fin d) F g
      (s : LargeEvenProj (LargeEvenSLGroup (Fin d) F)) =
    (s' : LargeEvenProj (LargeEvenSLGroup (Fin d) F))
  rw [CFSG.StandardType.TableB.linConjAut_mk]
  congr 1
  exact Subtype.ext (by rw [MulAut.conjNormal_apply]; exact hs.symm)

end CFSG.LocalAnalysis.GLTheoremA.T173A

end
