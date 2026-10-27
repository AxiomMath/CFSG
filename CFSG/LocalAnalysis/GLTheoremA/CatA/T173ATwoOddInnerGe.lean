module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173ATwoStdForm
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173ATwoOddTransv
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173ATwoOddGen

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T173A

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.Assembly CFSG.LocalAnalysis.GLTheoremA
open CFSG.LocalAnalysis.GLTheoremA.S172A.GL (fixSp comSp)
open CFSG.LocalAnalysis.GLTheoremA.T173X
  (stdLayer innerClosure stdFamily IsStdElt StdVanishes StdTyped StdExtends)

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]

theorem lin_two_oddFull_oddBlock_le (hV : 6 ≤ Module.finrank (ZMod 2) V)
    {A : Subgroup (V ≃ₗ[ZMod 2] V)} {g : V ≃ₗ[ZMod 2] V} (hA : GLAIsBmax 3 A)
    (hg : IsStdElt 3 A g) (hfix : Module.finrank (ZMod 2) (fixSp g) = 1) :
    linTwoOddBlock g ≤ innerClosure A g := by
  obtain ⟨hgA, -, hg3, -, -⟩ := hg
  obtain ⟨x, P, V0, hF⟩ := lin_two_std_form_of_bmax (by omega) hA
  have hsum := S172A.GL.finrank_fixSp hg3
  obtain ⟨m, hm⟩ := S172A.GL.even_finrank_comSp hg3
  have hodd : Odd (Module.finrank (ZMod 2) V) := ⟨m, by omega⟩
  obtain ⟨hfixV0, hcomW⟩ := lin_two_frame_full_support hF hodd hgA hg3 hfix
  refine (lin_two_cross_transv_generate hF (by omega) hg3 hfixV0 hcomW).trans ?_
  rw [Subgroup.closure_le]
  rintro _ ⟨i, j, hij, a, ha, f, hfV0, hfP, rfl⟩
  exact lin_two_oddFull_transv_mem hF hgA hg3 hfix hij ha f hfV0 hfP

end CFSG.LocalAnalysis.GLTheoremA.T173A

end
