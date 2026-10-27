module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.HStdExclDefs
public import CFSG.LocalAnalysis.GLTheoremA.CatB.I2610HF4Model
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1431cInspF4
public import CFSG.GroupTheory.InnerNormalizedAutomorphisms

public section

namespace CFSG.LocalAnalysis.GLTheoremA.HStdExcl

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)
open CFSG.HardMathSupport.Dickson.Bal207.FamF42 (F42CompType)


theorem exclF4_holds : ExclF4 := by
  intro K _ _ hK α hα3 hα1 I hI hIsmall
  obtain ⟨x, rfl⟩ :=
    CFSG.LocalAnalysis.GLTheoremA.CatB.I2610.exists_eq_conj_of_pow_three_F4 hK hα3
  have hx3 : x ^ 3 = 1 := by
    have hconj : MulAut.conj (x ^ 3) = 1 := by
      rw [map_pow]
      exact hα3
    have hcent := CFSG.InnerNormalizedAutomorphisms.mem_center_of_conj_eq_one hconj
    rwa [center_adjointGroup_eq_bot, Subgroup.mem_bot] at hcent
  have hx1 : x ≠ 1 := by
    rintro rfl
    exact hα1 (map_one _)
  have hxord : orderOf x = 3 := orderOf_eq_prime hx3 hx1
  have hshape := CFSG.HardMathSupport.Dickson.Bal207.FamF42.compShape_conj_F4_two hK x hxord
  have hcard : Nat.card (↥I ⧸ Subgroup.center ↥I) = 1451520 :=
    CFSG.LocalAnalysis.GLTheoremA.H1431c.card_of_f42CompType (hshape.type I hI)
  exfalso
  rcases hIsmall with h | h <;> omega

end CFSG.LocalAnalysis.GLTheoremA.HStdExcl

end
