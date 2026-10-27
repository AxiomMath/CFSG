module

public import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.InnExcRDCheck

public section

namespace CFSG.HardMathSupport.Dickson.Sec6.Up34Exc

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups

namespace RD

@[expose] def okF4 (s : ℕ) : Bool := s == 6 || s == 18 || s == 48

set_option maxRecDepth 100000 in
theorem rdCheck_F4 : rdCheck .F4 49 okF4 = true := by decide +kernel

end RD

theorem rdValues_F4 : ∀ (L : Type) [Field L] [CharP L 2] (a : Fin Tag.F4.rank → Lˣ),
    (∀ j, a j ^ 3 = 1) → ∀ i : KernelComponent (rootCharHom a),
      (componentRoots (rootCharHom a) i).ncard = 6 ∨ (componentRoots (rootCharHom a) i).ncard = 18 ∨
        (componentRoots (rootCharHom a) i).ncard = 48 := by
  intro L _ _ a ha i
  obtain ⟨s, hs, h | h⟩ := RD.size_of_check 49 RD.okF4 RD.rdCheck_F4 a ha i
  · obtain ⟨h1, h2⟩ := h
    simp only [RD.okF4, Bool.or_eq_true, beq_iff_eq] at hs
    omega
  · obtain ⟨rfl, -⟩ := h
    simp [RD.okF4] at hs

theorem rdSize_F4 : RDSize .F4 := by
  intro L _ _ a ha i
  have := rdValues_F4 L a ha i
  omega

theorem rdGlue_F4 : RDGlue .F4 := by
  intro L _ _ a ha i hi
  exact RD.glue_of_check 49 RD.okF4 (by norm_num) RD.rdCheck_F4 a ha i hi

end CFSG.HardMathSupport.Dickson.Sec6.Up34Exc
