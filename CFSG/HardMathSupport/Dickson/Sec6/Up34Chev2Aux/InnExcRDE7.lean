module

public import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.InnExcRDCheck2

public section

namespace CFSG.HardMathSupport.Dickson.Sec6.Up34Exc

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups

namespace RD

@[expose] def okE7 (s : ℕ) : Bool :=
  s == 2 || s == 6 || s == 30 || s == 40 || s == 42 || s == 60 || s == 72 || s == 126

set_option maxRecDepth 100000 in
theorem rdCheck2_E7 : rdCheck2 .E7 127 okE7 = true := by decide +kernel

end RD


theorem rdValues_E7 : ∀ (L : Type) [Field L] [CharP L 2] (a : Fin Tag.E7.rank → Lˣ),
    (∀ j, a j ^ 3 = 1) → ∀ i : KernelComponent (rootCharHom a),
      (componentRoots (rootCharHom a) i).ncard = 2 ∨ (componentRoots (rootCharHom a) i).ncard = 6 ∨
        (componentRoots (rootCharHom a) i).ncard = 30 ∨
        (componentRoots (rootCharHom a) i).ncard = 40 ∨
        (componentRoots (rootCharHom a) i).ncard = 42 ∨
        (componentRoots (rootCharHom a) i).ncard = 60 ∨
        (componentRoots (rootCharHom a) i).ncard = 72 ∨
        (componentRoots (rootCharHom a) i).ncard = 126 := by
  intro L _ _ a ha i
  obtain ⟨s, hs, h | h⟩ := RD.size_of_check2 RD.noG2_E7 127 RD.okE7 RD.rdCheck2_E7 a ha i
  · obtain ⟨h1, h2⟩ := h
    simp only [RD.okE7, Bool.or_eq_true, beq_iff_eq] at hs
    omega
  · obtain ⟨rfl, -⟩ := h
    simp [RD.okE7] at hs

theorem rdSize_E7 : RDSize .E7 := by
  intro L _ _ a ha i
  have := rdValues_E7 L a ha i
  omega

theorem rdGlue_E7 : RDGlue .E7 := by
  intro L _ _ a ha i hi
  exact RD.glue_of_check2 RD.noG2_E7 127 RD.okE7 (by norm_num) RD.rdCheck2_E7 a ha i hi

end CFSG.HardMathSupport.Dickson.Sec6.Up34Exc
