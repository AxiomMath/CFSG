module

public import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.InnExcRDCheck2

public section

namespace CFSG.HardMathSupport.Dickson.Sec6.Up34Exc

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups

namespace RD

@[expose] def okE6 (s : ℕ) : Bool :=
  s == 2 || s == 6 || s == 20 || s == 24 || s == 30 || s == 40 || s == 72

set_option maxRecDepth 100000 in
theorem rdCheck2_E6 : rdCheck2 .E6 73 okE6 = true := by decide +kernel

end RD


theorem rdValues_E6 : ∀ (L : Type) [Field L] [CharP L 2] (a : Fin Tag.E6.rank → Lˣ),
    (∀ j, a j ^ 3 = 1) → ∀ i : KernelComponent (rootCharHom a),
      (componentRoots (rootCharHom a) i).ncard = 2 ∨ (componentRoots (rootCharHom a) i).ncard = 6 ∨
        (componentRoots (rootCharHom a) i).ncard = 20 ∨
        (componentRoots (rootCharHom a) i).ncard = 24 ∨
        (componentRoots (rootCharHom a) i).ncard = 30 ∨
        (componentRoots (rootCharHom a) i).ncard = 40 ∨
        (componentRoots (rootCharHom a) i).ncard = 72 := by
  intro L _ _ a ha i
  obtain ⟨s, hs, h | h⟩ := RD.size_of_check2 RD.noG2_E6 73 RD.okE6 RD.rdCheck2_E6 a ha i
  · obtain ⟨h1, h2⟩ := h
    simp only [RD.okE6, Bool.or_eq_true, beq_iff_eq] at hs
    omega
  · obtain ⟨rfl, -⟩ := h
    simp [RD.okE6] at hs

theorem rdSize_E6 : RDSize .E6 := by
  intro L _ _ a ha i
  have := rdValues_E6 L a ha i
  omega

theorem rdGlue_E6 : RDGlue .E6 := by
  intro L _ _ a ha i hi
  exact RD.glue_of_check2 RD.noG2_E6 73 RD.okE6 (by norm_num) RD.rdCheck2_E6 a ha i hi

end CFSG.HardMathSupport.Dickson.Sec6.Up34Exc
