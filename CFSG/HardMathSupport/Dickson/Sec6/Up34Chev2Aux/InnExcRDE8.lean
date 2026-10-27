module

public import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.InnExcRDCheck2

public section

namespace CFSG.HardMathSupport.Dickson.Sec6.Up34Exc

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups

namespace RD

@[expose] def okE8 (s : ℕ) : Bool := s == 6 || s == 72 || s == 84 || s == 126 || s == 240

set_option maxHeartbeats 400000 in
set_option maxRecDepth 100000 in
theorem rdCheck2_E8 : rdCheck2 .E8 241 okE8 = true := by decide +kernel

end RD


theorem rdValues_E8 : ∀ (L : Type) [Field L] [CharP L 2] (a : Fin Tag.E8.rank → Lˣ),
    (∀ j, a j ^ 3 = 1) → ∀ i : KernelComponent (rootCharHom a),
      (componentRoots (rootCharHom a) i).ncard = 6 ∨ (componentRoots (rootCharHom a) i).ncard = 72 ∨
        (componentRoots (rootCharHom a) i).ncard = 84 ∨
        (componentRoots (rootCharHom a) i).ncard = 126 ∨
        (componentRoots (rootCharHom a) i).ncard = 240 := by
  intro L _ _ a ha i
  obtain ⟨s, hs, h | h⟩ := RD.size_of_check2 CFSG.LieType.Steinberg.Adjoint.noG2_E8 241 RD.okE8 RD.rdCheck2_E8 a ha i
  · obtain ⟨h1, h2⟩ := h
    simp only [RD.okE8, Bool.or_eq_true, beq_iff_eq] at hs
    omega
  · obtain ⟨rfl, -⟩ := h
    simp [RD.okE8] at hs

theorem rdSize_E8 : RDSize .E8 := by
  intro L _ _ a ha i
  have := rdValues_E8 L a ha i
  omega

theorem rdGlue_E8 : RDGlue .E8 := by
  intro L _ _ a ha i hi
  exact RD.glue_of_check2 CFSG.LieType.Steinberg.Adjoint.noG2_E8 241 RD.okE8 (by norm_num) RD.rdCheck2_E8 a ha i hi

end CFSG.HardMathSupport.Dickson.Sec6.Up34Exc
