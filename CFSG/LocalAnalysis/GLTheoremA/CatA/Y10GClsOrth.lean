module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GClsOrthKind

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10GClsOrth

open CFSG.Assembly CFSG.LocalAnalysis.GLTheoremA.Y10GField

theorem clsOrth_holds : ClsOrth := by
  intro S _ _ p α labK hfam hp hp2 _ hlab hα
  have hΛ : LargeEvenInLambda2 labK := by
    obtain ⟨-, lab, hl, _, _, _, _, _, -, -, hEq⟩ :=
      CFSG.StandardType.Canonical.largeEvenMarking_exists hlab
    exact (show lab = labK from hEq) ▸ hl
  rcases hfam with ⟨ht, hr3⟩ | ⟨ht, hr2, hr3⟩
  · have h3 : 3 ≤ labK.rank := by
      have h := hΛ.2
      rw [ht] at h
      exact h
    have h4 : 4 ≤ labK.rank := by omega
    rcases Nat.lt_or_ge labK.rank 5 with h5 | h5
    · have hr4 : labK.rank = 4 := by omega
      by_cases hp3 : p = 3
      · exact Or.inr (Or.inr ⟨ht, hr4, hp3⟩)
      · refine (innDiagKind_or_fieldKind hlab hα
          (canonicalLabelAll_omegaPlus ht h4 fun K _ _ _ _ => ?_)).imp_right Or.inl
        rw [hr4]
        exact rawOddInnField_omegaPlusFour hp hp2 hp3
    · exact (innDiagKind_or_fieldKind hlab hα (canonicalLabelAll_omegaPlus ht h4
        fun K _ _ _ _ => rawOddInnField_omegaPlus h5 hp hp2)).imp_right Or.inl
  · have h2 : 2 ≤ labK.rank := by
      have h := hΛ.2
      rw [ht] at h
      exact h
    have h4 : 4 ≤ labK.rank := by omega
    exact (innDiagKind_or_fieldKind hlab hα (canonicalLabelAll_omegaMinus ht h4
      fun K _ _ _ hK b c hirr => rawOddInnField_omegaMinus h4 hirr hK p)).imp_right Or.inl

end CFSG.LocalAnalysis.GLTheoremA.Y10GClsOrth
