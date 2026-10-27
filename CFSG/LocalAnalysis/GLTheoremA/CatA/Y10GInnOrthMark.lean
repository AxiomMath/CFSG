module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GField

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10GInnOrthMark

open CFSG.Open CFSG.Assembly CFSG.LocalAnalysis.GLTheoremA.Y10GField

theorem innDiagKind_orth_data {S : Type} [Group S] [Finite S] {labK : GLALabel} {α : MulAut S}
    (hcen : Subgroup.center S = ⊥) (hFam : FamOrth labK) (hin : InnDiagKind S labK α) :
    (StatedClassicalModel S .POmegaPlus labK.rank 2 (canonLabel labK).n ∨
      StatedClassicalModel S .POmegaMinus labK.rank 2 (canonLabel labK).n) ∧
      ∃ a : S, MulAut.conj a = α := by
  unfold InnDiagKind CFSG.Assembly.LargeEvenMarking at hin
  obtain ⟨-, lab', hlam, hraw⟩ := hin
  obtain ⟨_, _, _, _, hQ⟩ := CFSG.StandardType.Canonical.largeEvenRawDatum_exists hraw
  obtain ⟨-, -, -, hlab, -⟩ := hQ
  subst lab'
  rcases hFam with ⟨htag, hr3⟩ | ⟨htag, hr2, hr3⟩
  ·
    have h1n : 1 ≤ labK.n := hlam.1
    have hm3 : 3 ≤ labK.rank := by
      have h := hlam
      simp only [LargeEvenInLambda2, htag] at h
      exact h.2
    have hm4 : 4 ≤ labK.rank := by omega
    have hc : (canonLabel labK).n = labK.n := by simp [canonLabel, htag, hr3]
    unfold CFSG.Assembly.LargeEvenRawDatum at hraw
    simp only [htag, hr3, ↓reduceIte] at hraw
    unfold LargeEvenRecipeOmegaPlus at hraw
    obtain ⟨K, hKf, hKfin, hcard, hQ'⟩ := hraw
    obtain ⟨-, -, θ, -, u, hu, hind⟩ := hQ'
    simp only [LargeEvenInnSet] at hu
    obtain ⟨r, rfl⟩ := hu
    let e : S ≃* LargeEvenProj (LargeEvenOmega (LargeEvenQPlus K labK.rank)) :=
      ((QuotientGroup.quotientMulEquivOfEq hcen).trans QuotientGroup.quotientBot).symm.trans θ
    refine ⟨?_, ?_⟩
    · left
      rw [hc]
      exact CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv e.symm
        (CFSG.StandardType.statedClassicalModel_omegaPlus labK.rank labK.n hcard
          ⟨Nat.prime_two, h1n, hm4⟩)
    · refine ⟨e.symm r, ?_⟩
      refine MulEquiv.ext fun s => ?_
      apply e.injective
      rw [MulAut.conj_apply, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
      exact hind s (α s) rfl
  ·
    have hΛ : 1 ≤ labK.n ∧ 2 ≤ labK.rank := by
      have h := hlam
      simp only [LargeEvenInLambda2, htag] at h
      exact h
    have hm4 : 4 ≤ labK.rank := by omega
    have hc : (canonLabel labK).n = labK.n := by simp [canonLabel, htag, hr2, hr3]
    unfold CFSG.Assembly.LargeEvenRawDatum at hraw
    simp only [htag, hr2, hr3, ↓reduceIte] at hraw
    unfold LargeEvenRecipeOmegaMinus at hraw
    obtain ⟨K, hKf, hKfin, hcard, b, c, hbc, hQ'⟩ := hraw
    obtain ⟨-, -, θ, -, u, hu, hind⟩ := hQ'
    simp only [LargeEvenInnSet] at hu
    obtain ⟨r, rfl⟩ := hu
    let e : S ≃* LargeEvenProj (LargeEvenOmega (LargeEvenQMinus (labK.rank - 1) b c)) :=
      ((QuotientGroup.quotientMulEquivOfEq hcen).trans QuotientGroup.quotientBot).symm.trans θ
    refine ⟨?_, ?_⟩
    · right
      rw [hc]
      exact CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv e.symm
        (CFSG.StandardType.statedClassicalModel_omegaMinus labK.rank labK.n hcard b c hbc
          ⟨Nat.prime_two, hΛ.1, hm4⟩)
    · refine ⟨e.symm r, ?_⟩
      refine MulEquiv.ext fun s => ?_
      apply e.injective
      rw [MulAut.conj_apply, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
      exact hind s (α s) rfl

end CFSG.LocalAnalysis.GLTheoremA.Y10GInnOrthMark

end
