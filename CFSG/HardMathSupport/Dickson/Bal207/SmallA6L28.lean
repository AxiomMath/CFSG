module

public import CFSG.HardMathSupport.Dickson.Bal207.SmallBridge
public import CFSG.HardMathSupport.Dickson.I271.Support.AmbAlt
public import CFSG.HardMathSupport.Dickson.I271.Support.AmbL2

public section

namespace CFSG.HardMathSupport.Dickson.Bal207.Small

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Solomon.Coordinator.ChevQ
  CFSG.HardMathSupport.Dickson.I271

theorem bal207PlusSmallA6
    (G : ∀ (S : Type) [Group S], MulAut S → Prop) : Bal207PlusSmallA6 G := by
  intro X _ _ hX K B A ctx hIH a haA ha1 J hJ hS hBJ
  obtain ⟨⟨eJ⟩, h3⟩ := hS
  obtain ⟨hsn, hJC, hH⟩ := small_data ctx haA hJ hBJ
  haveI : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
  obtain ⟨⟨e₃⟩, hdvd⟩ := barX_centralQuotient hJC eJ.isSimpleGroup
  refine stronglyLocallyOneBalanced_of_bar ctx.prime hsn hBJ ?_
  rcases Amb.a6Case hH.core hH.comp hH.scp hH.norm (e₃.symm.trans eJ) with h | ⟨⟨-, hc, -⟩, -⟩
  · exact h
  · rw [hc] at hdvd
    exact absurd hdvd h3

theorem bal207PlusSmallL28
    (G : ∀ (S : Type) [Group S], MulAut S → Prop) : Bal207PlusSmallL28 G := by
  intro X _ _ hX K B A ctx hIH a haA ha1 J hJ hS hBJ
  obtain ⟨hsn, hJC, hH⟩ := small_data ctx haA hJ hBJ
  obtain ⟨⟨d, hv⟩, hd, ⟨eJ⟩⟩ := hS
  obtain ⟨q, rfl, hq⟩ := hd.exists
  haveI : Fact q.p.Prime := ⟨q.prime_p⟩
  have hF8 : Nat.card (GaloisField q.p q.exponent) = 8 := by
    rw [GaloisField.card q.p q.exponent q.exponent_pos.ne', hq.1, hq.2]
    norm_num
  let eJ' := eJ.trans (CFSG.ClassicalModels.linearCatalogCandidateEquivPSL 1 q hv)
  haveI : IsSimpleGroup
      (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField q.p q.exponent)) :=
    Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by rw [hF8]; norm_num)
  obtain ⟨⟨e₃⟩, -⟩ := barX_centralQuotient hJC eJ'.isSimpleGroup
  refine stronglyLocallyOneBalanced_of_bar ctx.prime hsn hBJ ?_
  exact Amb.l2EightCase hH.core hH.comp hH.scp hH.norm hF8 (e₃.symm.trans eJ')

end CFSG.HardMathSupport.Dickson.Bal207.Small

end
