module

public import CFSG.LocalAnalysis.RankThreeUC.ProofSupport.Y2ConjugationInvariance.Y2ConjugationInvariance

public section

namespace CFSG.LocalAnalysis.RankThreeUC.ProofSupport.ResidualConjugateClosure

open CFSG.LocalAnalysis.RankThreeUC SourceSetting Subgroup

variable {G : Type} [Group G]

theorem oPrimeResidual_mono {p : ℕ} {A B : Subgroup G} (h : A ≤ B) :
    oPrimeResidual p A ≤ oPrimeResidual p B := by
  unfold oPrimeResidual
  exact closure_mono fun x hx => ⟨h hx.1, hx.2⟩

theorem oPrimeResidual_le (p : ℕ) (Y : Subgroup G) : oPrimeResidual p Y ≤ Y := by
  unfold oPrimeResidual
  exact (closure_le Y).2 fun x hx => hx.1

theorem oPrimeResidual_oPrimeResidual (p : ℕ) (Y : Subgroup G) :
    oPrimeResidual p (oPrimeResidual p Y) = oPrimeResidual p Y := by
  refine le_antisymm (oPrimeResidual_le p _) ?_
  have : oPrimeResidual p Y ≤ oPrimeResidual p (oPrimeResidual p Y) := by
    unfold oPrimeResidual
    refine (closure_le _).2 fun x hx => ?_
    exact subset_closure ⟨subset_closure hx, hx.2⟩
  exact this

theorem oPrimeResidual_normalClosureUnder_oPrimeResidual [Finite G] (p : ℕ) (Y A : Subgroup G) :
    oPrimeResidual p (normalClosureUnder (oPrimeResidual p Y) A) =
      normalClosureUnder (oPrimeResidual p Y) A := by
  set R := oPrimeResidual p Y with hR
  set K := normalClosureUnder R A with hK
  apply le_antisymm (by
    unfold oPrimeResidual
    exact (closure_le K).2 fun x hx => hx.1)
  rw [hK]
  unfold normalClosureUnder
  refine iSup_le fun h => ?_
  have hle : R.map (MulAut.conj (h : G)).toMonoidHom ≤ K :=
    le_iSup (fun h : A => R.map (MulAut.conj (h : G)).toMonoidHom) h
  have e := Y2ConjugationInvariance.map_oPrimeResidual (h : G) p R
  rw [hR, oPrimeResidual_oPrimeResidual] at e
  calc R.map (MulAut.conj (h : G)).toMonoidHom
      = oPrimeResidual p (R.map (MulAut.conj (h : G)).toMonoidHom) := by
        exact e
    _ ≤ oPrimeResidual p K := oPrimeResidual_mono hle
    _ = _ := rfl

end CFSG.LocalAnalysis.RankThreeUC.ProofSupport.ResidualConjugateClosure
