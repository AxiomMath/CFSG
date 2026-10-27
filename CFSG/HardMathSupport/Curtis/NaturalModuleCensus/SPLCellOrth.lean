module

public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.SPLCellOrthInner
public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.SPLCellOrthSmall
public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.SPLCellOrthOuter

public section

open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  CFSG.LocalAnalysis.ComponentInitial.OrthogonalOuter

namespace CFSG.HardMathSupport.Curtis.NaturalModuleCensus.SPLCellOrth

open CFSG.HardMathSupport.Curtis CFSG.HardMathSupport.Curtis.Coordinator

variable {K : Type} [Field K] [Finite K] {n f : ℕ} {Q : QuadraticForm K (Fin (2 * n) → K)}

theorem orth_cell_P (h : OrthCellData Q f) {p r : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hr : r.Prime)
    (hr5 : 5 ≤ r) (hrp : ¬ r ∣ p - 1)
    (hout : ∀ ζ : MulAut (matrixProjectiveDerived Q), ζ ∈ matrixProjectiveImage Q →
      ζ ∉ (linearConjugationHom Q).range → ζ ^ p = 1 → ¬ Group.IsSolvable ↥(autFix ζ)) :
    SPLCellFor (matrixProjectiveDerived Q) p r := by
  intro Ē ζ γ hE hcard hζp hζE hsolv hγ hγE hcomm hnt
  obtain ⟨k, hk⟩ := hγ
  by_cases hn5 : 5 ≤ n
  · rcases h.zeta_cases hn5 hp hp2 hζp with ⟨y, rfl, hyp⟩ | ⟨g, hgζ, -, hζD⟩
    · obtain ⟨g, hg, -⟩ := h.exists_pair_of_prime_power hr (by omega) hk
      subst hg
      exact orth_inner_false h hp hp2 hr hr5 hrp Ē hE hcard y hyp
        (fun e he => by simpa [MulAut.conj_apply] using hζE e he) hsolv g k hk hγE hcomm hnt
    · exact hout ζ ⟨g, hgζ⟩ hζD hζp hsolv
  · exact orth_small_false h (by have := h.four_le_n; omega) hp hp2 hr hr5 hrp Ē hE hcard γ k hk
      hγE hnt

theorem orthPlusCell : OrthPlusCell := by
  intro S _ _ n f hmodel K _ _ hK e p r hp hp2 hr hr5 hrp
  exact SPLCellFor.of_mulEquiv (coordinatePlusWitnessEquiv K e)
    (orth_cell_P (orthCellData_plus hmodel K hK e) hp hp2 hr hr5 hrp
      fun ζ hζE hζD hζp => orth_outer_false_plus hmodel hp hp2 K hK e ζ hζE hζD hζp)

theorem orthMinusCell : OrthMinusCell := by
  intro S _ _ n f hmodel hn1 K _ _ hK b c hirr e p r hp hp2 hr hr5 hrp
  exact SPLCellFor.of_mulEquiv (coordinateMinusWitnessEquiv K hn1 b c e)
    (orth_cell_P (orthCellData_minus hmodel hn1 K hK b c hirr e) hp hp2 hr hr5 hrp
      fun ζ hζE hζD hζp => orth_outer_false_minus hmodel hn1 hp hp2 K hK b c hirr e ζ hζE hζD hζp)

end CFSG.HardMathSupport.Curtis.NaturalModuleCensus.SPLCellOrth

namespace CFSG.HardMathSupport.Curtis.Coordinator

theorem splLieInnerCellFam_D : SPLLieInnerCellFam IsIdxD :=
  NaturalModuleCensus.SPLCellOrth.splLieInnerCellFam_D_of
    NaturalModuleCensus.SPLCellOrth.orthPlusCell

theorem splLieInnerCellFam_TwistedD : SPLLieInnerCellFam IsIdxTwistedD :=
  NaturalModuleCensus.SPLCellOrth.splLieInnerCellFam_twistedD_of
    NaturalModuleCensus.SPLCellOrth.orthMinusCell

end CFSG.HardMathSupport.Curtis.Coordinator
