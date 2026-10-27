module

public import CFSG.HardMathSupport.Dickson.Sec6.I923Aux.FamPSL
public import CFSG.HardMathSupport.Dickson.Sec6.I923Aux.FamPSp
public import CFSG.HardMathSupport.Dickson.Sec6.I923Aux.FamSz
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofLieOrder

public section

namespace CFSG.HardMathSupport.Dickson.Sec6.I923

open CFSG CFSG.Open CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma514CoverNs CFSG.RankThree.PartOne.Sec66T

theorem y923_lieRestAt_pslTwo : Y923_LieRestAt FamPslTwo := by
  intro Y _ _ hq hcore hL2 t n p f hadm ht hF hm α h3 hnot J hJ r hr
  obtain ⟨rfl, rfl⟩ := hF
  have hC : StatedClassicalModel (Y ⧸ Subgroup.center Y) .PSL 2 p f :=
    (lieModel_classical_iff (by decide)).mp hm
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hC
  exact absurd ⟨K, inferInstance, inferInstance, rfl, ⟨e⟩⟩ (hL2 (Nat.card K))

theorem fam_cover {t : StatedLieTag} {n p f : ℕ} (hadm : StatedLieAdmissible t n p f)
    (ht : t ≠ .Tits) :
    FamPslTwo t n p f ∨ FamPslGood t n p f ∨ FamPslBad t n p f ∨ FamPsp t n p f ∨ FamPspTwoEight t n p f ∨ FamPsuGood t n p f ∨ FamPsuBad t n p f ∨ FamOrthOdd t n p f ∨ FamOrthPlus t n p f ∨ FamOrthMinus t n p f ∨ FamD4 t n p f ∨ FamTriD4 t n p f ∨ FamG2 t n p f ∨ FamF4 t n p f ∨ FamE6 t n p f ∨ FamTwE6 t n p f ∨ FamE7 t n p f ∨ FamE8 t n p f ∨ FamSz t n p f ∨ FamReeG2 t n p f ∨ FamReeF4 t n p f := by
  have hadm' := hadm
  cases t
  case PSL =>
    obtain ⟨-, -, hn, -⟩ := hadm
    by_cases h2 : n = 2
    · exact Or.inl (⟨rfl, h2⟩)
    · by_cases hc : Nat.Coprime 3 (Nat.gcd n (p ^ f - 1))
      · exact Or.inr (Or.inl (⟨rfl, by omega, hc⟩))
      · exact Or.inr (Or.inr (Or.inl (⟨rfl, by omega, hc⟩)))
  case PSU =>
    obtain ⟨-, -, hn, -⟩ := hadm
    by_cases hd : 3 ∣ Nat.gcd n (p ^ f + 1)
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨rfl, hn, hd⟩)))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨rfl, hn, hd⟩))))))
  case PSp =>
    obtain ⟨-, -, hn, -⟩ := hadm
    by_cases hx : n = 2 ∧ p ^ f = 8
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨rfl, hx.1, hx.2⟩)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inl (⟨rfl, hn, hx⟩))))
  case POmegaOdd => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (rfl))))))))
  case POmegaPlus =>
    obtain ⟨-, -, hn⟩ := hadm
    by_cases h4 : n = 4
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨rfl, h4⟩)))))))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨rfl, by omega⟩)))))))))
  case POmegaMinus => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (rfl))))))))))
  case G2 => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (rfl)))))))))))))
  case F4 => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (rfl))))))))))))))
  case E6 => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (rfl)))))))))))))))
  case E7 => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (rfl)))))))))))))))))
  case E8 => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (rfl))))))))))))))))))
  case twistedE6 => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (rfl))))))))))))))))
  case trialityD4 => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (rfl))))))))))))
  case twistedB2 => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (rfl)))))))))))))))))))
  case twistedG2 => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (rfl))))))))))))))))))))
  case twistedF4 => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (rfl))))))))))))))))))))
  case Tits => exact absurd rfl ht


section Assembly


theorem y923LieRest_of_families
    (hPslBad : Y923_PslBad)
    (hPsuGood : Y923_PsuGood) (hPsuBad : Y923_PsuBad)
    (hOrthOdd : Y923_OrthOdd) (hOrthPlus : Y923_OrthPlus) (hOrthMinus : Y923_OrthMinus)
    (hD4 : Y923_D4) (hTriD4 : Y923_TriD4)
    (hG2 : Y923_G2) (hF4 : Y923_F4) (hE6 : Y923_E6) (hTwE6 : Y923_TwE6)
    (hE7 : Y923_E7) (hE8 : Y923_E8)
    (hReeG2 : Y923_ReeG2) (hReeF4 : Y923_ReeF4) : Y923_LieRest := by
  have hO := CFSG.ComponentClassification.CatLeafProof.lieOrderFormulasInput
  have hPslTwo := y923_lieRestAt_pslTwo
  have hPslGood := y923_lieRestAt_psl hO
  have hPsp := y923_lieRestAt_psp hO
  have hPspTwoEight := y923_lieRestAt_pspTwoEight
  have hSz := y923_lieRestAt_sz
  exact y923_lieRest_of_cover (fun t n p f hadm ht => fam_cover hadm ht) (hPslTwo.union (hPslGood.union (hPslBad.union (hPsp.union (hPspTwoEight.union (hPsuGood.union (hPsuBad.union (hOrthOdd.union (hOrthPlus.union (hOrthMinus.union (hD4.union (hTriD4.union (hG2.union (hF4.union (hE6.union (hTwE6.union (hE7.union (hE8.union (hSz.union (hReeG2.union (hReeF4)))))))))))))))))))))

end Assembly

end CFSG.HardMathSupport.Dickson.Sec6.I923
