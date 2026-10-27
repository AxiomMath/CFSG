module

public import CFSG.HardMathSupport.Dickson.Sec6.I923Fam.PsuBadAux.SixTwoMain
public import CFSG.HardMathSupport.Dickson.Sec6.I923Fam.PsuGoodAux.Descent

public section

namespace CFSG.HardMathSupport.Dickson.Sec6.I923

open CFSG CFSG.Open CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ComponentClassification.CatLeaf
  CFSG.RankThree.PartOne.KCUnitaryModel

@[expose] def FamPsuSixTwo : StatedLieTag → ℕ → ℕ → ℕ → Prop :=
  fun t n p f => t = .PSU ∧ n = 6 ∧ p = 2 ∧ f = 1

theorem y923_lieRestAt_psuSixTwo (hO : LieOrderFormulasInput) : Y923_LieRestAt FamPsuSixTwo := by
  intro Y _ _ hq hcore hL2 t n p f hadm ht hF hm α h3 hnot J hJ r hr
  obtain ⟨rfl, rfl, rfl, rfl⟩ := hF
  obtain ⟨K, _, h, ⟨e0⟩⟩ := exists_psu_model hadm hm
  have hcard : Nat.card (primeFormP h (idGram K 6)) ∣ 9196830720 := by
    obtain ⟨-, hM, -⟩ := hO _ .PSU 6 2 1 hadm hm
    have hnum : lieOrderNumerator .PSU 6 (2 ^ 1) = 27590492160 := by decide +kernel
    have hdiv : lieOrderDivisor .PSU 6 (2 ^ 1) = 3 := by decide +kernel
    rw [hnum, hdiv] at hM
    have hX : Nat.card (Y ⧸ Subgroup.center Y) = 9196830720 := by omega
    rw [← Nat.card_congr e0.toEquiv, hX]
  exact noL2_of_famOK hq e0 (fun ψ hψ3 hninn =>
    ⟨1, ψ, by simp, noL2Layer_psu_sixTwo hO h hcard hψ3 hninn⟩) h3 hnot hJ hr

end CFSG.HardMathSupport.Dickson.Sec6.I923
