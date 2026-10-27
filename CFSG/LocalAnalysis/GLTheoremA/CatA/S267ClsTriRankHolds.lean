module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267ClsTriRankGraph
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267ClsTriRankGraphField
import CFSG.LocalAnalysis.GLTheoremA.CatA.S2019OrthD4GraphReduce
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267ClsTriRank

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S267.Cls

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.HardMathSupport.Lang.D4Three
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData


theorem d4TriRank_holds : D4TriRank := by
  intro K _ _ Q₈ hodd h3 hplus y hy3 hyE
  classical
  haveI : Fintype K := Fintype.ofFinite K
  obtain ⟨ℓ, hchar⟩ := CharP.exists K
  obtain ⟨n, hℓ, hn⟩ := FiniteField.card K ℓ
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  have hK : Nat.card K = ℓ ^ (n : ℕ) := by rw [Nat.card_eq_fintype_card, hn]
  have hℓ2 : ℓ ≠ 2 := by
    rintro rfl
    exact Nat.not_even_iff_odd.mpr hodd
      (even_iff_two_dvd.mpr (hK ▸ dvd_pow_self 2 n.ne_zero))
  have hℓ3 : ℓ ≠ 3 := by
    rintro rfl
    exact h3 (hK ▸ dvd_pow_self 3 n.ne_zero)
  have hℓ5 : 5 ≤ ℓ := by
    have h2 := hℓ.two_le
    by_contra h
    have h4 : ℓ = 4 := by omega
    rw [h4] at hℓ
    norm_num at hℓ
  have hp5 : 5 ≤ ringChar K := by rw [ringChar.eq K ℓ]; exact hℓ5
  have hK5 : 5 ≤ Nat.card K := by
    rw [hK]
    exact hℓ5.trans (Nat.le_self_pow n.ne_zero ℓ)
  obtain ⟨m, hm⟩ := exists_isCrossSimilarity_coordinateQuadPlus hplus
  set Ψ := matrixProjectiveCrossEquiv hm with hΨ
  set t := MulAut.congr Ψ y with ht
  have ht3 : t ^ 3 = 1 := by rw [ht, ← map_pow, hy3, map_one]
  have htE : t ∉ matrixProjectiveImage (coordinateQuadPlus 4 K) := fun h =>
    hyE ((congr_mem_matrixProjectiveImage_cross_iff hm y).mp h)
  obtain ⟨g, a, σ, ε, hε, hε0, -, hαeq⟩ :=
    S2019.exists_graph_normalForm_of_not_mem_matrixProjectiveImage K ℓ n hℓ hK t ht3 htE
  set Φ := coordinatePlusWitnessEquiv K (CFSG.HardMathSupport.Dickson.Bal207.D4Graph.isoAdj K).symm
    with hΦ
  set α := MulAut.congr Φ.symm t with hα
  have hα3 : α ^ 3 = 1 := by rw [hα, ← map_pow, ht3, map_one]
  have hfix : FixRankTwo α := by
    by_cases hσ1 : σ = 1
    · subst hσ1
      exact fixRankTwo_d4_graph hp5 hK5 h3 hα3 g a ε hε hε0 hαeq
    · exact fixRankTwo_d4_graphField hℓ2 hℓ3 K hK α hα3 g a σ ε hε hε0 hσ1 hαeq
  exact FixRankTwo.of_congr Ψ (FixRankTwo.of_congr Φ.symm hfix)

end CFSG.LocalAnalysis.GLTheoremA.S267.Cls
