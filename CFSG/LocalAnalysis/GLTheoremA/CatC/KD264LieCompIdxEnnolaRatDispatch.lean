module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieCompIdxEnnolaRatInner
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieCompIdxEnnolaRatOuterE
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieCompIdxEnnolaRatOuterD

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie
namespace ExcUntw

section

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.HardMathSupport.Timmesfeld.RootAut
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp
  CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple CFSG.StandardType.RecipeExcLang
  CFSG.ComponentClassification.OuterAutomorphisms
open scoped MatrixGroups

theorem excUntwRationalCatalogueExpAt_of_outer
    {τ : Tag}
    (hτ : τ = .G2 ∨ τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    (hD : (τ = .E6 ∨ τ = .E7 ∨ τ = .E8) → ExcUntwOuterDCatalogueExpAt τ)
    (hE : (τ = .E7 ∨ τ = .E8) → ExcUntwOuterECatalogueExpAt τ) :
    ExcUntwRationalCatalogueExpAt τ := by
  intro L _ _ p₀ S hFr p hp hp2 a hT hap h1 i hq
  classical
  have hp2' : p % 2 = 1 := (hp.eq_two_or_odd).resolve_left hp2
  have hℓp : ringChar L ≠ p := ringChar_ne_of_pow_eq_one hp hap h1
  have hpL : ((p : ℕ) : L) ≠ 0 := natCast_ne_zero_of_ringChar_ne hp hℓp
  have hTp := rootDiagUnit_pow_eq_one_of_forall hap
  by_cases hA : 1 ≤ compRank (componentRoots (rootCharHom a) i) ∧
      (componentRoots (rootCharHom a) i).ncard = compRank (componentRoots (rootCharHom a) i) *
        (compRank (componentRoots (rootCharHom a) i) + 1)
  · exact ⟨_, Or.inl rfl,
      catalogueOver_rationalComponent_typeA S hp hT hap h1 i hA hq⟩
  by_cases hinner : twistInner (componentRoots (rootCharHom a) i)
      ((S.ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength S.ρ
        (componentRoots (rootCharHom a) i)])
  ·
    cases τ with
    | G2 => exact (false_of_g2Class_nonAP hp S hpL hTp h1 i hA).elim
    | F4 => exact ratCatExp_of_inner_nonA_F4 hp hp2 S hT hap h1 i hA hinner hq
    | D4 => exact absurd hτ (by decide)
    | E6 => exact ratCatExp_of_inner_nonA_E6 S hp hpL hT hTp i hA hinner
    | E7 => exact ratCatExp_of_inner_nonA_E7 S hp hpL hT hTp i hA hinner
    | E8 => exact ratCatExp_of_inner_nonA_E8 S hp hpL hT hTp i hA hinner
  ·
    cases τ with
    | G2 => exact (false_of_g2Class_nonAP hp S hpL hTp h1 i hA).elim
    | F4 =>
      rcases f4_nonA_casesP hp hp2' S hpL hTp h1 i hA with ⟨hr, hn⟩ | ⟨v, J, -, -, hr, hn⟩
      · exact (hinner (twistInner_of_shape S hT i 2 8 hr hn (by omega) (by omega) (by omega)
          (by omega))).elim
      · exact (hinner (twistInner_of_shape S hT i 3 18 hr hn (by omega) (by omega) (by omega)
          (by omega))).elim
    | D4 => exact absurd hτ (by decide)
    | E6 =>
      obtain ⟨v, μ, x, c, -, hc, -, hlen, hroots, hrank, hncard⟩ :=
        exists_cand_of_class kacE6 facts_E6 e6_tree e6_adj e6_check e6_lt e6_card S hp hpL hTp i
      have hshape := e6_shape c hc hlen
      rw [← hncard, ← hrank] at hshape
      rcases hshape with hA' | hD' | hE'
      · exact (hA hA').elim
      · exact hD (Or.inl rfl) L p₀ S hFr p hp hp2 a hT hap h1 i hD' hinner hq
      · exact (false_of_e6Class_E S hp hpL hTp h1 i hE'.1 hE'.2).elim
    | E7 =>
      obtain ⟨v, μ, x, c, -, hc, -, hlen, hroots, hrank, hncard⟩ :=
        exists_cand_of_class kacE7 facts_E7 e7_tree e7_adj e7_check e7_lt e7_card S hp hpL hTp i
      have hshape := e7_shape c hc hlen
      rw [← hncard, ← hrank] at hshape
      rcases hshape with hA' | hD' | hE'
      · exact (hA hA').elim
      · exact hD (Or.inr (Or.inl rfl)) L p₀ S hFr p hp hp2 a hT hap h1 i hD' hinner hq
      · exact hE (Or.inl rfl) L p₀ S p hp hp2 a hT hap h1 i hE'.1 hE'.2 hinner
    | E8 =>
      obtain ⟨v, μ, x, c, -, hc, -, hlen, hroots, hrank, hncard⟩ :=
        exists_cand_of_class kacE8 facts_E8 e8_tree e8_adj e8_check e8_lt e8_card S hp hpL hTp i
      have hshape := e8_shape c hc hlen
      rw [← hncard, ← hrank] at hshape
      rcases hshape with hA' | hD' | hE'
      · exact (hA hA').elim
      · exact hD (Or.inr (Or.inr rfl)) L p₀ S hFr p hp hp2 a hT hap h1 i hD' hinner hq
      · exact hE (Or.inr rfl) L p₀ S p hp hp2 a hT hap h1 i hE'.1 hE'.2 hinner

theorem excUntwRationalCatalogueExpAt_F4
    : ExcUntwRationalCatalogueExpAt .F4 := by
  exact excUntwRationalCatalogueExpAt_of_outer (Or.inr (Or.inl rfl))
    (fun h => by rcases h with h | h | h <;> exact absurd h (by decide))
    (fun h => by rcases h with h | h <;> exact absurd h (by decide))

theorem excUntwRationalCatalogueExpAt_E7
    : ExcUntwRationalCatalogueExpAt .E7 := by
  exact excUntwRationalCatalogueExpAt_of_outer (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
    (fun h => excUntwOuterDCatalogueExp_holds .E7 h)
    (fun h => excUntwOuterECatalogueExp_holds .E7 h)

theorem excUntwRationalCatalogueExpAt_E8
    : ExcUntwRationalCatalogueExpAt .E8 := by
  exact excUntwRationalCatalogueExpAt_of_outer (Or.inr (Or.inr (Or.inr (Or.inr rfl))))
    (fun h => excUntwOuterDCatalogueExp_holds .E8 h)
    (fun h => excUntwOuterECatalogueExp_holds .E8 h)

end

end ExcUntw
end CFSG.LocalAnalysis.GLTheoremA.KD264Lie

end
