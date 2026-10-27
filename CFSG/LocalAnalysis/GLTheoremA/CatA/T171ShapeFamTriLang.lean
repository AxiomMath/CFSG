module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeFamTriDefs
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieCompIdxTriality

import CFSG.LocalAnalysis.GLTheoremA.CatC.RationalTypeAModel
import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.InnerTw

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T171Sh

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.RootAut
  CFSG.HardMathSupport.Dickson.Sec6.Up34Exc
  CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp
  CFSG.ComponentClassification.OuterAutomorphisms
  CFSG.LocalAnalysis.GLTheoremA.RationalModel
open scoped MatrixGroups


theorem triCompClassical_holds : TriCompClassical := by
  intro f K _ _ σ hdata p hp hp2 x hxp hx1 J hJ
  classical
  obtain ⟨hf1, hK, hσ⟩ := hdata
  let q : TauCeti.PrimePower := ⟨2, f, Nat.prime_two, hf1⟩
  haveI : Finite (TriGrp K σ) := Subtype.finite
  have hKq : Nat.card K = (q.p ^ q.exponent) ^ 3 := hK
  have hσq : ∀ c, σ c = c ^ (q.p ^ q.exponent) := hσ
  have hpq : p ≠ q.p := hp2
  have hmon : MonomialToralAt Tag.D4 p := by
    by_cases hp3 : p = 3
    · subst hp3
      exact monomialToralAt_three_of_block a2BlockToral_D4
    · exact monomialToralAt_of_not_dvd hp
        (CFSG.RankThree.PartOne.KGD.not_dvd_card_weylGroup_D4 hp
          (by have := hp.two_le; omega))
  obtain ⟨p₀, hp₀, hp₀ℓ, hq₀⟩ :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.exists_setup_prime
      q.prime_p q.exponent_pos hp hp2 hpq
  obtain ⟨S, a, ι, hSq, -, hT, hap, h1, hinj, hrange, hconj⟩ :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.exists_langSetup_of_inner_triD4_of_prime
      q.prime_p q.exponent_pos hKq σ hσq hp hpq hp₀ hp₀ℓ hq₀ hmon x hxp hx1
  have hpL : ((p : ℕ) : AlgebraicClosure K) ≠ 0 :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.natCast_ne_zero_algebraicClosure_of_ne
      q.prime_p hp hKq hpq
  have hTame :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.langSetup_hTame_of_prime
      S hp hpL (fun h => absurd h (by decide)) hT hap h1
  have hJ' : CFSG.Open.IsComponentOf J
      (CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup (MulAut.conj x)) :=
    (CFSG.Assembly.isComponentOf_iff_open).1 hJ
  obtain ⟨i, hqs, hJR⟩ :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieComp.components_of_langSetup
      S hp ι hinj hrange (MulAut.conj x) hconj hT hap h1 hTame hJ'
  have hTp := rootDiagUnit_pow_eq_one_of_forall hap
  have hA := CFSG.LocalAnalysis.GLTheoremA.KD264Lie.typeAShape_d4Class S hp hpL hTp h1 i
  obtain ⟨ν, f', hν, hf', hfeq, hmodel⟩ :=
    rationalComponent_typeA_model S hp hT hap h1 i hA hqs
  have hAC : ringChar (AlgebraicClosure K) = 2 := by
    rw [ringChar_algebraicClosure]
    exact ringChar_eq_of_card_eq_pow (n := q.exponent * 3) q.prime_p
      (by have := q.exponent_pos; omega) (by rw [hK, ← pow_mul])
  rw [hAC] at hmodel
  let R := rationalComponent S.ρ S.Γ (rootCharHom a) i
  let eJ : ↥J ≃* ↥R := (J.equivMapOfInjective ι hinj).trans (MulEquiv.subgroupCongr hJR)
  have hce : (↥J ⧸ Subgroup.center ↥J) ≃* (↥R ⧸ Subgroup.center ↥R) :=
    QuotientGroup.congr (Subgroup.center ↥J) (Subgroup.center ↥R) eJ
      (Subgroup.map_center_eq eJ)
  rcases hmodel with h | h
  · refine ⟨.PSL, ν, f', Or.inl rfl, hν, ?_⟩
    exact CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv hce.symm h
  · refine ⟨.PSU, ν, f', Or.inr rfl, hν, ?_⟩
    exact CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv hce.symm h

end CFSG.LocalAnalysis.GLTheoremA.T171Sh

end
