module

public import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.InnExcTwistedLane
public import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.InnExcPlumb
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwoDFour

public section

namespace CFSG.HardMathSupport.Dickson.Sec6

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Solomon.UniquenessMaximal CFSG.LocalAnalysis.GLTheoremB
  CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2 CFSG.RankThree.PartOne.KD4T
  CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple

namespace Up34Exc

section Rank

@[expose] def Char2HratRank (τ : Tag) (k : TwistKind) (P : ℕ → ℕ → Prop) : Prop :=
  ∀ (L : Type) [Field L] [IsAlgClosed L] [CharP L 2] (p₀ : ℕ) (S : LangSetup τ L p₀)
    (a : Fin τ.rank → Lˣ), rootDiagUnit τ a ∈ S.D.torus → (∀ j, a j ^ 3 = 1) →
    rootDiagUnit τ a ≠ 1 → ∀ i : KernelComponent (rootCharHom a),
      twistKind S.ρ (rootCharHom a) i = k →
      P (compRank (componentRoots (rootCharHom a) i)) (componentRoots (rootCharHom a) i).ncard →
      CFSG.IsQuasisimple (rationalComponent S.ρ S.Γ (rootCharHom a) i) →
      IsLThreeFour (↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸
        Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)) →
      ∃ z : ModGL τ L, z ∈ rationalComponent S.ρ S.Γ (rootCharHom a) i ∧
        (∀ g ∈ rationalComponent S.ρ S.Γ (rootCharHom a) i, g * z = z * g) ∧
        z ^ 3 = 1 ∧ z ≠ 1

end Rank

section Kinds

set_option linter.unusedSectionVars false

theorem char2Hrat_twoD_of_high {τ : Tag} (hH : Char2HratRank τ .twoD fun r _ => 5 ≤ r) :
    Char2Hrat τ .twoD := by
  intro L _ _ _ p₀ S a hT hap h1 i hk hq hL34
  obtain ⟨hnin, h4, hcard⟩ := twoD_kind_unpack hk
  by_cases h5 : 5 ≤ compRank (componentRoots (rootCharHom a) i)
  · exact hH L p₀ S a hT hap h1 i hk h5 hq hL34
  · exfalso
    have hr : compRank (componentRoots (rootCharHom a) i) = 4 := by omega
    have hTp : rootDiagUnit τ a ^ 3 = 1 := rootDiagUnit_pow_eq_one_of_forall hap
    exact not_isLThreeFour_d4class S hT hTp h1 i hr (by rw [hcard, hr]) hnin hL34

theorem char2Hrat_exc_of_e6class {τ : Tag}
    (hH : Char2HratRank τ .exc fun r n => r = 6 ∧ n = 72) : Char2Hrat τ .exc := by
  intro L _ _ _ p₀ S a hT hap h1 i hk hq hL34
  obtain ⟨hnin, h⟩ := exc_kind hk
  rcases h with h6 | ⟨h4, h24, -⟩
  · exact hH L p₀ S a hT hap h1 i hk h6 hq hL34
  · exfalso
    have hTp : rootDiagUnit τ a ^ 3 = 1 := rootDiagUnit_pow_eq_one_of_forall hap
    exact not_isLThreeFour_d4class S hT hTp h1 i h4 h24 hnin hL34

end Kinds

end Up34Exc

end CFSG.HardMathSupport.Dickson.Sec6
