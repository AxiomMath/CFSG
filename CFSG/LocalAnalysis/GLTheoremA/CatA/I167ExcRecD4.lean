module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I167ExcRecD
public import CFSG.LocalAnalysis.GLTheoremA.CatA.L154NonCfgRank4

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I167

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp CFSG.LieType.Steinberg.Adjoint
  CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
  CFSG.RankThree.PartOne.KE CFSG.Timmesfeld
open scoped MatrixGroups Matrix

set_option linter.unusedSectionVars false


section D4

variable {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ}

theorem excRec_dInnerAll (S : LangSetup τ L p₀) {p : ℕ} (hp : p.Prime) {a : Fin τ.rank → Lˣ}
    (hT : rootDiagUnit τ a ∈ S.D.torus) (hap : ∀ m, a m ^ p = 1) (ha1 : rootDiagUnit τ a ≠ 1)
    (i : KernelComponent (rootCharHom a))
    (h4 : 4 ≤ compRank (componentRoots (rootCharHom a) i))
    (hn : (componentRoots (rootCharHom a) i).ncard =
      2 * compRank (componentRoots (rootCharHom a) i) *
        (compRank (componentRoots (rootCharHom a) i) - 1))
    (hinner : twistInner (componentRoots (rootCharHom a) i)
      ((S.ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength S.ρ (componentRoots (rootCharHom a) i)])) :
    ∃ f, 1 ≤ f ∧
      ringChar L ^ f = S.D.q ^ componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) ∧
      StatedClassicalModel (↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸
        Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)) .POmegaPlus
        (compRank (componentRoots (rootCharHom a) i)) (ringChar L) f := by
  classical
  have hℓp : ringChar L ≠ p := ringChar_ne_of_pow_eq_one hp hap ha1
  have hTp := rootDiagUnit_pow_eq_one_of_forall hap
  have hpL : ((p : ℕ) : L) ≠ 0 := natCast_ne_zero_of_ringChar_ne hp hℓp
  have hE : (τ = .E6 ∨ τ = .E7 ∨ τ = .E8) →
      ∃ f, 1 ≤ f ∧
        ringChar L ^ f = S.D.q ^ componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) ∧
        StatedClassicalModel (↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸
          Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)) .POmegaPlus
          (compRank (componentRoots (rootCharHom a) i)) (ringChar L) f := by
    intro hτ
    obtain ⟨r, e, hr', hchar, he, hq⟩ := exists_char_pow S
    obtain ⟨hs0, -, -⟩ := outer_componentOrbitLength_spec S hT i
    have hm := excRec_dInner4 hτ S hp hT hap ha1 i h4 hn hinner hr' he hq
    have hrL : ringChar L = r := ringChar.eq L r
    exact ⟨e * componentOrbitLength S.ρ (componentRoots (rootCharHom a) i),
      Nat.mul_pos he hs0, by rw [hrL, hq, pow_mul], by rw [hrL]; exact hm⟩
  have hle := compRank_le_rank (componentRoots (rootCharHom a) i)
  cases τ with
  | G2 => exact absurd (le_trans h4 hle) (by decide)
  | F4 =>
    have hr4 : compRank (componentRoots (rootCharHom a) i) = 4 :=
      le_antisymm (le_trans hle (by decide)) h4
    have hc : (componentRoots (rootCharHom a) i).ncard = 24 := by rw [hn, hr4]
    obtain ⟨v, μ, -, hpinned⟩ := S.exists_pinnedT_of_prime hp hpL facts_F4 hTp
    obtain ⟨x, C, -, -, -, hr', hc'⟩ := hpinned i
    exact absurd (hc' ▸ hc) (kacCount_F4_four C (hr' ▸ hr4))
  | D4 =>
    have hr4 : compRank (componentRoots (rootCharHom a) i) = 4 :=
      le_antisymm (le_trans hle (by decide)) h4
    exact absurd (rootDiagUnit_eq_one_of_ncard i (by rw [hn, hr4]; rfl)) ha1
  | E6 => exact hE (Or.inl rfl)
  | E7 => exact hE (Or.inr (Or.inl rfl))
  | E8 => exact hE (Or.inr (Or.inr rfl))

theorem excRec_D4_inner (S : LangSetup τ L p₀) {p : ℕ} (hp : p.Prime) {a : Fin τ.rank → Lˣ}
    (hT : rootDiagUnit τ a ∈ S.D.torus) (hap : ∀ m, a m ^ p = 1) (ha1 : rootDiagUnit τ a ≠ 1)
    (i : KernelComponent (rootCharHom a))
    (hr : compRank (componentRoots (rootCharHom a) i) = 4)
    (hc : (componentRoots (rootCharHom a) i).ncard = 24)
    (hinner : twistInner (componentRoots (rootCharHom a) i)
      ((S.ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength S.ρ (componentRoots (rootCharHom a) i)])) :
    ∃ f, 1 ≤ f ∧
      ringChar L ^ f = S.D.q ^ componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) ∧
      StatedClassicalModel (↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸
        Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)) .POmegaPlus 4
        (ringChar L) f := by
  obtain ⟨f, hf1, hf, hm⟩ := excRec_dInnerAll S hp hT hap ha1 i (by omega) (by rw [hc, hr])
    hinner
  rw [hr] at hm
  exact ⟨f, hf1, hf, hm⟩

theorem excRec_D4_outer (S : LangSetup τ L p₀) {p : ℕ} (hp : p.Prime) {a : Fin τ.rank → Lˣ}
    (hT : rootDiagUnit τ a ∈ S.D.torus) (hap : ∀ m, a m ^ p = 1) (ha1 : rootDiagUnit τ a ≠ 1)
    (i : KernelComponent (rootCharHom a))
    (hr : compRank (componentRoots (rootCharHom a) i) = 4)
    (hc : (componentRoots (rootCharHom a) i).ncard = 24)
    (hout : ¬ twistInner (componentRoots (rootCharHom a) i)
      ((S.ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength S.ρ (componentRoots (rootCharHom a) i)])) :
    ∃ f, ringChar L ^ f = S.D.q ∧
      (CFSG.Blueprint.LieModel (↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸
          Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)) .POmegaMinus 4
          (ringChar L) f ∨
        CFSG.Blueprint.LieModel (↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸
          Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)) .trialityD4 0
          (ringChar L) f) := by
  have hℓp : ringChar L ≠ p := ringChar_ne_of_pow_eq_one hp hap ha1
  have hpL : ((p : ℕ) : L) ≠ 0 := natCast_ne_zero_of_ringChar_ne hp hℓp
  exact CFSG.LocalAnalysis.GLTheoremA.K155X.l154r4_of_rank_four S hp hpL hT
    (rootDiagUnit_pow_eq_one_of_forall hap) ha1 i hr hc hout

end D4

end CFSG.LocalAnalysis.GLTheoremA.I167

end
