module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.L154NonCfgE7

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I167

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp CFSG.LieType.Steinberg.Adjoint
  CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
  CFSG.RankThree.PartOne.KE CFSG.Timmesfeld
  CFSG.LocalAnalysis.GLTheoremA.K155X
  CFSG.LocalAnalysis.GLTheoremA.KD264Lie.ExcUntw
open scoped MatrixGroups Matrix

set_option linter.unusedSectionVars false


section E

variable {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ}

theorem excRec_E6_outer (S : LangSetup τ L p₀) {p : ℕ} (hp : p.Prime) {a : Fin τ.rank → Lˣ}
    (hT : rootDiagUnit τ a ∈ S.D.torus) (hap : ∀ m, a m ^ p = 1) (ha1 : rootDiagUnit τ a ≠ 1)
    (i : KernelComponent (rootCharHom a))
    (hr : compRank (componentRoots (rootCharHom a) i) = 6)
    (hc : (componentRoots (rootCharHom a) i).ncard = 72)
    (hout : ¬ twistInner (componentRoots (rootCharHom a) i)
      ((S.ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength S.ρ (componentRoots (rootCharHom a) i)])) :
    ∃ f, 0 < f ∧ ringChar L ^ f = S.D.q ∧
      CFSG.Blueprint.LieModel (↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸
        Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)) .twistedE6 0
        (ringChar L) f := by
  classical
  have hℓp : ringChar L ≠ p := ringChar_ne_of_pow_eq_one hp hap ha1
  have hTp := rootDiagUnit_pow_eq_one_of_forall hap
  have hpL : ((p : ℕ) : L) ≠ 0 := natCast_ne_zero_of_ringChar_ne hp hℓp
  have hn : (componentRoots (rootCharHom a) i).ncard =
      eRootCount (compRank (componentRoots (rootCharHom a) i)) := by
    rw [hc, hr]
    rfl
  have hle := compRank_le_rank (componentRoots (rootCharHom a) i)
  rw [hr] at hle
  cases τ with
  | G2 => exact absurd hle (by decide)
  | F4 => exact absurd hle (by decide)
  | D4 => exact absurd hle (by decide)
  | E6 => exact absurd (rootDiagUnit_eq_one_of_ncard i (by rw [hc]; rfl)) ha1
  | E7 => exact lieModel_rationalComponent_of_outer_E7 S hp hpL hT hTp i (by omega) hn hout
  | E8 => exact lieModel_rationalComponent_of_outer_E8 S hp hpL hT hTp i (by omega) hn hout

theorem excRec_E7_inner (S : LangSetup τ L p₀) {p : ℕ} (hp : p.Prime) {a : Fin τ.rank → Lˣ}
    (hT : rootDiagUnit τ a ∈ S.D.torus) (hap : ∀ m, a m ^ p = 1) (ha1 : rootDiagUnit τ a ≠ 1)
    (i : KernelComponent (rootCharHom a))
    (h7 : compRank (componentRoots (rootCharHom a) i) = 7)
    (hn : (componentRoots (rootCharHom a) i).ncard = 126)
    (hinner : twistInner (componentRoots (rootCharHom a) i)
      ((S.ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength S.ρ (componentRoots (rootCharHom a) i)])) :
    ∃ f, 1 ≤ f ∧
      ringChar L ^ f = S.D.q ^ componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) ∧
      CFSG.Blueprint.LieModel (↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸
        Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)) .E7 0 (ringChar L) f := by
  classical
  have hℓp : ringChar L ≠ p := ringChar_ne_of_pow_eq_one hp hap ha1
  have hTp := rootDiagUnit_pow_eq_one_of_forall hap
  have hpL : ((p : ℕ) : L) ≠ 0 := natCast_ne_zero_of_ringChar_ne hp hℓp
  have hle := compRank_le_rank (componentRoots (rootCharHom a) i)
  rw [h7] at hle
  cases τ with
  | G2 => exact absurd hle (by decide)
  | F4 => exact absurd hle (by decide)
  | D4 => exact absurd hle (by decide)
  | E6 => exact absurd hle (by decide)
  | E7 => exact absurd (rootDiagUnit_eq_one_of_ncard i (by rw [hn]; rfl)) ha1
  | E8 =>
    have hn' : (componentRoots (rootCharHom a) i).ncard =
        eRootCount (compRank (componentRoots (rootCharHom a) i)) := by
      rw [hn, h7]
      rfl
    obtain ⟨v, n, l, -, -, hrk, hroots, hnon, hE⟩ :=
      l154_exists_tree_of_class_rank kacE8 facts_E8 e8_tree e8_adj e8_check e8_lt e8_card edgeE 6
        eRootCount e8_ecount e8_etrees (fun n => n = 6 ∨ n = 7 ∨ n = 8) e8_elen S hp hpL hTp i
        (by omega) hn'
    have hn7 : n = 7 := by rw [← hrk, h7]
    subst hn7
    obtain ⟨r, e, hr, hchar, he, hq⟩ := exists_char_pow S
    obtain ⟨hs0, -, -⟩ := outer_componentOrbitLength_spec S hT i
    have hroots' : componentRoots (rootCharHom a) i =
        rootsOfFam (fun x => v • kacE8.extRoot x) (Set.range l) := by
      rw [hroots, l154_smul_image_rootsOf_eq]
    have hmodel := l154_rationalComponent_e7Model S (Or.inr (Or.inr (Or.inr rfl))) hT i hinner
      (fun x => v • kacE8.extRoot x) (fun b => IsRoot.smul (kacE8.isRoot_extRoot b) v) l hroots'
      (fun c d hcd h1 h2 => by
        show iform (v • kacE8.extRoot (l c)) (v • kacE8.extRoot (l d)) = 0
        rw [iform_smul]
        exact hnon c d hcd h1 h2)
      (fun {F} _ c d hcd =>
        treeFrames kacE8 (fun {F} _ x y h => e8_frames x y h) v l (edgeE 7) hE (F := F) c d hcd)
      hr he hq
    exact ⟨e * componentOrbitLength S.ρ (componentRoots (rootCharHom a) i), Nat.mul_pos he hs0,
      by rw [ringChar.eq L r, hq, pow_mul], by rw [ringChar.eq L r]; exact hmodel⟩

end E

end CFSG.LocalAnalysis.GLTheoremA.I167

end
