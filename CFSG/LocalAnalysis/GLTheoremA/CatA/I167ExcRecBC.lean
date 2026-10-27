module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.L154NonCfgF4

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I167

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp CFSG.LieType.Steinberg.Adjoint
  CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
  CFSG.RankThree.PartOne.KE CFSG.Timmesfeld
  CFSG.LocalAnalysis.GLTheoremA.K155X
open scoped MatrixGroups Matrix

set_option linter.unusedSectionVars false


section BC

theorem excRec_F4_B3C3 {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] {p₀ : ℕ}
    (S : LangSetup Tag.F4 L p₀) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {a : Fin Tag.F4.rank → Lˣ} (hT : rootDiagUnit Tag.F4 a ∈ S.D.torus)
    (hap : ∀ m, a m ^ p = 1) (ha1 : rootDiagUnit Tag.F4 a ≠ 1)
    (i : KernelComponent (rootCharHom a))
    (hr : compRank (componentRoots (rootCharHom a) i) = 3)
    (hc : (componentRoots (rootCharHom a) i).ncard = 18)
    (hinner : twistInner (componentRoots (rootCharHom a) i)
      ((S.ρ : (Fin Tag.F4.rank → ℤ) → _)^[componentOrbitLength S.ρ
        (componentRoots (rootCharHom a) i)])) :
    ∃ f, 1 ≤ f ∧
      ringChar L ^ f = S.D.q ^ componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) ∧
      StatedClassicalModel (↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸
        Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)) .PSp 3 (ringChar L) f := by
  classical
  have hp2' : p % 2 = 1 := (hp.eq_two_or_odd).resolve_left hp2
  have hℓp : ringChar L ≠ p := ringChar_ne_of_pow_eq_one hp hap ha1
  have hpL : ((p : ℕ) : L) ≠ 0 := natCast_ne_zero_of_ringChar_ne hp hℓp
  have hTp := rootDiagUnit_pow_eq_one_of_forall hap
  have hnonA : ¬ (1 ≤ compRank (componentRoots (rootCharHom a) i) ∧
      (componentRoots (rootCharHom a) i).ncard = compRank (componentRoots (rootCharHom a) i) *
        (compRank (componentRoots (rootCharHom a) i) + 1)) := by
    rintro ⟨-, hn⟩
    rw [hr, hc] at hn
    omega
  rcases f4_nonA_casesP2 hp hp2' S hpL hTp ha1 i hnonA with ⟨v, -, hr2, -⟩ |
      ⟨v, J, hJ, hroots, -, -⟩
  · omega
  obtain ⟨K, hfin, hcard, g, hg, hker⟩ := l154f4_exists_spSurj S hT i hinner (m := 3)
    (fun K hfin hK => by
      haveI := hfin
      obtain ⟨hch, f, hf, hKf, hadm, -⟩ :=
        l154f4_subfield_params K (m := 3) (by norm_num) hK (fun h => absurd h (by norm_num))
      haveI := hch
      refine ⟨Group.isPerfect_def.mp
        (CFSG.LieType.Universal.Symplectic.isQuasisimple_of_admissible 3 ↥K hadm hKf).1, ?_⟩
      obtain ⟨Ψ, hΨk, hΨr⟩ := l154f4_cover_levi hJ hf hKf
      obtain ⟨Ψ', hk', hr'⟩ := l154f4_spRange_smul v hΨk hΨr
      refine ⟨Ψ', hk', ?_⟩
      rw [hr']
      show _ = rootSpan Tag.F4 ↥K (componentRoots (rootCharHom a) i)
      rw [hroots])
  haveI := hfin
  obtain ⟨-, f, hf, hKf, hadm, -⟩ :=
    l154f4_subfield_params K (m := 3) (by norm_num) hcard (fun h => absurd h (by norm_num))
  have hperf : commutator (StatedSp 3 ↥K) = ⊤ := Group.isPerfect_def.mp
    (CFSG.LieType.Universal.Symplectic.isQuasisimple_of_admissible 3 ↥K hadm hKf).1
  obtain ⟨e⟩ := nonempty_centralQuotient_mulEquiv hperf g hg hker
  rw [ringChar.eq L 2]
  exact ⟨f, hf, by rw [← hcard, hKf], hadm, ↥K, inferInstance, inferInstance, hKf,
    ⟨e.symm.trans (CFSG.LieType.Universal.Symplectic.centerQuotientEquiv 3 ↥K)⟩⟩

end BC

end CFSG.LocalAnalysis.GLTheoremA.I167

end
