module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I167Exc3CoreOutDefs
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I167ExcRecA

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I167

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S10
open CFSG.Assembly (LargeEvenInduces)
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups


theorem exc3core_out_typeA_inner {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] [CharP L 2]
    (SL : LangSetup τ L 5) {a : Fin τ.rank → Lˣ} (hT : rootDiagUnit τ a ∈ SL.D.torus)
    (hap : ∀ m, a m ^ 3 = 1) (ha1 : rootDiagUnit τ a ≠ 1) (i : KernelComponent (rootCharHom a))
    (hA : (compRank (componentRoots (rootCharHom a) i) = 1 ∧
        (componentRoots (rootCharHom a) i).ncard = 2) ∨
      (compRank (componentRoots (rootCharHom a) i) = 2 ∧
        (componentRoots (rootCharHom a) i).ncard = 6) ∨
      (compRank (componentRoots (rootCharHom a) i) = 5 ∧
        (componentRoots (rootCharHom a) i).ncard = 30))
    (hinner : twistInner (componentRoots (rootCharHom a) i)
      ((SL.ρ : (Fin τ.rank → ℤ) → (Fin τ.rank → ℤ))^[componentOrbitLength SL.ρ
        (componentRoots (rootCharHom a) i)]))
    (hqs : CFSG.IsQuasisimple ↥(rationalComponent SL.ρ SL.Γ (rootCharHom a) i)) :
    exc3core_Out (↥(rationalComponent SL.ρ SL.Γ (rootCharHom a) i) ⧸
      Subgroup.center ↥(rationalComponent SL.ρ SL.Γ (rootCharHom a) i)) := by
  have hA' : 1 ≤ compRank (componentRoots (rootCharHom a) i) ∧
      (componentRoots (rootCharHom a) i).ncard =
        compRank (componentRoots (rootCharHom a) i) *
          (compRank (componentRoots (rootCharHom a) i) + 1) := by
    rcases hA with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> simp [h1, h2]
  obtain ⟨f, -, -, hm⟩ :=
    excRec_typeA_inner SL Nat.prime_three hT hap ha1 i hA' hinner hqs
  refine ⟨.PSL, compRank (componentRoots (rootCharHom a) i) + 1, f,
    excRec_lieModel_two (by simp [CFSG.Blueprint.classicalTags]) hm, ?_⟩
  rcases hA with ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ <;> rw [h1] <;> decide


theorem exc3core_out_typeA_suN {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] [CharP L 2]
    (SL : LangSetup τ L 5) {a : Fin τ.rank → Lˣ} (hT : rootDiagUnit τ a ∈ SL.D.torus)
    (hap : ∀ m, a m ^ 3 = 1) (ha1 : rootDiagUnit τ a ≠ 1) (i : KernelComponent (rootCharHom a))
    (hA : 2 ≤ compRank (componentRoots (rootCharHom a) i) ∧
      (componentRoots (rootCharHom a) i).ncard = compRank (componentRoots (rootCharHom a) i) *
        (compRank (componentRoots (rootCharHom a) i) + 1))
    (hout : ¬ twistInner (componentRoots (rootCharHom a) i)
      ((SL.ρ : (Fin τ.rank → ℤ) → (Fin τ.rank → ℤ))^[componentOrbitLength SL.ρ
        (componentRoots (rootCharHom a) i)]))
    (hqs : CFSG.IsQuasisimple ↥(rationalComponent SL.ρ SL.Γ (rootCharHom a) i)) :
    exc3core_Out (↥(rationalComponent SL.ρ SL.Γ (rootCharHom a) i) ⧸
      Subgroup.center ↥(rationalComponent SL.ρ SL.Γ (rootCharHom a) i)) := by
  obtain ⟨f, -, -, hm⟩ :=
    excRec_typeA_suN SL Nat.prime_three hT hap ha1 i hA hout hqs
  refine ⟨.PSU, compRank (componentRoots (rootCharHom a) i) + 1, f,
    excRec_lieModel_two (by simp [CFSG.Blueprint.classicalTags]) hm, ?_⟩
  rintro (⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩) <;> exact absurd h (by decide)



end CFSG.LocalAnalysis.GLTheoremA.I167

end
