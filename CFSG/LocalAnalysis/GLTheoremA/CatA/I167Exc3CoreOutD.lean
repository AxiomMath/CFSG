module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I167Exc3CoreOutDefs
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I167ExcRecA
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I167ExcRecD4
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I167ExcRecDTwo

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I167

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S10
open CFSG.Assembly (LargeEvenInduces)
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups


theorem exc3core_out_D4 {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] [CharP L 2]
    (SL : LangSetup τ L 5) {a : Fin τ.rank → Lˣ} (hT : rootDiagUnit τ a ∈ SL.D.torus)
    (hap : ∀ m, a m ^ 3 = 1) (ha1 : rootDiagUnit τ a ≠ 1) (i : KernelComponent (rootCharHom a))
    (hr : compRank (componentRoots (rootCharHom a) i) = 4)
    (hc : (componentRoots (rootCharHom a) i).ncard = 24) :
    exc3core_Out (↥(rationalComponent SL.ρ SL.Γ (rootCharHom a) i) ⧸
      Subgroup.center ↥(rationalComponent SL.ρ SL.Γ (rootCharHom a) i)) := by
  by_cases hin : twistInner (componentRoots (rootCharHom a) i)
      ((SL.ρ : (Fin τ.rank → ℤ) → (Fin τ.rank → ℤ))^[componentOrbitLength SL.ρ
        (componentRoots (rootCharHom a) i)])
  · obtain ⟨f, -, -, hm⟩ := excRec_D4_inner SL Nat.prime_three hT hap ha1 i hr hc hin
    exact ⟨.POmegaPlus, 4, f,
      excRec_lieModel_two (by simp [CFSG.Blueprint.classicalTags]) hm, by decide⟩
  · obtain ⟨f, -, hm | hm⟩ := excRec_D4_outer SL Nat.prime_three hT hap ha1 i hr hc hin
    · rw [ringChar.eq L 2] at hm
      exact ⟨.POmegaMinus, 4, f, hm, by decide⟩
    · rw [ringChar.eq L 2] at hm
      exact ⟨.trialityD4, 0, f, hm, by decide⟩


theorem exc3core_out_D6_inner {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] [CharP L 2]
    (SL : LangSetup τ L 5) {a : Fin τ.rank → Lˣ} (hT : rootDiagUnit τ a ∈ SL.D.torus)
    (hap : ∀ m, a m ^ 3 = 1) (ha1 : rootDiagUnit τ a ≠ 1) (i : KernelComponent (rootCharHom a))
    (hr : compRank (componentRoots (rootCharHom a) i) = 6)
    (hn : (componentRoots (rootCharHom a) i).ncard = 60)
    (hinner : twistInner (componentRoots (rootCharHom a) i)
      ((SL.ρ : (Fin τ.rank → ℤ) → (Fin τ.rank → ℤ))^[componentOrbitLength SL.ρ
        (componentRoots (rootCharHom a) i)])) :
    exc3core_Out (↥(rationalComponent SL.ρ SL.Γ (rootCharHom a) i) ⧸
      Subgroup.center ↥(rationalComponent SL.ρ SL.Γ (rootCharHom a) i)) := by
  obtain ⟨f, -, -, hm⟩ :=
    excRec_dInnerAll SL Nat.prime_three hT hap ha1 i (by omega) (by rw [hn, hr]) hinner
  exact ⟨.POmegaPlus, compRank (componentRoots (rootCharHom a) i), f,
    excRec_lieModel_two (by simp [CFSG.Blueprint.classicalTags]) hm, by rw [hr]; decide⟩


theorem exc3core_out_twoD {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] [CharP L 2]
    (SL : LangSetup τ L 5) {a : Fin τ.rank → Lˣ} (hT : rootDiagUnit τ a ∈ SL.D.torus)
    (hap : ∀ m, a m ^ 3 = 1) (ha1 : rootDiagUnit τ a ≠ 1) (i : KernelComponent (rootCharHom a))
    (hA : (compRank (componentRoots (rootCharHom a) i) = 5 ∧
        (componentRoots (rootCharHom a) i).ncard = 40) ∨
      (compRank (componentRoots (rootCharHom a) i) = 7 ∧
        (componentRoots (rootCharHom a) i).ncard = 84))
    (hout : ¬ twistInner (componentRoots (rootCharHom a) i)
      ((SL.ρ : (Fin τ.rank → ℤ) → (Fin τ.rank → ℤ))^[componentOrbitLength SL.ρ
        (componentRoots (rootCharHom a) i)])) :
    exc3core_Out (↥(rationalComponent SL.ρ SL.Γ (rootCharHom a) i) ⧸
      Subgroup.center ↥(rationalComponent SL.ρ SL.Γ (rootCharHom a) i)) := by
  have h5 : 5 ≤ compRank (componentRoots (rootCharHom a) i) := by
    rcases hA with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> simp [h1, h2]
  have hn : (componentRoots (rootCharHom a) i).ncard =
      2 * compRank (componentRoots (rootCharHom a) i) *
        (compRank (componentRoots (rootCharHom a) i) - 1) := by
    rcases hA with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> simp [h1, h2]
  obtain ⟨e, -, hm⟩ := excRec_twoD SL Nat.prime_three hT hap ha1 i h5 hn hout
  rw [ringChar.eq L 2] at hm
  exact ⟨.POmegaMinus, compRank (componentRoots (rootCharHom a) i), e, hm,
    by rcases hA with ⟨h1, -⟩ | ⟨h1, -⟩ <;> rw [h1] <;> decide⟩



end CFSG.LocalAnalysis.GLTheoremA.I167

end
