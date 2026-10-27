module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I167Exc3CoreOutDefs
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I167ExcRecA
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I167ExcRecBC
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I167ExcRecE

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I167

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S10
open CFSG.Assembly (LargeEvenInduces)
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups


theorem exc3core_out_F4_B3C3 {L : Type} [Field L] [IsAlgClosed L] [CharP L 2]
    (SL : LangSetup Tag.F4 L 5) {a : Fin Tag.F4.rank → Lˣ} (hT : rootDiagUnit Tag.F4 a ∈ SL.D.torus)
    (hap : ∀ m, a m ^ 3 = 1) (ha1 : rootDiagUnit Tag.F4 a ≠ 1) (i : KernelComponent (rootCharHom a))
    (hr : compRank (componentRoots (rootCharHom a) i) = 3)
    (hc : (componentRoots (rootCharHom a) i).ncard = 18)
    (hinner : twistInner (componentRoots (rootCharHom a) i)
      ((SL.ρ : (Fin Tag.F4.rank → ℤ) → (Fin Tag.F4.rank → ℤ))^[componentOrbitLength SL.ρ
        (componentRoots (rootCharHom a) i)])) :
    exc3core_Out (↥(rationalComponent SL.ρ SL.Γ (rootCharHom a) i) ⧸
      Subgroup.center ↥(rationalComponent SL.ρ SL.Γ (rootCharHom a) i)) := by
  obtain ⟨f, -, -, hm⟩ :=
    excRec_F4_B3C3 SL Nat.prime_three (by norm_num) hT hap ha1 i hr hc hinner
  exact ⟨.PSp, 3, f, excRec_lieModel_two (by simp [CFSG.Blueprint.classicalTags]) hm,
    by decide⟩


theorem exc3core_out_E6 {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] [CharP L 2]
    (SL : LangSetup τ L 5) {a : Fin τ.rank → Lˣ} (hT : rootDiagUnit τ a ∈ SL.D.torus)
    (hap : ∀ m, a m ^ 3 = 1) (ha1 : rootDiagUnit τ a ≠ 1) (i : KernelComponent (rootCharHom a))
    (hr : compRank (componentRoots (rootCharHom a) i) = 6)
    (hc : (componentRoots (rootCharHom a) i).ncard = 72)
    (hout : ¬ twistInner (componentRoots (rootCharHom a) i)
      ((SL.ρ : (Fin τ.rank → ℤ) → (Fin τ.rank → ℤ))^[componentOrbitLength SL.ρ
        (componentRoots (rootCharHom a) i)])) :
    exc3core_Out (↥(rationalComponent SL.ρ SL.Γ (rootCharHom a) i) ⧸
      Subgroup.center ↥(rationalComponent SL.ρ SL.Γ (rootCharHom a) i)) := by
  obtain ⟨f, -, -, hm⟩ := excRec_E6_outer SL Nat.prime_three hT hap ha1 i hr hc hout
  rw [ringChar.eq L 2] at hm
  exact ⟨.twistedE6, 0, f, hm, by simp⟩


theorem exc3core_out_E7 {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] [CharP L 2]
    (SL : LangSetup τ L 5) {a : Fin τ.rank → Lˣ} (hT : rootDiagUnit τ a ∈ SL.D.torus)
    (hap : ∀ m, a m ^ 3 = 1) (ha1 : rootDiagUnit τ a ≠ 1) (i : KernelComponent (rootCharHom a))
    (hr : compRank (componentRoots (rootCharHom a) i) = 7)
    (hn : (componentRoots (rootCharHom a) i).ncard = 126)
    (hinner : twistInner (componentRoots (rootCharHom a) i)
      ((SL.ρ : (Fin τ.rank → ℤ) → (Fin τ.rank → ℤ))^[componentOrbitLength SL.ρ
        (componentRoots (rootCharHom a) i)])) :
    exc3core_Out (↥(rationalComponent SL.ρ SL.Γ (rootCharHom a) i) ⧸
      Subgroup.center ↥(rationalComponent SL.ρ SL.Γ (rootCharHom a) i)) := by
  obtain ⟨f, -, -, hm⟩ := excRec_E7_inner SL Nat.prime_three hT hap ha1 i hr hn hinner
  rw [ringChar.eq L 2] at hm
  exact ⟨.E7, 0, f, hm, by simp⟩



end CFSG.LocalAnalysis.GLTheoremA.I167

end
