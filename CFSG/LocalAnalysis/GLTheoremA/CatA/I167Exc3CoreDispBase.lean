module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I167Exc3CoreKind
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I167Exc3CoreK2
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I167Exc3CoreWE7
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I167Exc3CoreOutA

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I167

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S10
open CFSG.Assembly (LargeEvenInduces)
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups


theorem exc3core_inner_of_size {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] (SL : LangSetup τ L 5)
    {a : Fin τ.rank → Lˣ} (hT : rootDiagUnit τ a ∈ SL.D.torus) (i : KernelComponent (rootCharHom a))
    (h : (componentRoots (rootCharHom a) i).ncard = 2 ∨ (componentRoots (rootCharHom a) i).ncard = 18 ∨
      (componentRoots (rootCharHom a) i).ncard = 126) :
    twistInner (componentRoots (rootCharHom a) i)
      ((SL.ρ : (Fin τ.rank → ℤ) → (Fin τ.rank → ℤ))^[componentOrbitLength SL.ρ
        (componentRoots (rootCharHom a) i)]) :=
  twistInner_of_twistKind_eq_innerT SL RootAut.rootAutIsWeyl_holds hT i
    (exc3core_kind_inner_of_size SL.ρ (rootCharHom a) i h)

theorem exc3core_inner_D6 {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] (SL : LangSetup Tag.E7 L 5)
    {a : Fin Tag.E7.rank → Lˣ} (i : KernelComponent (rootCharHom a)) (w : WeylGroup Tag.E7)
    (hρ : ∀ γ, IsRoot Tag.E7 γ → SL.ρ γ = w • γ) {e : ℕ} (hq : SL.D.q = 2 ^ e) (h3 : 3 ∣ 2 ^ e + 1)
    (hT : rootDiagUnit Tag.E7 a ∈ SL.D.torus) (hap : ∀ m, a m ^ 3 = 1)
    (hn : (componentRoots (rootCharHom a) i).ncard = 60) :
    twistInner (componentRoots (rootCharHom a) i)
      ((SL.ρ : (Fin Tag.E7.rank → ℤ) → (Fin Tag.E7.rank → ℤ))^[componentOrbitLength SL.ρ
        (componentRoots (rootCharHom a) i)]) := by
  obtain ⟨hstab, hs⟩ := exc3core_orbit_one SL hq h3 hT hap i (exc3core_uniq_E7_D6 a hap i hn)
  rw [hs, Function.iterate_one]
  have hw : (fun γ => w • γ) '' componentRoots (rootCharHom a) i = componentRoots (rootCharHom a) i :=
    calc (fun γ => w • γ) '' componentRoots (rootCharHom a) i
        = (SL.ρ : (Fin Tag.E7.rank → ℤ) → (Fin Tag.E7.rank → ℤ)) '' componentRoots (rootCharHom a) i :=
          Set.image_congr fun γ hγ => (hρ γ hγ.1.1).symm
      _ = componentRoots (rootCharHom a) i := hstab
  obtain ⟨u, hu, huw⟩ := exc3core_inner_E7_D6 a hap i hn w hw
  exact ⟨u, hu, fun γ hγ => by rw [hρ γ hγ.1.1]; exact huw γ hγ⟩

theorem exc3core_out_A1 {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] [CharP L 2]
    (SL : LangSetup τ L 5) {a : Fin τ.rank → Lˣ} (hT : rootDiagUnit τ a ∈ SL.D.torus)
    (hap : ∀ m, a m ^ 3 = 1) (ha1 : rootDiagUnit τ a ≠ 1) (i : KernelComponent (rootCharHom a))
    (hr : compRank (componentRoots (rootCharHom a) i) = 1)
    (hn : (componentRoots (rootCharHom a) i).ncard = 2)
    (hqs : CFSG.IsQuasisimple ↥(rationalComponent SL.ρ SL.Γ (rootCharHom a) i)) :
    exc3core_Out (↥(rationalComponent SL.ρ SL.Γ (rootCharHom a) i) ⧸
      Subgroup.center ↥(rationalComponent SL.ρ SL.Γ (rootCharHom a) i)) :=
  exc3core_out_typeA_inner SL hT hap ha1 i (Or.inl ⟨hr, hn⟩)
    (exc3core_inner_of_size SL hT i (Or.inl hn)) hqs

theorem exc3core_out_A25 {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] [CharP L 2]
    (SL : LangSetup τ L 5) {a : Fin τ.rank → Lˣ} (hT : rootDiagUnit τ a ∈ SL.D.torus)
    (hap : ∀ m, a m ^ 3 = 1) (ha1 : rootDiagUnit τ a ≠ 1) (i : KernelComponent (rootCharHom a))
    (hA : (compRank (componentRoots (rootCharHom a) i) = 2 ∧
        (componentRoots (rootCharHom a) i).ncard = 6) ∨
      (compRank (componentRoots (rootCharHom a) i) = 5 ∧
        (componentRoots (rootCharHom a) i).ncard = 30))
    (hqs : CFSG.IsQuasisimple ↥(rationalComponent SL.ρ SL.Γ (rootCharHom a) i)) :
    exc3core_Out (↥(rationalComponent SL.ρ SL.Γ (rootCharHom a) i) ⧸
      Subgroup.center ↥(rationalComponent SL.ρ SL.Γ (rootCharHom a) i)) := by
  by_cases hin : twistInner (componentRoots (rootCharHom a) i)
      ((SL.ρ : (Fin τ.rank → ℤ) → (Fin τ.rank → ℤ))^[componentOrbitLength SL.ρ
        (componentRoots (rootCharHom a) i)])
  · refine exc3core_out_typeA_inner SL hT hap ha1 i ?_ hin hqs
    rcases hA with h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  · refine exc3core_out_typeA_suN SL hT hap ha1 i ?_ hin hqs
    rcases hA with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨by omega, by rw [h1]; omega⟩
    · exact ⟨by omega, by rw [h1]; omega⟩


end CFSG.LocalAnalysis.GLTheoremA.I167

end
