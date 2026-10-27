module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieCompIdxExc2
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieCompIdxEnnolaRatDefs

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie
namespace ExcUntw

section

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Minuscule MinData.Valid CFSG.LieType.Steinberg.TwistedE6
  CFSG.LieType.Steinberg.Isogeny CFSG.LieType.CurtisTits CFSG.Assembly.LowTwoRank
  CFSG.ComponentClassification.CatLeaf CFSG.ComponentClassification.CatLeafProof
  CFSG.Adapters.RankTwoModelTransports CFSG.HardMathSupport.Solomon.Coordinator.LieComp
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.RankThree.PartOne.KE CFSG.Timmesfeld CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
  CFSG.RankThree.PartOne.KE6 CFSG.RankThree.PartOne.KD4T CFSG.ComponentClassification.CatLeafProof
  CFSG.HardMathSupport.Timmesfeld.RootAut CFSG.RankThree.Lattice
open scoped MatrixGroups Matrix

theorem ratCatExp_of_outer_E7
    {L : Type} [Field L] [IsAlgClosed L] {p₀ p : ℕ}
    (S : LangSetup Tag.E7 L p₀) (hp : p.Prime) (hpL : (p : L) ≠ 0)
    {a : Fin Tag.E7.rank → Lˣ} (hTor : rootDiagUnit Tag.E7 a ∈ S.D.torus)
    (hTp : rootDiagUnit Tag.E7 a ^ p = 1) (i : KernelComponent (rootCharHom a))
    (h6 : 6 ≤ compRank (componentRoots (rootCharHom a) i))
    (hn : (componentRoots (rootCharHom a) i).ncard =
      eRootCount (compRank (componentRoots (rootCharHom a) i)))
    (hout : ¬ twistInner (componentRoots (rootCharHom a) i)
      ((S.ρ : (Fin Tag.E7.rank → ℤ) → _)^[componentOrbitLength S.ρ
        (componentRoots (rootCharHom a) i)])) :
    RationalCatalogueExp S i := by
  obtain ⟨f, hf, hq, hlie⟩ :=
    lieModel_rationalComponent_of_outer_E7 S hp hpL hTor hTp i h6 hn hout
  refine ⟨1, Or.inr rfl, ?_⟩
  rw [pow_one, ← hq]
  exact catalogueOver_of_lieModel_twistedE6 hlie

theorem ratCatExp_of_outer_E8
    {L : Type} [Field L] [IsAlgClosed L] {p₀ p : ℕ}
    (S : LangSetup Tag.E8 L p₀) (hp : p.Prime) (hpL : (p : L) ≠ 0)
    {a : Fin Tag.E8.rank → Lˣ} (hTor : rootDiagUnit Tag.E8 a ∈ S.D.torus)
    (hTp : rootDiagUnit Tag.E8 a ^ p = 1) (i : KernelComponent (rootCharHom a))
    (h6 : 6 ≤ compRank (componentRoots (rootCharHom a) i))
    (hn : (componentRoots (rootCharHom a) i).ncard =
      eRootCount (compRank (componentRoots (rootCharHom a) i)))
    (hout : ¬ twistInner (componentRoots (rootCharHom a) i)
      ((S.ρ : (Fin Tag.E8.rank → ℤ) → _)^[componentOrbitLength S.ρ
        (componentRoots (rootCharHom a) i)])) :
    RationalCatalogueExp S i := by
  obtain ⟨f, hf, hq, hlie⟩ :=
    lieModel_rationalComponent_of_outer_E8 S hp hpL hTor hTp i h6 hn hout
  refine ⟨1, Or.inr rfl, ?_⟩
  rw [pow_one, ← hq]
  exact catalogueOver_of_lieModel_twistedE6 hlie

theorem excUntwOuterECatalogueExp_holds
    : ∀ (τ : Tag), (τ = .E7 ∨ τ = .E8) → ExcUntwOuterECatalogueExpAt τ := by
  intro τ hτ L _ _ p₀ S p hp hp2 a hT hap h1 i h6 hn hout
  have hℓp : ringChar L ≠ p := ringChar_ne_of_pow_eq_one hp hap h1
  have hpL : ((p : ℕ) : L) ≠ 0 := natCast_ne_zero_of_ringChar_ne hp hℓp
  have hTp := rootDiagUnit_pow_eq_one_of_forall hap
  rcases hτ with rfl | rfl
  · exact ratCatExp_of_outer_E7 S hp hpL hT hTp i h6 hn hout
  · exact ratCatExp_of_outer_E8 S hp hpL hT hTp i h6 hn hout

end

end ExcUntw
end CFSG.LocalAnalysis.GLTheoremA.KD264Lie

end
