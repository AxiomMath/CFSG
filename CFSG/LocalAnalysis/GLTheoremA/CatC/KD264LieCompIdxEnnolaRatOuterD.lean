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
  CFSG.RankThree.PartOne.KE CFSG.ClassicalInvolution.WeakCT CFSG.Timmesfeld
  CFSG.HardMathSupport.Timmesfeld.RootAut CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp.CompsPTwoDMain
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp.CompsPTwoDRecog
open scoped MatrixGroups Matrix

theorem ratCatExp_of_twoD_highG
    {p : ℕ} (hp : p.Prime) {τ : Tag} {L : Type} [Field L]
    [IsAlgClosed L] {p₀ : ℕ} (S : LangSetup τ L p₀) {a : Fin τ.rank → Lˣ}
    (hT : rootDiagUnit τ a ∈ S.D.torus) (hap : ∀ i, a i ^ p = 1) (h1 : rootDiagUnit τ a ≠ 1)
    (i : KernelComponent (rootCharHom a))
    (h5 : 5 ≤ compRank (componentRoots (rootCharHom a) i))
    (hn : (componentRoots (rootCharHom a) i).ncard =
      2 * compRank (componentRoots (rootCharHom a) i) *
        (compRank (componentRoots (rootCharHom a) i) - 1))
    (hout : ¬ twistInner (componentRoots (rootCharHom a) i)
      ((S.ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength S.ρ
        (componentRoots (rootCharHom a) i)]))
    (Q : ℕ → ℕ → Prop) (hrec : CompsPTwoDRecog.TwoDChainRecogAll L Q)
    (hQ : Q (ringChar L) S.D.q) :
    RationalCatalogueExp S i := by
  obtain ⟨m, e, hq, hlie⟩ :=
    lieModel_rationalComponent_of_twoD_highG hp S hT hap h1 i h5 hn hout Q hrec hQ
  refine ⟨1, Or.inr rfl, ?_⟩
  rw [pow_one, ← hq]
  exact catalogueOver_of_lieModel_pominus hlie

end

end ExcUntw
end CFSG.LocalAnalysis.GLTheoremA.KD264Lie

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie
namespace ExcUntw

section

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley
  CFSG.RankThree.PartOne.KD4T CFSG.RankThree.PartOne.KE CFSG.RankThree.PartOne.KD4L
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.Yardstones.Md0ec50421ce4
  CFSG.RankThree.PartOne.KE6 CFSG.HardMathSupport.Solomon.Coordinator.LieComp
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp.CompsPD4Layers
  CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
  CFSG.ComponentClassification.CatLeafProof
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped Matrix MatrixGroups

theorem ratCatExp_of_rank_four_all
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p₀ p : ℕ}
    (S : LangSetup τ L p₀) (hp : p.Prime) (hpL : (p : L) ≠ 0) {a : Fin τ.rank → Lˣ}
    (hT : rootDiagUnit τ a ∈ S.D.torus) (hTp : rootDiagUnit τ a ^ p = 1)
    (ha1 : rootDiagUnit τ a ≠ 1) (i : KernelComponent (rootCharHom a))
    (hr : compRank (componentRoots (rootCharHom a) i) = 4)
    (hc : (componentRoots (rootCharHom a) i).ncard = 24)
    (hnin : ¬ twistInner (componentRoots (rootCharHom a) i)
      ((S.ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength S.ρ
        (componentRoots (rootCharHom a) i)])) :
    RationalCatalogueExp S i :=
  ⟨1, Or.inr rfl, by
    rw [pow_one]
    exact catalogueOver_of_rank_four_all S hp hpL hT hTp ha1 i hr hc hnin⟩

theorem ratCatExp_of_outerD_all
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ}
    (S : LangSetup τ L p₀) {p : ℕ} (hp : p.Prime) {a : Fin τ.rank → Lˣ}
    (hT : rootDiagUnit τ a ∈ S.D.torus) (hap : ∀ i, a i ^ p = 1) (h1 : rootDiagUnit τ a ≠ 1)
    (i : KernelComponent (rootCharHom a))
    (hshape : 4 ≤ compRank (componentRoots (rootCharHom a) i) ∧
      (componentRoots (rootCharHom a) i).ncard =
        2 * compRank (componentRoots (rootCharHom a) i) *
          (compRank (componentRoots (rootCharHom a) i) - 1))
    (hout : ¬ twistInner (componentRoots (rootCharHom a) i)
      ((S.ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength S.ρ
        (componentRoots (rootCharHom a) i)])) :
    RationalCatalogueExp S i := by
  by_cases h5 : 5 ≤ compRank (componentRoots (rootCharHom a) i)
  · exact ratCatExp_of_twoD_highG hp S hT hap h1 i h5 hshape.2 hout (fun _ _ => True)
      (fun r _ _ e m he hm5 _ => CompsPTwoDChainO.twoDChainRecog_all he (by omega)) trivial
  · have hr4 : compRank (componentRoots (rootCharHom a) i) = 4 := by omega
    have hc : (componentRoots (rootCharHom a) i).ncard = 24 := by
      rw [hshape.2, hr4]
    have hℓp : ringChar L ≠ p := ringChar_ne_of_pow_eq_one hp hap h1
    have hpL : ((p : ℕ) : L) ≠ 0 := natCast_ne_zero_of_ringChar_ne hp hℓp
    have hTp := rootDiagUnit_pow_eq_one_of_forall hap
    exact ratCatExp_of_rank_four_all S hp hpL hT hTp h1 i hr4 hc hout

theorem excUntwOuterDCatalogueExp_holds
    : ∀ (τ : Tag), (τ = .E6 ∨ τ = .E7 ∨ τ = .E8) → ExcUntwOuterDCatalogueExpAt τ := by
  intro τ _ L _ _ p₀ S _ p hp _ a hT hap h1 i hshape hout _
  exact ratCatExp_of_outerD_all S hp hT hap h1 i hshape hout

end

end ExcUntw
end CFSG.LocalAnalysis.GLTheoremA.KD264Lie

end
