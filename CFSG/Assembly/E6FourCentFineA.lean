module

public import CFSG.Assembly.E6FourCentFineACover
public import CFSG.Assembly.E6FourCoverQuot
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GCenterQuot

public section

namespace CFSG.Assembly

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Timmesfeld.LangTorus



theorem e6Four_A5_fine {L : Type} [Field L] [IsAlgClosed L] (S : LangSetup Tag.E6 L 5)
    (hq : S.D.q = 4) {a : Fin Tag.E6.rank → Lˣ} (hT : rootDiagUnit Tag.E6 a ∈ S.D.torus)
    (hap : ∀ j, a j ^ 5 = 1) (h1 : rootDiagUnit Tag.E6 a ≠ 1)
    (i : KernelComponent (rootCharHom a))
    (hr : compRank (componentRoots (rootCharHom a) i) = 5)
    (hn : (componentRoots (rootCharHom a) i).ncard = 30)
    (hs : componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) = 1)
    (hin : twistInner (componentRoots (rootCharHom a) i)
      ((S.ρ : (Fin Tag.E6.rank → ℤ) → _))) :
    LieModel (↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸
      Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)) .PSL 6 2 2 := by
  obtain ⟨K, _, _, g, hK, hg, hker⟩ := e6Four_A5_cover S hq hT hap h1 i hr hn hs hin
  have hperf : commutator (Matrix.SpecialLinearGroup (Fin 6) K) = ⊤ :=
    (CFSG.LinearGroups.special_linear_dimension_at_least_three_perfect (K := K)
      (by norm_num)).commutator_eq_top
  obtain ⟨-, ⟨e⟩⟩ := e6Four_cover_quot g hg hker hperf
  obtain ⟨e2⟩ := CFSG.LocalAnalysis.GLTheoremA.Y10GCenterQuot.nonempty_centerQuot_sl (E := K) 6
    (MulEquiv.refl (Matrix.SpecialLinearGroup (Fin 6) K))
  refine Or.inl ⟨by simp [classicalTags], ⟨?_, K, inferInstance, inferInstance, by rw [hK]; norm_num,
    ⟨e.symm.trans e2⟩⟩⟩
  exact ⟨Nat.prime_two, by norm_num, by norm_num, by decide, by decide⟩

end CFSG.Assembly

end
