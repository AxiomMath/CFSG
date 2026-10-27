module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.K1419ExcBigGroup
public import CFSG.LocalAnalysis.GLTheoremA.CatA.K1419ExcBigTripleE
public import CFSG.LocalAnalysis.GLTheoremA.CatA.K1419ExcBigTripleF

public section

namespace CFSG.LocalAnalysis.GLTheoremA.K1419E

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Dickson.Sec6.Up34Exc

section Main


theorem k1419e_innerBigNonA {τ : Tag} (hτ : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) :
    ∀ (L : Type) [Field L] [IsAlgClosed L] [CharP L 2] (p₀ : ℕ) (S : LangSetup τ L p₀)
      (a : Fin τ.rank → Lˣ), rootDiagUnit τ a ∈ S.D.torus → (∀ j, a j ^ 3 = 1) →
      rootDiagUnit τ a ≠ 1 →
      ∀ i : KernelComponent (rootCharHom a), twistKind S.ρ (rootCharHom a) i = .inner →
        14 ≤ (componentRoots (rootCharHom a) i).ncard →
        ¬ (1 ≤ compRank (componentRoots (rootCharHom a) i) ∧
            (componentRoots (rootCharHom a) i).ncard =
              compRank (componentRoots (rootCharHom a) i) *
                (compRank (componentRoots (rootCharHom a) i) + 1)) →
        CFSG.IsQuasisimple (rationalComponent S.ρ S.Γ (rootCharHom a) i) →
        27 ∣ Nat.card (↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸
          Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)) := by
  intro L _ _ _ p₀ S a hT hap _ i hk hbig hnonA _
  obtain ⟨D⟩ := nonempty_innerData S hT i hk
  refine k1419e_dvd_27_of_triple hτ D hbig ?_
  rcases hτ with rfl | rfl | rfl | rfl
  · exact k1419e_hasTriple_F4 S hap i hnonA
  · exact k1419e_hasTriple_E6 S hap i hnonA
  · exact k1419e_hasTriple_E7 S hap i hnonA
  · exact k1419e_hasTriple_E8 S hap i hnonA

end Main

end CFSG.LocalAnalysis.GLTheoremA.K1419E

end
