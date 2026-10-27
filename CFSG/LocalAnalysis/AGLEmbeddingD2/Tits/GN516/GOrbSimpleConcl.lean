module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.GN516.GraphOrbitDefs
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.MinParTwoPar

public section

namespace CFSG.AGLEmbeddingD2.Tits.GN516

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.AGLEmbeddingD2.GN
open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData

@[expose] def GOrbConclS {Y : Type*} [Group Y] (R P : Subgroup Y) : Prop :=
  Group.IsSolvable ↥(pElementSubgroup 2 (conjClosure P R)) ∨
    (∃ C : Subgroup Y, C ≤ pElementSubgroup 2 C ∧ C ≤ pElementSubgroup 2 (conjClosure P R) ∧
      pElementSubgroup 2 (conjClosure P R) ≤ Subgroup.normalizer (C : Set Y) ∧
      pElementSubgroup 2 (conjClosure P R) ≤ conjClosure C R ∧
      ∀ r ∈ R, r ∉ Subgroup.normalizer (P : Set Y) →
        ⁅C, B6.conjSub r C⁆ ≤ pCoreOf 2 (pElementSubgroup 2 (conjClosure P R))) ∨
    QuasisimpleModTwoNonab ↥(twoResidual (pElementSubgroup 2 (conjClosure P R)))

@[expose] def ResidualGraph (Y : Type) [Group Y] : Prop :=
  ∀ T : Subgroup Y, IsSylowTwoOf T ⊤ →
    (∃ P₁ P₂ : Subgroup Y, MsideParabolicEscape.MinPar.TwoPar Y T P₁ P₂) ∨
      IsCoatom (Subgroup.normalizer (T : Set Y))

end CFSG.AGLEmbeddingD2.Tits.GN516
