module

public import CFSG.Yardstones.Md8ed6d263d89.Definitions
public import CFSG.LocalAnalysis.GL83PartI.I_7_13
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic5KFacts

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.P5

open CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbeddingD2 CFSG.LocalAnalysis.RankThreeTheoremC Subgroup

@[expose] def GL83NormalElementaryRankFourOdd : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ), p.Prime → 5 ≤ p → ∀ R : Subgroup G, IsPGroup p R →
    4 ≤ Open.pRank p R →
      ∃ E : Subgroup G, E ≤ R ∧ R ≤ normalizer (E : Set G) ∧ IsElemAbelian p E ∧
        Nat.card E = p ^ 4

structure P5KFacts : Prop where
  h243 : GL83ComponentPCoreTrivial
  h244 : GL83NongenerationList
  hsig : GL83SignalizerAut
  hInn : KFactInnerAction
  hWC : KFactWeakClosure
  h713 : GL83.I_7_13_1
  hexcl : PPointExclusionFive

structure P5Global (G : Type) [Group G] [Finite G] : Prop where
  glob : D1Global G
  d1 : D1For G
  d2 : D2For G
  fc : FullCoreLocality G

@[expose] def PTypeHyp {G : Type} [Group G] [Finite G] (p : ℕ) (P : Sylow p G) (M : Subgroup G) :
    Prop :=
  ∀ (x : G) (R : Sylow p (RedCent p x)) (K : Subgroup (RedCent p x)) (i : TauCeti.CFSGIndex),
    CFSG.Yardstones.Md8ed6d263d89.PPointData p P M x R K i →
      CFSG.Yardstones.Md8ed6d263d89.IsLinTwoType p i ∨
        CFSG.Yardstones.Md8ed6d263d89.IsUnitaryThreeType p i

structure PtShape {G : Type} [Group G] (p : ℕ) (P : Sylow p G) (x : G) : Prop where
  abelian : IsMulCommutative (P : Subgroup G)
  weak : ∀ g : G, (zpowers x).map (MulAut.conj g).toMonoidHom ≤ (P : Subgroup G) →
    (zpowers x).map (MulAut.conj g).toMonoidHom = zpowers x

end CFSG.LocalAnalysis.RankFourTheoremC.P5
