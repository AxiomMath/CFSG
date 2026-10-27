module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GenericLayerReductionDefs
public import CFSG.LocalAnalysis.AGLEmbedding.CatalogComponent
public import CFSG.Open.GLBDefs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.RankThree.PartOne.Census3 (IsoLie)
open scoped MatrixGroups

@[expose] def KFactComponentPCoreThree : Prop :=
  ∀ (X : Type) [Group X] [Finite X], CFSG.AGLEmbedding.CatalogSimpleSections X →
    ∀ (R : Sylow 3 X) (K : Subgroup X), 3 ≤ CFSG.Open.pRank 3 (R : Subgroup X) →
      IsComponentOf K ⊤ → ¬ K ≤ GLBWeakCore 3 (R : Subgroup X) → CFSG.pCore 3 K = ⊥

@[expose] def IsPrimeThreeType (Q : Type) [Group Q] : Prop :=
  Nonempty (Q ≃* PSL(2, GaloisField 3 2)) ∨
  (∃ q : TauCeti.PrimePower, q.p = 3 ∧ q.exponent = 1 ∧ IsoLie Q (.twistedA 2 q)) ∨
  Nonempty (Q ≃* (TauCeti.CFSGIndex.sporadic TauCeti.SporadicName.M11).Group) ∨
  (∃ q : TauCeti.PrimePower, q.p = 2 ∧ q.exponent = 2 ∧ IsoLie Q (.A 2 q)) ∨
  IsoLie Q (.A 1 ⟨2, 3, by norm_num, by norm_num⟩)

@[expose] def GenericRedThreeAt (G : Type) [Group G] [Finite G]
    (L : ∀ (Q : Type) [Group Q], Prop) : Prop :=
  GenericAt G fun p _ M x => p = 3 → ∀ J : Subgroup G,
    J ≤ Subgroup.centralizer ({x} : Set G) →
    Subgroup.centralizer ({x} : Set G) ≤ Subgroup.normalizer (J : Set G) → Group.IsPerfect J →
    rankThreePrimeCore p J < J →
    (∀ N : Subgroup G, N ≤ J → (N.subgroupOf J).Normal → rankThreePrimeCore p J ≤ N →
      N = rankThreePrimeCore p J ∨ N = J) → ¬ J ≤ M →
    ∀ (Q : Type) [Group Q] (ψ : ↥J →* Q), Function.Surjective ψ →
      ψ.ker = (rankThreePrimeCore p J).subgroupOf J → L Q → False

@[expose] def GL83GenericPrimeThreeTypes (G : Type) [Group G] [Finite G] : Prop :=
  GenericRedThreeAt G fun Q _ => IsPrimeThreeType Q

theorem GenericRedThreeAt.mono {G : Type} [Group G] [Finite G]
    {L L' : ∀ (Q : Type) [Group Q], Prop} (hLL : ∀ (Q : Type) [Group Q], L' Q → L Q)
    (h : GenericRedThreeAt G L) : GenericRedThreeAt G L' := by
  intro p hp P M hM hfail hIH x hgen hp3 J hJC hCJ hperf hlt hmin hnot Q _ ψ hψ hker hL
  exact h p hp P M hM hfail hIH x hgen hp3 J hJC hCJ hperf hlt hmin hnot Q ψ hψ hker (hLL Q hL)

theorem GenericRedThreeAt.union {G : Type} [Group G] [Finite G]
    {L₁ L₂ : ∀ (Q : Type) [Group Q], Prop}
    (h₁ : GenericRedThreeAt G L₁) (h₂ : GenericRedThreeAt G L₂) :
    GenericRedThreeAt G fun Q _ => L₁ Q ∨ L₂ Q := by
  intro p hp P M hM hfail hIH x hgen hp3 J hJC hCJ hperf hlt hmin hnot Q _ ψ hψ hker hL
  rcases hL with hL | hL
  · exact h₁ p hp P M hM hfail hIH x hgen hp3 J hJC hCJ hperf hlt hmin hnot Q ψ hψ hker hL
  · exact h₂ p hp P M hM hfail hIH x hgen hp3 J hJC hCJ hperf hlt hmin hnot Q ψ hψ hker hL

@[expose] def GL83GenericPrimeThreeA6 (G : Type) [Group G] [Finite G] : Prop :=
  GenericRedThreeAt G fun Q _ => Nonempty (Q ≃* PSL(2, GaloisField 3 2))

@[expose] def GL83GenericPrimeThreeU3 (G : Type) [Group G] [Finite G] : Prop :=
  GenericRedThreeAt G fun Q _ =>
    ∃ q : TauCeti.PrimePower, q.p = 3 ∧ q.exponent = 1 ∧ IsoLie Q (.twistedA 2 q)

@[expose] def GL83GenericPrimeThreeM11 (G : Type) [Group G] [Finite G] : Prop :=
  GenericRedThreeAt G fun Q _ =>
    Nonempty (Q ≃* (TauCeti.CFSGIndex.sporadic TauCeti.SporadicName.M11).Group)

@[expose] def GL83GenericPrimeThreeL34 (G : Type) [Group G] [Finite G] : Prop :=
  GenericRedThreeAt G fun Q _ =>
    ∃ q : TauCeti.PrimePower, q.p = 2 ∧ q.exponent = 2 ∧ IsoLie Q (.A 2 q)

@[expose] def GL83GenericPrimeThreeL28 (G : Type) [Group G] [Finite G] : Prop :=
  GenericRedThreeAt G fun Q _ => IsoLie Q (.A 1 ⟨2, 3, by norm_num, by norm_num⟩)

end CFSG.LocalAnalysis.RankThreeTheoremC
