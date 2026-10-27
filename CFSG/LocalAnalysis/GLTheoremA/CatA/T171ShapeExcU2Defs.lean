module

public import CFSG.GroupActions.SubgroupStabilizerOuterBound
public import CFSG.LocalAnalysis.GLTheoremA.CatA.MIAut
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeDefs
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieOuter

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T171Sh

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4
open CFSG.LocalAnalysis.GLTheoremA.S10
open CFSG.ComponentClassification.OuterAutomorphisms (innAutDerived)
open CFSG.ComponentClassification.PerfectAutomorphisms (centerQuotientHom)

@[expose] def ExcAdjCompInnAut : Prop :=
  ∀ {τ : CFSG.Blueprint.Chevalley.Tag},
    (τ = .G2 ∨ τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) →
    ∀ (K : Type) [Field K] [Finite K] [CharP K 2] (p : ℕ), p.Prime → p ≠ 2 →
      (τ = .G2 → 4 ≤ Nat.card K) →
      (τ = .E6 → p = 3 → ¬ 3 ∣ Nat.card K - 1) →
      ∀ x w : ↥(CFSG.Blueprint.Chevalley.adjointGroup τ K), x ≠ 1 → x ^ p = 1 → w ^ p = 1 →
        x * w = w * x →
      ∀ Kc : Subgroup ↥(CFSG.Blueprint.Chevalley.adjointGroup τ K),
        CFSG.Assembly.IsComponentOf Kc
          (CFSG.ComponentClassification.FixedCommutingProduct.fixedSubgroup
            (MulAut.conj x)) →
        Nat.card (↥Kc ⧸ Subgroup.center ↥Kc) ≠ 360 →
        ∀ hw : MulAut.conj w ∈ CFSG.GroupActions.subgroupStabAut Kc,
          centerQuotientHom ↥Kc (CFSG.GroupActions.subgroupStabRestrict Kc ⟨MulAut.conj w, hw⟩) ∈
            innAutDerived (↥Kc ⧸ Subgroup.center ↥Kc)

@[expose] def ExcSmallExit : Prop :=
  ∀ {G : Type} [Group G] [Finite G] (p : ℕ) (L J A : Subgroup G) (d b : G)
    (hS : Setup p L J A d b),
    catalogIs (PSimple p L) (onLie fun i : TauCeti.LieTypeIndex =>
      KD264Lie.isExcUntwistedIdx i ∧ i.characteristic = 2) →
    ¬ I171.I171LieShapeAt p L → InducesInnerMod p L b →
    (catalogIs (PSimple p J) (ambiguousChev 2) ∨
      catalogIs (PSimple p J) (onLie fun i : TauCeti.LieTypeIndex =>
        (∃ q : TauCeti.PrimePower, i = .D 4 q ∧ q.p = 2) ∨ i = .tits) ∨
      Nat.card (PSimple p J) = 360) →
    (MI.indAut p J b hS.b_norm ∈ innAutDerived (PSimple p J) ∨
      Nat.card (PSimple p J) = 360) →
    InducesInnerMod p J b

end CFSG.LocalAnalysis.GLTheoremA.T171Sh

end
