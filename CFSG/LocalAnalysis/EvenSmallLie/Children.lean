module

public import CFSG.Blueprint.EvenStandardExact
public import CFSG.Blueprint.RecognitionDefs
public import CFSG.Open.StandardComponentRecognitionMilestoneDefs

public section

namespace CFSG.EvenSmallLie

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.Recognition

structure StandardSetting (G : Type) [Group G] [Finite G] (L : Subgroup G) : Prop where
  simple : IsSimpleGroup G
  nonab : ∃ a b : G, a * b ≠ b * a
  kProper : CFSG.Assembly.KProper Blueprint.Catalog G
  standard : standardComponentIsStandard L
  core : ∀ t : G, orderOf t = 2 →
    standardComponentOddCore (centralizer ({t} : Set G)) = ⊥
  cyclic : ∃ S : Sylow 2 (centralizer (L : Set G)),
    IsCyclic (S : Subgroup (centralizer (L : Set G)))

@[expose] def ChildG2F4 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), StandardSetting G L →
    Nat.card (center L) = 2 →
    (LieModel (L ⧸ center L) .G2 0 2 2 ∨ LieModel (L ⧸ center L) .F4 0 2 1) → False

@[expose] def Child2E6 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), StandardSetting G L →
    Nat.card (center L) = 2 → LieModel (L ⧸ center L) .twistedE6 0 2 1 →
    NativeSporadic.IsSporadic G .B

@[expose] def ChildSp6Centerless : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), StandardSetting G L →
    center L = ⊥ → LieModel (L ⧸ center L) .PSp 3 2 1 → False

@[expose] def ChildSp6Cover : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), StandardSetting G L →
    center L ≠ ⊥ → IsPGroup 2 (center L) → LieModel (L ⧸ center L) .PSp 3 2 1 →
    NativeSporadic.IsSporadic G .Co3

@[expose] def ChildU6Centerless : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), StandardSetting G L →
    center L = ⊥ → LieModel (L ⧸ center L) .PSU 6 2 1 → False

@[expose] def ChildU6Cover : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), StandardSetting G L →
    center L ≠ ⊥ → IsPGroup 2 (center L) → LieModel (L ⧸ center L) .PSU 6 2 1 →
    NativeSporadic.IsSporadic G .Fi22

@[expose] def ChildO8PlusCenterless : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), StandardSetting G L →
    center L = ⊥ → LieModel (L ⧸ center L) .POmegaPlus 4 2 1 → False

@[expose] def ChildO8PlusCover : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), StandardSetting G L →
    center L ≠ ⊥ → IsPGroup 2 (center L) → LieModel (L ⧸ center L) .POmegaPlus 4 2 1 → False

@[expose] def ChildO8Minus : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), StandardSetting G L →
    center L = ⊥ → LieModel L .POmegaMinus 4 2 1 → False

theorem even_small_lie_of_children (h1 : ChildG2F4) (h2 : Child2E6) (h3 : ChildSp6Centerless)
    (h4 : ChildSp6Cover) (h5 : ChildU6Centerless) (h6 : ChildU6Cover)
    (h7 : ChildO8PlusCenterless) (h8 : ChildO8PlusCover) (h9 : ChildO8Minus)
    (G : Type) [Group G] [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (hK : CFSG.Assembly.KProper Blueprint.Catalog G)
    (L : Subgroup G) (hL : standardComponentIsStandard L)
    (hcore : ∀ t : G, orderOf t = 2 →
      standardComponentOddCore (centralizer ({t} : Set G)) = ⊥)
    (S : Sylow 2 (centralizer (L : Set G)))
    (hS : IsCyclic (S : Subgroup (centralizer (L : Set G))))
    (hres : Exact.EvenStandardResidual L)
    (hbcd : Exact.ResidualB L ∨ Exact.ResidualC L ∨ Exact.ResidualD L) :
    EvenSporadicOutcome G := by
  have hset : StandardSetting G L := ⟨inferInstance, hnonab, hK, hL, hcore, S, hS⟩
  have hZ2 : IsPGroup 2 (center L) := hres.1
  rcases hbcd with ⟨hc, hB | hB | hB⟩ | hC | ⟨hc, hD⟩
  · exact (h1 G L hset hc (Or.inl hB)).elim
  · exact (h1 G L hset hc (Or.inr hB)).elim
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (h2 G L hset hc hB))))))
  · by_cases hcb : center L = ⊥
    · rcases hC with hC | hC | hC
      · exact (h3 G L hset hcb hC).elim
      · exact (h5 G L hset hcb hC).elim
      · exact (h7 G L hset hcb hC).elim
    · rcases hC with hC | hC | hC
      · exact Or.inl (h4 G L hset hcb hZ2 hC)
      · exact Or.inr (Or.inr (Or.inl (h6 G L hset hcb hZ2 hC)))
      · exact (h8 G L hset hcb hZ2 hC).elim
  · exact (h9 G L hset hc hD).elim

end CFSG.EvenSmallLie
