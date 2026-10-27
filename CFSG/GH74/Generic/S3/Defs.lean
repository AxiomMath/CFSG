module

public import CFSG.GH74.Generic.Front.Transfer
public import CFSG.GH74.Generic.Shapes

public section

namespace CFSG.GH74.Generic.S3

open CFSG CFSG.GH74 CFSG.GH74.Generic CFSG.Blueprint Subgroup

structure S3Setup (G : Type) [Group G] [Finite G] (x : G) (K : Subgroup (CentralizerBar x)) :
    Prop where
  simple : IsSimpleGroup G
  nonab : ∃ a b : G, a * b ≠ b * a
  rank : 3 ≤ Open.twoRank G
  gen4 : Gen4 G
  kgh : KGH G
  sylow : ∀ S : Sylow 2 G, ¬ IsMulCommutative (S : Subgroup G)
  layerNe : ∃ y : G, orderOf y = 2 ∧ layerBar y ≠ ⊥
  inv : orderOf x = 2
  comp : IsComponent K
  g2 : GLS.InG2 ↥K
  shape : ShapeS3 x K

@[expose] def QcongEps {G : Type} [Group G] {x : G} (K : Subgroup (CentralizerBar x)) : Prop :=
  ∃ p f : ℕ, (LieModel ↥K .PSL 3 p f ∧ p ^ f % 4 = 1) ∨ (LieModel ↥K .PSU 3 p f ∧ p ^ f % 4 = 3)

@[expose] def QcongNegEps {G : Type} [Group G] {x : G} (K : Subgroup (CentralizerBar x)) : Prop :=
  ∃ p f : ℕ, (LieModel ↥K .PSL 3 p f ∧ p ^ f % 4 = 3) ∨ (LieModel ↥K .PSU 3 p f ∧ p ^ f % 4 = 1)

@[expose] def CentralizerCyclic2 {G : Type} [Group G] (x : G) (K : Subgroup (CentralizerBar x)) :
    Prop :=
  ∀ P : Subgroup (CentralizerBar x), IsPGroup 2 ↥P → P ≤ centralizer (K : Set (CentralizerBar x)) →
    IsCyclic ↥P

@[expose] noncomputable def imgBar {G : Type} [Group G] (x : G) (M : Subgroup G) :
    Subgroup (CentralizerBar x) :=
  (M.subgroupOf (centralizer ({x} : Set G))).map (proj x)

theorem mem_imgBar {G : Type} [Group G] {x : G} {M : Subgroup G} {c : CentralizerBar x} :
    c ∈ imgBar x M ↔ ∃ g : ↥(centralizer ({x} : Set G)), (g : G) ∈ M ∧ proj x g = c := by
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact ⟨g, hg, rfl⟩
  · rintro ⟨g, hg, rfl⟩
    exact ⟨g, hg, rfl⟩

theorem imgBar_mono {G : Type} [Group G] (x : G) {M N : Subgroup G} (h : M ≤ N) :
    imgBar x M ≤ imgBar x N := by
  intro c hc
  obtain ⟨g, hg, rfl⟩ := mem_imgBar.1 hc
  exact mem_imgBar.2 ⟨g, h hg, rfl⟩

@[expose] def A3Reflection {G : Type} [Group G] (x u : G) (Y : Fin 3 → Subgroup G) : Prop :=
  (∀ g ∈ Y 0, g * x = x * g) ∧ (∀ g ∈ Y 1, g * x = x * g) ∧
    ∀ g ∈ Y 2, g * (x * u) = (x * u) * g

end CFSG.GH74.Generic.S3
