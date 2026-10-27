module

public import CFSG.GH74.Generic.S3.Defs

public section

namespace CFSG.GH74.Generic.S3

open CFSG CFSG.GH74 CFSG.GH74.Generic CFSG.Blueprint CFSG.ABGLocalTools CFSG.Assembly.LowTwoRank Subgroup
open scoped MatrixGroups

@[expose] def IsCompC {G : Type} [Group G] (I : Subgroup G) (u : G) : Prop :=
  I ≤ centralizer ({u} : Set G) ∧ IsComponent (I.subgroupOf (centralizer ({u} : Set G)))

@[expose] def IsNormCompC {G : Type} [Group G] (I : Subgroup G) (u : G) : Prop :=
  IsCompC I u ∧ (I.subgroupOf (centralizer ({u} : Set G))).Normal

structure GlobalHyp (G : Type) [Group G] [Finite G] : Prop where
  simple : IsSimpleGroup G
  nonab : ∃ a b : G, a * b ≠ b * a
  rank : 3 ≤ Open.twoRank G
  gen4 : Gen4 G
  kgh : KGH G
  sylow : ∀ S : Sylow 2 G, ¬ IsMulCommutative (S : Subgroup G)
  layerNe : ∃ y : G, orderOf y = 2 ∧ layerBar y ≠ ⊥

theorem S3Setup.global {G : Type} [Group G] [Finite G] {x : G} {K : Subgroup (CentralizerBar x)}
    (h : S3Setup G x K) : GlobalHyp G :=
  ⟨h.simple, h.nonab, h.rank, h.gen4, h.kgh, h.sylow, h.layerNe⟩

structure Conf2A (G : Type) [Group G] [Finite G] (t : StatedLieTag) (p f : ℕ) (v w : G)
    (Iv Iw Ivw P : Subgroup G) : Prop where
  tag : t = .PSL ∨ t = .PSU
  prime : p.Prime ∧ p ≠ 2 ∧ 5 ≤ p ^ f
  v_inv : orderOf v = 2
  w_inv : orderOf w = 2
  comm : v * w = w * v
  ne : v ≠ w
  comp_v : IsCompC Iv v
  comp_w : IsNormCompC Iw w
  comp_vw : IsNormCompC Ivw (v * w)
  v_mem : v ∈ Iv
  iso_v : ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = p ^ f ∧ Nonempty (SL(2, F) ≃* Iv)
  model_w : LieModel (↥Iw ⧸ center ↥Iw) t 3 p f
  model_vw : LieModel (↥Ivw ⧸ center ↥Ivw) t 3 p f
  odd_w : Odd (Nat.card ↥(center ↥Iw))
  odd_vw : Odd (Nat.card ↥(center ↥Ivw))
  le_w : Iv ≤ Iw
  le_vw : Iv ≤ Ivw
  notConj_w : ¬ IsConj v w
  notConj_vw : ¬ IsConj v (v * w)
  sylow_w : IsSylowOf 2 P (centralizer ({w} : Set G))
  sylow_vw : IsSylowOf 2 P (centralizer ({v * w} : Set G))
  v_P : v ∈ P
  w_P : w ∈ P
  v_central : ∀ a ∈ P, a * v = v * a
  Q_iso : Nonempty (↥(P ⊓ centralizer (Iw : Set G)) ≃* ↥(P ⊓ centralizer (Ivw : Set G)))
  Q_cyc : IsCyclic ↥(P ⊓ centralizer (Iw : Set G))
  Q_exp : (t = .PSL → Monoid.exponent ↥(P ⊓ centralizer (Iw : Set G)) ∣ p ^ f - 1) ∧
    (t = .PSU → Monoid.exponent ↥(P ⊓ centralizer (Iw : Set G)) ∣ p ^ f + 1)

end CFSG.GH74.Generic.S3
