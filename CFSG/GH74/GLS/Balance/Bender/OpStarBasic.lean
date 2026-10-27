module

public import CFSG.GH74.GLS.Balance.Bender.Defs

public section

namespace CFSG.GH74.GLS.Balance

open Subgroup CFSG CFSG.GH74.GLS
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

@[expose] def oResOf (p : ℕ) (X : Subgroup G) : Subgroup G := (oResidual p ↥X).map X.subtype

@[expose] def IsSylowIn (p : ℕ) (T N : Subgroup G) : Prop :=
  T ≤ N ∧ IsPGroup p ↥T ∧ ∀ S : Subgroup G, S ≤ N → IsPGroup p ↥S → Nat.card ↥S ≤ Nat.card ↥T

omit [Finite G] in
theorem opStar_le (p : ℕ) (X : Subgroup G) : OpStar p X ≤ X :=
  sSup_le fun _ hN => hN.1

omit [Finite G] in
theorem le_opStar {p : ℕ} {N X : Subgroup G} (hNX : N ≤ X) (hn : (N.subgroupOf X).Normal)
    (hp : IsPStar p ↥N) : N ≤ OpStar p X :=
  le_sSup ⟨hNX, hn, hp⟩

instance opStar_normal (p : ℕ) (X : Subgroup G) : ((OpStar p X).subgroupOf X).Normal := by
  refine ⟨fun n hn g => ?_⟩
  have key : OpStar p X ≤ (OpStar p X).comap (MulAut.conj (g : G)).toMonoidHom := by
    refine sSup_le fun N hN => ?_
    intro m hm
    have hm' : (⟨m, hN.1 hm⟩ : ↥X) ∈ N.subgroupOf X := hm
    have h1 := hN.2.1.conj_mem _ hm' g
    have h2 : (g : G) * m * (g : G)⁻¹ ∈ N := h1
    exact le_sSup hN h2
  have hn' : (n : G) ∈ OpStar p X := hn
  have h3 : (g : G) * (n : G) * (g : G)⁻¹ ∈ OpStar p X := key hn'
  exact h3

@[expose] noncomputable def OpStarP (p : ℕ) (X : Subgroup G) : Subgroup G :=
  ((pCore p (↥X ⧸ (OpStar p X).subgroupOf X)).comap
    (QuotientGroup.mk' ((OpStar p X).subgroupOf X))).map X.subtype

end CFSG.GH74.GLS.Balance
