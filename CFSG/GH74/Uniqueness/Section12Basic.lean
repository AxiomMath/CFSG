module

public import CFSG.GH74.Uniqueness.Bender.Models
public import CFSG.GH74.Uniqueness.Prop38

public section

namespace CFSG.GH74.Uniqueness

open Subgroup

section Basic

variable {X : Type} [Group X] [Finite X]

abbrev dGrp (M : Subgroup X) (t : X) : Subgroup X := M ⊓ conjugate M t

abbrev kGrp (M : Subgroup X) (t : X) : Subgroup X :=
  ⁅zpowers t, pPrimeCoreIn (M ⊓ conjugate M t)⁆

abbrev cenHull (Z : Set X) (v : X) : Subgroup X := zHull Z (centralizer ({v} : Set X))

@[expose] def deltaSet (Z : Set X) (M : Subgroup X) (u : X) : Set X :=
  {x | ∃ y ∈ centralizer ({u} : Set X) ⊓ zHull Z M, x = y * u}

@[expose] noncomputable def qU (Z : Set X) (M : Subgroup X) (u : X) : ℕ :=
  Nat.card ↥(centralizer ({u} : Set X) ⊓ zHull Z M)

@[expose] def Shears (Z : Set X) (M : Subgroup X) (u : X) : Prop :=
  ∃ x ∈ deltaSet Z M u, x ≠ u ∧ IsConj u x

@[expose] def zM (Z : Set X) (M : Subgroup X) : Set X := Z ∩ (M : Set X)

end Basic

section BenderSub

variable {X : Type} [Group X] [Finite X]

structure BenderSub (Z : Set X) (M F : Subgroup X) (n i e : ℕ) : Prop where
  ne_top : F ≠ ⊤
  not_le : ¬ F ≤ M
  nonempty : (Z ∩ ((F ⊓ M : Subgroup X) : Set X)).Nonempty
  zhull : zHull Z F = F
  core : pPrimeCoreIn F = (center ↥F).map F.subtype
  bender : Bender.BenderType (↥F ⧸ center ↥F) n i e
  borel : ∃ T : Sylow 2 (↥F ⧸ center ↥F),
    ((M ⊓ F).subgroupOf F).map (QuotientGroup.mk' (center ↥F)) =
      normalizer ((T : Subgroup (↥F ⧸ center ↥F)) : Set (↥F ⧸ center ↥F))
  invol : ∀ y ∈ F, orderOf y = 2 → y ∈ Z
  strong : IsStronglyEmbedded ((M ⊓ F).subgroupOf F)

end BenderSub

structure Ctx12 {X : Type} [Group X] [Finite X] (Z : Set X) (M : Subgroup X) where
  t : X
  z : X
  ht : t ∈ Z
  htM : t ∉ M
  hz : z ∈ Z
  hzM : z ∈ M
  hD : Even (Nat.card ↥(M ⊓ conjugate M t))
  hL : lSubgroup M z t ≠ ⊤

namespace Ctx12

variable {X : Type} [Group X] [Finite X] {Z : Set X} {M : Subgroup X}

abbrev L (c : Ctx12 Z M) : Subgroup X := lSubgroup M c.z c.t

abbrev D (c : Ctx12 Z M) : Subgroup X := M ⊓ conjugate M c.t

end Ctx12

end CFSG.GH74.Uniqueness
