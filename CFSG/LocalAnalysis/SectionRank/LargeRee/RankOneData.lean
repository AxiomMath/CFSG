module

public import CFSG.LocalAnalysis.SectionRank.LargeRee.Torus
public import CFSG.LocalAnalysis.SectionRank.LargeRee.Blocks

public section

namespace CFSG.SectionRank.LargeRee

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree CFSG.LieType.Simplicity

variable {K : Type} [Field K] [Finite K] [CharP K ReeTag.F4.prime] (a : ℕ)

noncomputable abbrev blockX
    (i : Fin 2) : Subgroup (reeFixed ReeTag.F4 K a) :=
  UminusFixed ReeTag.F4 K a (blockGen i : WeylGroup ReeTag.F4.tag)

@[expose] noncomputable def blockT
    (hK : Nat.card K = ReeTag.F4.prime ^ (2 * a + 1)) :
    Fin 2 → Subgroup (reeFixed ReeTag.F4 K a)
  | 0 => reeTorusSub a hK fi_zero_mem_longSet
  | 1 => reeTorusSub a hK fi_one_mem_longSet

@[expose] def RankOneCells
    (i : Fin 2) (T : Subgroup (reeFixed ReeTag.F4 K a)) : Prop :=
  ∀ x ∈ blockX (K := K) a i,
    (∃ t ∈ T, ∃ y ∈ blockX (K := K) a i,
      relNrepHom K a (blockGen i) * x * relNrepHom K a (blockGen i) = t * y) ∨
    ∃ t ∈ T, ∃ y ∈ blockX (K := K) a i, ∃ y' ∈ blockX (K := K) a i,
      relNrepHom K a (blockGen i) * x * relNrepHom K a (blockGen i) =
        t * y * relNrepHom K a (blockGen i) * y'

@[expose] def RankOneSection
    {E : Type*} [Group E] (π : E →* reeFixed ReeTag.F4 K a) (i : Fin 2)
    (T : Subgroup (reeFixed ReeTag.F4 K a)) : Prop :=
  ∃ R : Subgroup (reeFixed ReeTag.F4 K a), ∃ r : R →* E, (∀ g, π (r g) = g) ∧
    blockX (K := K) a i ≤ R ∧ T ≤ R ∧ relNrepHom K a (blockGen i) ∈ R

end CFSG.SectionRank.LargeRee
