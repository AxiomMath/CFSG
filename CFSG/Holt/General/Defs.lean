module

public import CFSG.Foundations.Basic
public import CFSG.Open.FusionDefs

public section

namespace CFSG.Holt.General

open MulAction

variable (G : Type*) [Group G] (Ω : Type*) [MulAction G Ω]

structure IsHoltTriple (z : G) (α : Ω) : Prop where
  isPretransitive : IsPretransitive G Ω
  orderOf_eq_two : orderOf z = 2
  smul_eq_iff : ∀ ω : Ω, z • ω = ω ↔ ω = α
  exists_sylow : ∃ S : Sylow 2 G, z ∈ (S : Subgroup G) ∧
    (S : Subgroup G) ≤ Subgroup.centralizer {z}

variable {G}

@[expose] def oddCoreOf (B : Subgroup G) : Subgroup G :=
  (CFSG.pPrimeCore 2 B).map B.subtype

@[expose] def zStarIn (B : Subgroup G) : Subgroup B :=
  haveI : (CFSG.pPrimeCore 2 B).Normal := CFSG.pPrimeCore_normal
  (Subgroup.center (B ⧸ CFSG.pPrimeCore 2 B)).comap (QuotientGroup.mk' (CFSG.pPrimeCore 2 B))

instance zStarIn_normal (B : Subgroup G) : (zStarIn B).Normal := by
  have : (CFSG.pPrimeCore 2 B).Normal := CFSG.pPrimeCore_normal
  unfold zStarIn
  exact Subgroup.Normal.comap inferInstance _

@[expose] def stabilizerImage (α : Ω) (B : Subgroup G) : Subgroup (B ⧸ zStarIn B) :=
  ((stabilizer G α).subgroupOf B).map (QuotientGroup.mk' (zStarIn B))

variable (G)

@[expose] def IsGoodZ (α : Ω) (B : Subgroup G) : Prop :=
  (CFSG.Open.fusionIsBenderGroup (B ⧸ zStarIn B) ∧
      CFSG.IsStronglyEmbedded (stabilizerImage Ω α B)) ∨
    ∃ m : ℕ, 2 ≤ m ∧ ∃ e : (B ⧸ zStarIn B) ≃* alternatingGroup (Fin (2 * m + 1)),
      (stabilizerImage Ω α B).map e.toMonoidHom =
        stabilizer (alternatingGroup (Fin (2 * m + 1))) (0 : Fin (2 * m + 1))

end CFSG.Holt.General
