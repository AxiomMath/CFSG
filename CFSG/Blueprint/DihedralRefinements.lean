module

public import CFSG.Dihedral.BlueprintDefs

public noncomputable section

namespace CFSG.DihedralBlueprint.OriginalData

variable {G : Type} [Group G] [Finite G] (d : OriginalData G)

@[expose] def primePart (p a : ℕ) : ℕ := p ^ a.factorization p

@[expose] def AlternatingQPrimary : Prop :=
  ∀ p ∈ primeSupport d.R, ∀ P : Subgroup G, IsSylowIn p P d.R →
    NormalizedBy P (d.S : Subgroup G) → HasAlternatingQuotient (d.HP P) →
    ∃ i j : Fin 2, i ≠ j ∧ d.commonE ⊓ d.HP P = d.JP P ∧ d.E j ⊓ d.HP P = d.JP P ∧
      ∃ I : Subgroup G, Nat.card I = 3 ∧
        d.E i ⊓ d.HP P = d.R ⊓ d.HP P ∧ d.R ⊓ d.HP P = d.JP P ⊔ I ∧
        d.JP P ⊓ I = ⊥ ∧ d.JP P ≤ Subgroup.centralizer (I : Set G) ∧
        primePart p (d.commonE.subgroupOf d.R).index = (if p = 3 then 3 else 1) ∧
        primePart p (d.commonE.subgroupOf (d.E i)).index = (if p = 3 then 3 else 1) ∧
        primePart p (d.commonE.subgroupOf (d.E j)).index = 1

@[expose] def CanonicalNormalizersFull : Prop :=
  d.CanonicalNormalizers ∧ d.AlternatingQPrimary

@[expose] def ConditionalSylowPrime : Prop :=
  ∀ k l : Fin 2, k ≠ l → ∀ R0 : Subgroup G, R0 ≤ d.R →
    (R0.subgroupOf d.R).Normal → NormalizedBy R0 (d.S : Subgroup G) →
    ⁅d.R, d.R⁆ ≤ R0 → ⁅d.R, d.V k⁆ ≤ R0 → ⁅d.R, (d.S : Subgroup G)⁆ ⊔ R0 ≠ d.R →
    NormalizedBy (d.E k ⊓ R0) (Subgroup.normalizer (d.V k : Set G)) →
    d.E l = d.commonE → (d.commonE.subgroupOf (d.E k)).index = 3 →
    ∀ p : ℕ, p.Prime → p ∣ ((d.E k).subgroupOf d.R).index →
      ∀ P : Subgroup G, IsSylowIn p P d.C → ¬ IsSylowIn p P ⊤

@[expose] def ConditionalOrderFull : Prop := d.ConditionalOrder ∧ d.ConditionalSylowPrime

end CFSG.DihedralBlueprint.OriginalData
