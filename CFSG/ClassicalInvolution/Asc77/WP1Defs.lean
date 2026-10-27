module

public import CFSG.ClassicalInvolution.Asc77.HypOmegaDefs

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution.Generic

variable {G : Type} [Group G]

@[expose] def centerIn (R : Subgroup G) : Subgroup G :=
  (Subgroup.center ↥R).map R.subtype

@[expose] def OCW (W : Subgroup G) : Subgroup G :=
  oddCoreOf (Subgroup.centralizer (W : Set G))

@[expose] def DSet (Ω : Set (Subgroup G)) (W : Subgroup G) : Set (Subgroup G) :=
  {R | R ∈ RSet Ω ∧ R ≤ Subgroup.normalizer (W : Set G)}

@[expose] def MGrp (Ω : Set (Subgroup G)) (W : Subgroup G) : Subgroup G :=
  ⨆ R ∈ DSet Ω W, R

@[expose] def NQuot (K : Subgroup G) : Type :=
  ↥(Subgroup.normalizer (K : Set G)) ⧸ K.subgroupOf (Subgroup.normalizer (K : Set G))

noncomputable instance (K : Subgroup G) : Group (NQuot K) := by
  unfold NQuot
  exact inferInstance

@[expose] noncomputable def muImage (M W : Subgroup G) : Subgroup (NQuot (W ⊔ OCW W)) :=
  ((M ⊔ OCW W).subgroupOf (Subgroup.normalizer ((W ⊔ OCW W : Subgroup G) : Set G))).map
    (QuotientGroup.mk' _)

@[expose] noncomputable def muGroup (Ω : Set (Subgroup G)) (W : Subgroup G) :
    Subgroup (NQuot (W ⊔ OCW W)) :=
  muImage (MGrp Ω W) W

@[expose] def DComm (W R T : Subgroup G) : Prop :=
  ¬ (T ≤ R ⊔ W ⊔ OCW W) ∧ ∀ r ∈ R, ∀ t ∈ T, (r * t * r⁻¹ * t⁻¹) ∈ W ⊔ OCW W

@[expose] def DOrder3 (W R S : Subgroup G) : Prop :=
  ∃ r ∈ R, ∃ s ∈ S, r ∉ W ⊔ OCW W ∧ s ∉ W ⊔ OCW W ∧ (r * s) ^ 3 ∈ W ⊔ OCW W ∧
    r * s ∉ W ⊔ OCW W

@[expose] def IsSylow2In (V P : Subgroup G) : Prop :=
  V ≤ P ∧ IsPGroup 2 V ∧ ∀ V' : Subgroup G, V' ≤ P → IsPGroup 2 V' → V ≤ V' → V' = V

@[expose] def IsSemidihedral (P : Subgroup G) : Prop :=
  ∃ a b : G, 8 ≤ orderOf a ∧ Nat.card P = 2 * orderOf a ∧ b * b = 1 ∧
    b ∉ Subgroup.zpowers a ∧ b * a * b⁻¹ = a ^ (orderOf a / 2 - 1) ∧
    Subgroup.closure {a, b} = P

@[expose] def IsWreathed (P : Subgroup G) : Prop :=
  ∃ a c b : G, 4 ≤ orderOf a ∧ orderOf c = orderOf a ∧ a * c = c * a ∧
    Nat.card P = 2 * orderOf a ^ 2 ∧ b * b = 1 ∧ b * a * b⁻¹ = c ∧ b * c * b⁻¹ = a ∧
    Subgroup.closure {a, c, b} = P

@[expose] def IsQuaternionSub (P : Subgroup G) : Prop :=
  ∃ a b : G, 4 ≤ orderOf a ∧ Nat.card P = 2 * orderOf a ∧ b * b = a ^ (orderOf a / 2) ∧
    b * a * b⁻¹ = a⁻¹ ∧ Subgroup.closure {a, b} = P

@[expose] def FixesUniqueCoset (a : G) (H : Subgroup G) : Prop :=
  ∃! c : G ⧸ H, a • c = c

end CFSG.ClassicalInvolution.Asc77
