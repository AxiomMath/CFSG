module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711PfCover

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic

set_option linter.unusedSectionVars false

namespace Twin1711

section Defs

variable {G : Type} [Group G]

structure CoreData (X R : Subgroup G) (t : G) : Prop where
  le : R ≤ X
  q8 : Nonempty (↥R ≃* QuaternionGroup 2)
  inv : IsUniqueInvolution R t
  noncentral : ¬ ∀ x ∈ X, x * t = t * x
  inO2 : ∃ P : Subgroup G, P ≤ X ⊓ Subgroup.centralizer ({t} : Set G) ∧
    (∀ s ∈ X ⊓ Subgroup.centralizer ({t} : Set G), ∀ p ∈ P, s * p * s⁻¹ ∈ P) ∧
    IsPGroup 2 ↥P ∧ R ≤ P
  twins : ∀ s ∈ X ⊓ Subgroup.centralizer ({t} : Set G),
    conjSub s R = R ∨ Commutes R (conjSub s R)

theorem MemberData.core {X R : Subgroup G} {t : G} (h : MemberData X R t) : CoreData X R t :=
  ⟨h.le, h.q8, h.inv, h.noncentral, h.inO2, h.twins⟩

end Defs

@[expose] def NoSandwichAt (H : Type) [Group H] : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (X R : Subgroup G) (t : G) (B : Set (Subgroup G))
    (N : Subgroup G), Nonempty (↥X ≃* H) → CoreData X R t → SandwichData X R t B N → False

@[expose] def SandwichSizeTwoAt (H : Type) [Group H] : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (X R : Subgroup G) (t : G) (B : Set (Subgroup G))
    (N : Subgroup G), Nonempty (↥X ≃* H) → CoreData X R t → SandwichData X R t B N →
      B.ncard = 2

@[expose] def PairingAt (H : Type) [Group H] : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (X R : Subgroup G) (t : G), Nonempty (↥X ≃* H) →
    CoreData X R t →
      (commNbrs X R).ncard = 4 ∧
      ∀ J ∈ commNbrs X R, ∀ J' ∈ commNbrs X R, J ≠ J' → ∀ u u' : G,
        IsUniqueInvolution J u → IsUniqueInvolution J' u' →
          u ≠ u' ∧ ∀ x ∈ X, x * (u * u') = (u * u') * x

structure PfTables : Prop where
  sp0 : NoSandwichAt ModSp0
  sp1 : NoSandwichAt ModSp1
  om0 : NoSandwichAt ModOm0
  om1 : NoSandwichAt ModOm1
  om2 : SandwichSizeTwoAt ModOm2
  om2p : PairingAt ModOm2

section Derive


theorem fin1711Sandwich_of_tables (hT : PfTables) : Fin1711Sandwich := by
  intro G _ _ X R t B N hM hS
  have hc := hM.core
  rcases quasiE4_cases hM.quasi with ⟨e, -⟩ | ⟨e, -⟩ | ⟨e, -⟩ | ⟨e, -⟩ | ⟨e, hz⟩
  · exact (hT.sp0 G X R t B N e hc hS).elim
  · exact (hT.sp1 G X R t B N e hc hS).elim
  · exact (hT.om0 G X R t B N e hc hS).elim
  · exact (hT.om1 G X R t B N e hc hS).elim
  · exact ⟨hz, hT.om2 G X R t B N e hc hS⟩

theorem fin1711Pairing_of_tables (hT : PfTables) : Fin1711Pairing := by
  intro G _ _ X R t hM h4
  have hc := hM.core
  rcases quasiE4_cases hM.quasi with ⟨e, hz⟩ | ⟨e, hz⟩ | ⟨e, hz⟩ | ⟨e, hz⟩ | ⟨e, hz⟩
  · omega
  · omega
  · omega
  · omega
  · exact hT.om2p G X R t e hc

end Derive

end Twin1711

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
