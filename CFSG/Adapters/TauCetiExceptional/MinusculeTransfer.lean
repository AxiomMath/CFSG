module

public import CFSG.Adapters.TauCetiExceptional.TwistedTransfer

public noncomputable section

namespace CFSG.TauCetiBridge.Minuscule

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley TauCeti
open scoped commutatorElement

@[expose] def frobFixedGroup (τ : Tag) (L : Type) [Field L] (Fr : L →+* L) :
    Subgroup (ModGL τ L) :=
  adjointGroup τ L ⊓ (Units.map (entrywiseHom Fr)).eqLocus (MonoidHom.id _)

variable {τ : Tag} {L : Type} [Field L] {Fr : L →+* L} {G : Type} [Group G]

structure IsIsogeny (τ : Tag) (L : Type) [Field L] (Fr : L →+* L) (F : G →* G)
    (π : G →* ModGL τ L) : Prop where
  mem : ∀ g, π g ∈ adjointGroup τ L
  surj : ∀ x ∈ adjointGroup τ L, ∃ g, π g = x
  ker : ∀ g, π g = 1 → g ∈ Subgroup.center G
  comm : ∀ g, π (F g) = Units.map (entrywiseHom Fr) (π g)

namespace IsIsogeny

variable {F : G →* G} {π : G →* ModGL τ L} (h : IsIsogeny τ L Fr F π)
include h

theorem map_fixedSubgroup_le : (fixedSubgroup F).map π ≤ frobFixedGroup τ L Fr := by
  rintro _ ⟨g, hg, rfl⟩
  refine ⟨h.mem g, ?_⟩
  change Units.map (entrywiseHom Fr) (π g) = π g
  rw [← h.comm, mem_fixedSubgroup.1 hg]

theorem inv_mul_mem_center {g : G} (hg : π g ∈ frobFixedGroup τ L Fr) :
    g⁻¹ * F g ∈ Subgroup.center G := by
  apply h.ker
  have hg2 : Units.map (entrywiseHom Fr) (π g) = π g := hg.2
  rw [map_mul, map_inv, h.comm, hg2, inv_mul_cancel]

theorem commutator_le_map :
    ⁅frobFixedGroup τ L Fr, frobFixedGroup τ L Fr⁆ ≤ (fixedSubgroup F).map π := by
  rw [Subgroup.commutator_le]
  intro r₁ hr₁ r₂ hr₂
  obtain ⟨g₁, rfl⟩ := h.surj r₁ hr₁.1
  obtain ⟨g₂, rfl⟩ := h.surj r₂ hr₂.1
  refine ⟨⁅g₁, g₂⁆, ?_, map_commutatorElement π g₁ g₂⟩
  change F ⁅g₁, g₂⁆ = ⁅g₁, g₂⁆
  rw [map_commutatorElement]
  have e₁ : F g₁ = g₁ * (g₁⁻¹ * F g₁) := by group
  have e₂ : F g₂ = g₂ * (g₂⁻¹ * F g₂) := by group
  rw [e₁, e₂, Twisted.commutatorElement_mul_mul_of_mem_center _ _ (h.inv_mul_mem_center hr₁)
    (h.inv_mul_mem_center hr₂)]

variable (hperf : ⁅⁅frobFixedGroup τ L Fr, frobFixedGroup τ L Fr⁆,
  ⁅frobFixedGroup τ L Fr, frobFixedGroup τ L Fr⁆⁆ = ⁅frobFixedGroup τ L Fr, frobFixedGroup τ L Fr⁆)
include hperf

theorem map_commutator_fixedSubgroup :
    ⁅fixedSubgroup F, fixedSubgroup F⁆.map π = ⁅frobFixedGroup τ L Fr, frobFixedGroup τ L Fr⁆ := by
  rw [Subgroup.map_commutator]
  refine le_antisymm (Subgroup.commutator_mono h.map_fixedSubgroup_le h.map_fixedSubgroup_le) ?_
  calc ⁅frobFixedGroup τ L Fr, frobFixedGroup τ L Fr⁆ = _ := hperf.symm
    _ ≤ _ := Subgroup.commutator_mono h.commutator_le_map h.commutator_le_map

@[expose] def derivedMap :
    ↥(commutator ↥(fixedSubgroup F)) →* ↥⁅frobFixedGroup τ L Fr, frobFixedGroup τ L Fr⁆ :=
  ((π.comp (fixedSubgroup F).subtype).comp (commutator ↥(fixedSubgroup F)).subtype).codRestrict _
    fun x => by
      rw [← h.map_commutator_fixedSubgroup hperf, ← Twisted.map_subtype_commutator]
      exact ⟨((x : ↥(fixedSubgroup F)) : G), ⟨x, x.2, rfl⟩, rfl⟩

theorem coe_derivedMap (x : ↥(commutator ↥(fixedSubgroup F))) :
    (h.derivedMap hperf x : ModGL τ L) = π ((x : ↥(fixedSubgroup F)) : G) :=
  rfl

theorem derivedMap_surjective : Function.Surjective (h.derivedMap hperf) := by
  rintro ⟨y, hy⟩
  rw [← h.map_commutator_fixedSubgroup hperf, ← Twisted.map_subtype_commutator,
    Subgroup.map_map] at hy
  obtain ⟨x, hx, rfl⟩ := hy
  exact ⟨⟨x, hx⟩, rfl⟩

@[expose] def derivedCentralQuotientEquiv
    (hZ : Subgroup.center ↥⁅frobFixedGroup τ L Fr, frobFixedGroup τ L Fr⁆ = ⊥) :
    TauCeti.DerivedCentralQuotient ↥(fixedSubgroup F) ≃*
      ↥⁅frobFixedGroup τ L Fr, frobFixedGroup τ L Fr⁆ :=
  MulEquiv.ofBijective
    (DerivedCentralQuotient.lift (h.derivedMap hperf) (h.derivedMap_surjective hperf) hZ)
    ⟨(injective_iff_map_eq_one _).2 fun q hq => by
      induction q using QuotientGroup.induction_on with
      | H x =>
        rw [DerivedCentralQuotient.lift_mk] at hq
        have hc := h.ker _ (congrArg Subtype.val hq)
        rw [QuotientGroup.eq_one_iff, Subgroup.mem_center_iff]
        rw [Subgroup.mem_center_iff] at hc
        intro y
        exact Subtype.ext (Subtype.ext (hc ((y : ↥(fixedSubgroup F)) : G))),
      DerivedCentralQuotient.lift_surjective _ _ _⟩

end IsIsogeny

end CFSG.TauCetiBridge.Minuscule
