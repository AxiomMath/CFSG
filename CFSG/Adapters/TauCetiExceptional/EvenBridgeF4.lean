module

public import CFSG.Adapters.TauCetiExceptional.EvenF4
public import CFSG.Adapters.TauCetiExceptional.EvenInterface
public import CFSG.Adapters.TauCetiExceptional.BridgeF4
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Assembly.LieType
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Assembly.GraphTwisted

public noncomputable section

namespace CFSG.TauCetiBridge.Even

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley TauCeti BigCell

variable (q : PrimePower) (hv : (LieTypeIndex.F4 q).Valid)

theorem nativeCarrier_F4_two
    (hp2 : q.p = 2) :
    geckMatchF4.nativeCarrier (ValidLieTypeIndex.Closure ⟨_, hv⟩) =
      adjointGroup .F4 (ValidLieTypeIndex.Closure ⟨_, hv⟩) := by
  have hp2' : ValidLieTypeIndex.characteristic ⟨_, hv⟩ = 2 := by
    rw [show ValidLieTypeIndex.characteristic ⟨_, hv⟩ = q.p from LieTypeIndex.characteristic_F4 q]
    exact hp2
  exact le_antisymm (le_adjointGroup_F4_two (p := ValidLieTypeIndex.characteristic ⟨_, hv⟩) hp2' _
      (geckMatchF4.adjointGroup_le_nativeCarrier _)
      fun _ hh => geckMatchF4.vanishes_of_mem_nativeCarrier geckRootGenerated_F4 _ hh)
    (geckMatchF4.adjointGroup_le_nativeCarrier _)

@[expose] def geckGroupEquiv_F4_two
    (hp2 : q.p = 2) :
    ↥(DynkinType.F4.geckPoints DynkinType.valid_F4 (ValidLieTypeIndex.Closure ⟨_, hv⟩)) ≃*
      ↥(adjointGroup .F4 (ValidLieTypeIndex.Closure ⟨_, hv⟩)) :=
  ((geckMatchF4.toGeck _).symm.subgroupMap
      (DynkinType.F4.geckPoints DynkinType.valid_F4 (ValidLieTypeIndex.Closure ⟨_, hv⟩))).trans
    (MulEquiv.subgroupCongr (nativeCarrier_F4_two q hv hp2))

theorem untwistedBridgeEven_F4
    : UntwistedBridgeEven .F4 LieTypeIndex.F4 := by
  intro q hv hp2 K _ _ hK
  have hq : ValidLieTypeIndex.fieldOrder ⟨_, hv⟩ = q.card := LieTypeIndex.fieldOrder_F4 q
  have hfin : ∀ d : ValidLieTypeIndex, Finite d.fixedField := fun _ => inferInstance
  have := hfin ⟨_, hv⟩
  have : IsAlgClosure (ValidLieTypeIndex.fixedField ⟨_, hv⟩)
      (ValidLieTypeIndex.Closure ⟨_, hv⟩) := by
    rw [ValidLieTypeIndex.fixedField_def]
    exact isAlgClosure_frobeniusFixedSubfield _
  have hFr : ∀ c, (ValidLieTypeIndex.frobeniusEquiv ⟨_, hv⟩).toRingHom c =
      c ^ Nat.card (ValidLieTypeIndex.fixedField ⟨_, hv⟩) := fun c => by
    rw [ValidLieTypeIndex.card_fixedField]
    exact ValidLieTypeIndex.frobeniusEquiv_apply _ c
  have hperf := commutator_adjointGroup_eq_of_singleEdge .F4
    (ValidLieTypeIndex.fixedField ⟨_, hv⟩) (Or.inl rfl)
  obtain ⟨⟨F, hF⟩, -, -, hder⟩ := Lang_Frobenius_fixed_derived_of_perfect .F4
    (ValidLieTypeIndex.fixedField ⟨_, hv⟩) hperf (ValidLieTypeIndex.Closure ⟨_, hv⟩) _ hFr
  let ψ : (UnimodularExceptionalIndex.f4 q).AmbientGroup ≃*
      ↥(adjointGroup .F4 (ValidLieTypeIndex.Closure ⟨_, hv⟩)) := geckGroupEquiv_F4_two q hv hp2
  have hψ : (ψ : (UnimodularExceptionalIndex.f4 q).AmbientGroup →*
      ↥(adjointGroup .F4 (ValidLieTypeIndex.Closure ⟨_, hv⟩))).comp
      (UnimodularExceptionalIndex.f4 q).steinberg =
        F.toMonoidHom.comp (ψ : (UnimodularExceptionalIndex.f4 q).AmbientGroup →*
          ↥(adjointGroup .F4 (ValidLieTypeIndex.Closure ⟨_, hv⟩))) := by
    refine MonoidHom.ext fun g => Subtype.ext ?_
    change (geckGroupEquiv_F4_two q hv hp2 (UnimodularExceptionalIndex.steinberg _ g) :
        ModGL .F4 (ValidLieTypeIndex.Closure ⟨_, hv⟩)) =
      (F (geckGroupEquiv_F4_two q hv hp2 g) : ModGL .F4 (ValidLieTypeIndex.Closure ⟨_, hv⟩))
    rw [hF]
    change (geckMatchF4.toGeck (ValidLieTypeIndex.Closure ⟨_, hv⟩)).symm
        ((UnimodularExceptionalIndex.f4 q).steinberg g).1 =
      Units.map _ ((geckMatchF4.toGeck (ValidLieTypeIndex.Closure ⟨_, hv⟩)).symm g.1)
    refine geckMatchF4.toGeck_symm_entrywise _ _ _ fun r s => ?_
    exact (UnimodularExceptionalIndex.coe_steinberg_apply _ g r s).trans
      (ValidLieTypeIndex.frobeniusEquiv_apply _ _).symm
  have e₁ : ValidLieTypeIndex.Group ⟨_, hv⟩ ≃* FixedPointCandidate F.toMonoidHom :=
    FixedPointCandidate.congr ψ hψ
  have hR : (fixedSubgroup F.toMonoidHom).map
      (adjointGroup .F4 (ValidLieTypeIndex.Closure ⟨_, hv⟩)).subtype =
      adjointGroup .F4 (ValidLieTypeIndex.Closure ⟨_, hv⟩) ⊓
        (Units.map (entrywiseHom (ValidLieTypeIndex.frobeniusEquiv ⟨_, hv⟩).toRingHom)).eqLocus
          (MonoidHom.id _) := by
    ext x
    constructor
    · rintro ⟨g, hg, rfl⟩
      refine ⟨g.2, ?_⟩
      have hg' : F g = g := mem_fixedSubgroup.1 hg
      change Units.map _ (g : ModGL .F4 (ValidLieTypeIndex.Closure ⟨_, hv⟩)) =
        (g : ModGL .F4 (ValidLieTypeIndex.Closure ⟨_, hv⟩))
      rw [← hF g, hg']
    · rintro ⟨hxC, hx⟩
      refine ⟨⟨x, hxC⟩, mem_fixedSubgroup.2 (Subtype.ext ((hF _).trans hx)), rfl⟩
  have e₂ : FixedPointCandidate F.toMonoidHom ≃*
      AdjointQuotient .F4 (ValidLieTypeIndex.fixedField ⟨_, hv⟩) :=
    (TauCeti.DerivedCentralQuotient.congr ((fixedSubgroup F.toMonoidHom).equivMapOfInjective
      _ (adjointGroup .F4 (ValidLieTypeIndex.Closure ⟨_, hv⟩)).subtype_injective)).trans
      (derivedCentralQuotientEquiv (algebraMap _ _) _ (by rw [hR]; exact hder))
  have : Fintype K := Fintype.ofFinite K
  have : Fintype (ValidLieTypeIndex.fixedField ⟨_, hv⟩) := Fintype.ofFinite _
  have hcardK : Fintype.card K = Fintype.card (ValidLieTypeIndex.fixedField ⟨_, hv⟩) := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hK,
      ValidLieTypeIndex.card_fixedField, hq]
  exact ⟨(adjointQuotientCongr (FiniteField.ringEquivOfCardEq hcardK)).trans
    (e₂.symm.trans e₁.symm)⟩

end CFSG.TauCetiBridge.Even
