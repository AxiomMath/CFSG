module

public import CFSG.Adapters.TauCetiExceptional.BridgeTransport
public import CFSG.Adapters.TauCetiExceptional.BigCellG2Three
public import CFSG.Adapters.TauCetiExceptional.GeckG2
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.GeckLattice.SchemeGeneration
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Assembly.LieType
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Assembly.GraphTwisted

public noncomputable section

namespace CFSG.TauCetiBridge

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley TauCeti BigCell

theorem geckRootGenerated_G2 : GeckRootGenerated DynkinType.G2 DynkinType.valid_G2 :=
  DynkinType.geckDefiningIdeal_eq_kostantGeneratedDefiningIdeal_G2

variable (q : PrimePower) (hv : (LieTypeIndex.G2 q).Valid)

theorem nativeCarrier_G2
    (hp2 : q.p ≠ 2) :
    geckMatchG2.nativeCarrier (ValidLieTypeIndex.Closure ⟨_, hv⟩) =
      adjointGroup .G2 (ValidLieTypeIndex.Closure ⟨_, hv⟩) := by
  have hp2' : (ValidLieTypeIndex.characteristic ⟨_, hv⟩) ≠ 2 := by
    rw [show ValidLieTypeIndex.characteristic ⟨_, hv⟩ = q.p from LieTypeIndex.characteristic_G2 q]
    exact hp2
  exact le_antisymm (le_adjointGroup_G2 (p := ValidLieTypeIndex.characteristic ⟨_, hv⟩) hp2' _
      (geckMatchG2.adjointGroup_le_nativeCarrier _)
      fun _ hh => geckMatchG2.vanishes_of_mem_nativeCarrier geckRootGenerated_G2 _ hh)
    (geckMatchG2.adjointGroup_le_nativeCarrier _)

@[expose] def geckGroupEquiv_G2
    (hp2 : q.p ≠ 2) :
    ↥(DynkinType.G2.geckPoints DynkinType.valid_G2 (ValidLieTypeIndex.Closure ⟨_, hv⟩)) ≃*
      ↥(adjointGroup .G2 (ValidLieTypeIndex.Closure ⟨_, hv⟩)) :=
  ((geckMatchG2.toGeck _).symm.subgroupMap
      (DynkinType.G2.geckPoints DynkinType.valid_G2 (ValidLieTypeIndex.Closure ⟨_, hv⟩))).trans
    (MulEquiv.subgroupCongr (nativeCarrier_G2 q hv hp2))

theorem coe_geckGroupEquiv_G2
    (hp2 : q.p ≠ 2)
    (g : ↥(DynkinType.G2.geckPoints DynkinType.valid_G2 (ValidLieTypeIndex.Closure ⟨_, hv⟩))) :
    (geckGroupEquiv_G2 q hv hp2 g : ModGL .G2 (ValidLieTypeIndex.Closure ⟨_, hv⟩)) =
      (geckMatchG2.toGeck _).symm (g : Matrix.GeneralLinearGroup
        (Fin (DynkinType.G2.geckDim DynkinType.valid_G2)) (ValidLieTypeIndex.Closure ⟨_, hv⟩)) :=
  rfl

theorem untwistedBridge_G2 :
    UntwistedBridge .G2 LieTypeIndex.G2 := by
  intro q hv hp2 K _ _ hK
  have hq3 : 3 ≤ q.card :=
    (LieTypeIndex.inStandardRange_iff _).1 ((LieTypeIndex.valid_iff _).1 hv).1
  have hq : ValidLieTypeIndex.fieldOrder ⟨_, hv⟩ = q.card := LieTypeIndex.fieldOrder_G2 q
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
  have hodd : Odd (Nat.card (ValidLieTypeIndex.fixedField ⟨_, hv⟩)) := by
    rw [ValidLieTypeIndex.card_fixedField, hq, PrimePower.card_def]
    exact (q.prime_p.odd_of_ne_two hp2).pow
  obtain ⟨⟨F, hF⟩, -, -, hder⟩ := exceptional_Lang_Frobenius_fixed_derived_root_group .G2
    (ValidLieTypeIndex.fixedField ⟨_, hv⟩) hodd (ValidLieTypeIndex.Closure ⟨_, hv⟩) _ hFr
  let ψ : (UnimodularExceptionalIndex.g2 q hq3).AmbientGroup ≃*
      ↥(adjointGroup .G2 (ValidLieTypeIndex.Closure ⟨_, hv⟩)) := geckGroupEquiv_G2 q hv hp2
  have hψ : (ψ : (UnimodularExceptionalIndex.g2 q hq3).AmbientGroup →*
      ↥(adjointGroup .G2 (ValidLieTypeIndex.Closure ⟨_, hv⟩))).comp
      (UnimodularExceptionalIndex.g2 q hq3).steinberg =
        F.toMonoidHom.comp (ψ : (UnimodularExceptionalIndex.g2 q hq3).AmbientGroup →*
          ↥(adjointGroup .G2 (ValidLieTypeIndex.Closure ⟨_, hv⟩))) := by
    refine MonoidHom.ext fun g => Subtype.ext ?_
    change (geckGroupEquiv_G2 q hv hp2 (UnimodularExceptionalIndex.steinberg _ g) :
        ModGL .G2 (ValidLieTypeIndex.Closure ⟨_, hv⟩)) =
      (F (geckGroupEquiv_G2 q hv hp2 g) : ModGL .G2 (ValidLieTypeIndex.Closure ⟨_, hv⟩))
    rw [hF]
    change (geckMatchG2.toGeck (ValidLieTypeIndex.Closure ⟨_, hv⟩)).symm
        ((UnimodularExceptionalIndex.g2 q hq3).steinberg g).1 =
      Units.map _ ((geckMatchG2.toGeck (ValidLieTypeIndex.Closure ⟨_, hv⟩)).symm g.1)
    refine geckMatchG2.toGeck_symm_entrywise _ _ _ fun r s => ?_
    exact (UnimodularExceptionalIndex.coe_steinberg_apply _ g r s).trans
      (ValidLieTypeIndex.frobeniusEquiv_apply _ _).symm
  have e₁ : ValidLieTypeIndex.Group ⟨_, hv⟩ ≃* FixedPointCandidate F.toMonoidHom :=
    FixedPointCandidate.congr ψ hψ
  have hR : (fixedSubgroup F.toMonoidHom).map
      (adjointGroup .G2 (ValidLieTypeIndex.Closure ⟨_, hv⟩)).subtype =
      adjointGroup .G2 (ValidLieTypeIndex.Closure ⟨_, hv⟩) ⊓
        (Units.map (entrywiseHom (ValidLieTypeIndex.frobeniusEquiv ⟨_, hv⟩).toRingHom)).eqLocus
          (MonoidHom.id _) := by
    ext x
    constructor
    · rintro ⟨g, hg, rfl⟩
      refine ⟨g.2, ?_⟩
      have hg' : F g = g := mem_fixedSubgroup.1 hg
      change Units.map _ (g : ModGL .G2 (ValidLieTypeIndex.Closure ⟨_, hv⟩)) =
        (g : ModGL .G2 (ValidLieTypeIndex.Closure ⟨_, hv⟩))
      rw [← hF g, hg']
    · rintro ⟨hxC, hx⟩
      refine ⟨⟨x, hxC⟩, mem_fixedSubgroup.2 (Subtype.ext ((hF _).trans hx)), rfl⟩
  have e₂ : FixedPointCandidate F.toMonoidHom ≃*
      AdjointQuotient .G2 (ValidLieTypeIndex.fixedField ⟨_, hv⟩) :=
    (TauCeti.DerivedCentralQuotient.congr ((fixedSubgroup F.toMonoidHom).equivMapOfInjective
      _ (adjointGroup .G2 (ValidLieTypeIndex.Closure ⟨_, hv⟩)).subtype_injective)).trans
      (derivedCentralQuotientEquiv (algebraMap _ _) _ (by rw [hR]; exact hder))
  have : Fintype K := Fintype.ofFinite K
  have : Fintype (ValidLieTypeIndex.fixedField ⟨_, hv⟩) := Fintype.ofFinite _
  have hcardK : Fintype.card K = Fintype.card (ValidLieTypeIndex.fixedField ⟨_, hv⟩) := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hK,
      ValidLieTypeIndex.card_fixedField, hq]
  exact ⟨(adjointQuotientCongr (FiniteField.ringEquivOfCardEq hcardK)).trans
    (e₂.symm.trans e₁.symm)⟩

end CFSG.TauCetiBridge
