module

public import CFSG.Adapters.TauCetiExceptional.MinusculeBridge
public import CFSG.Adapters.TauCetiExceptional.MinusculeCellE
public import CFSG.Adapters.TauCetiExceptional.MinusculeSignsE
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Assembly.LieType
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Assembly.GraphTwisted

public noncomputable section

namespace CFSG.TauCetiBridge

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Minuscule
  TauCeti BigCell Minuscule

theorem e6Data_excl : ∀ π' : Equiv.Perm (Fin (Tag.rank .E6)),
    (∀ ij : Fin (Tag.rank .E6) × Fin (Tag.rank .E6),
      Tag.cartan .E6 (π' ij.1) (π' ij.2) = Tag.cartan .E6 ij.1 ij.2) →
      (∀ a : Fin e6Data.d, ∃ b : Fin e6Data.d, ∀ j, e6Data.wt b (π' j) = e6Data.wt a j) →
        π' = 1 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem e7Data_excl : ∀ π' : Equiv.Perm (Fin (Tag.rank .E7)),
    (∀ ij : Fin (Tag.rank .E7) × Fin (Tag.rank .E7),
      Tag.cartan .E7 (π' ij.1) (π' ij.2) = Tag.cartan .E7 ij.1 ij.2) →
      (∀ a : Fin e7Data.d, ∃ b : Fin e7Data.d, ∀ j, e7Data.wt b (π' j) = e7Data.wt a j) →
        π' = 1 := by
  decide +kernel

theorem untwistedBridge_E6
    : UntwistedBridge .E6 LieTypeIndex.E6 := by
  intro q hv hp2 K _ _ hK
  have hq : ValidLieTypeIndex.fieldOrder ⟨_, hv⟩ = q.card := LieTypeIndex.fieldOrder_E6 q
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
  have hp2' : ValidLieTypeIndex.characteristic ⟨_, hv⟩ ≠ 2 := by
    rw [show ValidLieTypeIndex.characteristic ⟨_, hv⟩ = q.p from LieTypeIndex.characteristic_E6 q]
    exact hp2
  obtain ⟨e⟩ := nonempty_fixedPointCandidate_equiv e6Match.lab
    (ValidLieTypeIndex.Closure ⟨_, hv⟩) e6Data_valid posDef_cartan_E6 e6Signs_check
    (E6Minuscule.points _) (fun z hz P hP => e6_evalMat_eq_zero P hP _ z hz)
    (fun _ c => e6_toMat_mem_points _ ⟨_, e6Data_valid.xu_mem _ _ c⟩)
    (fun _ c => e6_toMat_mem_points _ ⟨_, e6Data_valid.xu_mem _ _ c⟩)
    e6Data_dominant e6Data_degOrdered (by decide) e6Data_excl (by decide) hp2'
    (TypeE6LieIndex.steinberg ⟨⟨_, hv⟩, by simp⟩)
    (ValidLieTypeIndex.frobeniusEquiv ⟨_, hv⟩).toRingHom
    (fun z r s => (TypeE6LieIndex.coe_steinberg_apply ⟨⟨_, hv⟩, by simp⟩ z r s).trans
      (ValidLieTypeIndex.frobeniusEquiv_apply ⟨_, hv⟩ _).symm)
    (ValidLieTypeIndex.fixedField ⟨_, hv⟩) hodd hFr
    (commutator_adjointGroup_eq e6Data_valid posDef_cartan_E6 e6Signs_check _
      (CFSG.LieType.CurtisTits.isPerfect_e6 _))
  have : Fintype K := Fintype.ofFinite K
  have : Fintype (ValidLieTypeIndex.fixedField ⟨_, hv⟩) := Fintype.ofFinite _
  have hcardK : Fintype.card K = Fintype.card (ValidLieTypeIndex.fixedField ⟨_, hv⟩) := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hK,
      ValidLieTypeIndex.card_fixedField, hq]
  exact ⟨(adjointQuotientCongr (FiniteField.ringEquivOfCardEq hcardK)).trans e.symm⟩

theorem untwistedBridge_E7
    : UntwistedBridge .E7 LieTypeIndex.E7 := by
  intro q hv hp2 K _ _ hK
  have hq : ValidLieTypeIndex.fieldOrder ⟨_, hv⟩ = q.card := LieTypeIndex.fieldOrder_E7 q
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
  have hp2' : ValidLieTypeIndex.characteristic ⟨_, hv⟩ ≠ 2 := by
    rw [show ValidLieTypeIndex.characteristic ⟨_, hv⟩ = q.p from LieTypeIndex.characteristic_E7 q]
    exact hp2
  obtain ⟨e⟩ := nonempty_fixedPointCandidate_equiv e7Match.lab
    (ValidLieTypeIndex.Closure ⟨_, hv⟩) e7Data_valid posDef_cartan_E7 e7Signs_check
    (E7Minuscule.points _) (fun z hz P hP => e7_evalMat_eq_zero P hP _ z hz)
    (fun _ c => e7_toMat_mem_points _ ⟨_, e7Data_valid.xu_mem _ _ c⟩)
    (fun _ c => e7_toMat_mem_points _ ⟨_, e7Data_valid.xu_mem _ _ c⟩)
    e7Data_dominant e7Data_degOrdered (by decide) e7Data_excl (by decide) hp2'
    (TypeE7LieIndex.steinberg ⟨⟨_, hv⟩, by simp⟩)
    (ValidLieTypeIndex.frobeniusEquiv ⟨_, hv⟩).toRingHom
    (fun z r s => (TypeE7LieIndex.coe_steinberg_apply ⟨⟨_, hv⟩, by simp⟩ z r s).trans
      (ValidLieTypeIndex.frobeniusEquiv_apply ⟨_, hv⟩ _).symm)
    (ValidLieTypeIndex.fixedField ⟨_, hv⟩) hodd hFr
    (commutator_adjointGroup_eq e7Data_valid posDef_cartan_E7 e7Signs_check _
      (CFSG.LieType.CurtisTits.isPerfect_e7 _))
  have : Fintype K := Fintype.ofFinite K
  have : Fintype (ValidLieTypeIndex.fixedField ⟨_, hv⟩) := Fintype.ofFinite _
  have hcardK : Fintype.card K = Fintype.card (ValidLieTypeIndex.fixedField ⟨_, hv⟩) := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hK,
      ValidLieTypeIndex.card_fixedField, hq]
  exact ⟨(adjointQuotientCongr (FiniteField.ringEquivOfCardEq hcardK)).trans e.symm⟩

end CFSG.TauCetiBridge
