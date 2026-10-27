module

public import CFSG.Adapters.TauCetiExceptional.ReeModel
public import CFSG.Adapters.TauCetiExceptional.ReeSteinberg
public import CFSG.Adapters.TauCetiExceptional.BigCellG2Three
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Assembly.LieType
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Assembly.AmbientGroup

public noncomputable section

namespace CFSG.TauCetiBridge

open CFSG.Blueprint CFSG.Blueprint.Chevalley TauCeti CFSG.TauCetiBridge.BigCell

namespace Ree

variable (a : ℕ) (hv : (LieTypeIndex.reeG2 a).Valid)

theorem zerosInAdjoint_closure :
    ZerosInAdjoint (ReeG2LieIndex.of a hv).1.Closure :=
  fun H hCH hH => le_adjointGroup_G2 (p := (ReeG2LieIndex.of a hv).1.characteristic)
    (by rw [ReeG2LieIndex.characteristic_eq_three]; decide) H hCH hH

theorem isReeSteinberg_steinberg :
    IsReeSteinberg a (ReeG2LieIndex.of a hv).steinberg :=
  steinberg_rootSubgroupPoints a hv

theorem finite_fixedField_reeG2 : Finite (ValidLieTypeIndex.fixedField ⟨.reeG2 a, hv⟩) := by
  have hfin : ∀ d : ValidLieTypeIndex, Finite d.fixedField := fun _ => inferInstance
  exact hfin _

theorem isAlgClosure_fixedField_reeG2 :
    IsAlgClosure (ValidLieTypeIndex.fixedField ⟨.reeG2 a, hv⟩)
      (ReeG2LieIndex.of a hv).1.Closure := by
  rw [ValidLieTypeIndex.fixedField_def]
  exact isAlgClosure_frobeniusFixedSubfield _

theorem card_fixedField_reeG2 :
    Nat.card (ValidLieTypeIndex.fixedField ⟨.reeG2 a, hv⟩) = 3 ^ (2 * a + 1) :=
  (ValidLieTypeIndex.card_fixedField _).trans (LieTypeIndex.fieldOrder_reeG2 a)

end Ree

open Ree in
theorem reeG2Bridge :
    ReeG2Bridge := by
  intro a hv K _ _ hK
  have : Fintype K := Fintype.ofFinite K
  have : CharP K 3 := charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card, hK])
  have := finite_fixedField_reeG2 a hv
  have : Fintype (ValidLieTypeIndex.fixedField ⟨.reeG2 a, hv⟩) := Fintype.ofFinite _
  have := isAlgClosure_fixedField_reeG2 a hv
  have : Algebra.IsAlgebraic (ValidLieTypeIndex.fixedField ⟨.reeG2 a, hv⟩)
      (ReeG2LieIndex.of a hv).1.Closure := IsAlgClosure.isAlgebraic
  have hcard : Fintype.card K = Fintype.card (ValidLieTypeIndex.fixedField ⟨.reeG2 a, hv⟩) := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hK, card_fixedField_reeG2]
  let e : K ≃+* ValidLieTypeIndex.fixedField ⟨.reeG2 a, hv⟩ := FiniteField.ringEquivOfCardEq hcard
  let _ : Algebra K (ReeG2LieIndex.of a hv).1.Closure :=
    ((ValidLieTypeIndex.fixedField ⟨.reeG2 a, hv⟩).subtype.comp e.toRingHom).toAlgebra
  have : Algebra.IsAlgebraic K (ReeG2LieIndex.of a hv).1.Closure :=
    Algebra.IsAlgebraic.of_ringHom_of_comp_eq e (RingHom.id _) e.surjective
      Function.injective_id rfl
  obtain ⟨φ⟩ := nonempty_reeModel_equiv (K := K) (L := (ReeG2LieIndex.of a hv).1.Closure)
    (zerosInAdjoint_closure a hv) (isReeSteinberg_steinberg a hv)
    (steinberg_steinberg_eq_frobenius a hv) hK
  exact ⟨φ⟩

end CFSG.TauCetiBridge
