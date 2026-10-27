module

import all TauCeti.GroupTheory.SpecificGroups.CFSG.Assembly.LieType
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Assembly.AmbientGroup
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Classification
public import CFSG.LieType.SeitzGeneration.Defs
public import CFSG.RankThree.PartTwo.Census.Carrier.ReeF4Catalog
public import CFSG.Sporadic.Schreier.TitsOuter

public section

namespace CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.TitsAux

open CFSG.Blueprint TauCeti CFSG.LieType.SeitzGeneration CFSG.Sporadic.Schreier.Tits

section Tits


theorem nonempty_mulEquiv_titsD_cat (hv : LieTypeIndex.tits.Valid) :
    Nonempty (Cat ⟨.tits, hv⟩ ≃* titsD) := by
  have hfin : ∀ d : TitsLieIndex, Finite d.1.fixedField := fun _ => inferInstance
  have hchar : ∀ d : TitsLieIndex, CharP d.1.fixedField 2 := fun _ => inferInstance
  have := hfin TitsLieIndex.of
  have := hchar TitsLieIndex.of
  obtain ⟨e₁⟩ := CFSG.TauCetiBridge.ReeF4.nonempty_candidate_equiv_tits TitsLieIndex.of
  have hmodel : ReeTitsModel (Cat ⟨.tits, hv⟩) .Tits 2 1 :=
    ⟨⟨Nat.prime_two, le_rfl, ⟨rfl, rfl, rfl⟩⟩, 0, rfl,
      ⟨TitsLieIndex.of.1.fixedField, inferInstance, inferInstance,
        (CFSG.TauCetiBridge.ReeF4.card_fixedField_tits _).trans (pow_one 2).symm,
        ⟨e₁.trans (CFSG.TauCetiBridge.ReeF4.nativeModelEquiv 0).symm⟩⟩⟩
  exact titsModelEquiv _ 2 1 hmodel

end Tits

end CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.TitsAux
