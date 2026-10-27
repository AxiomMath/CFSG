module

public import CFSG.Adapters.TauCetiExceptional.ReeBridge
public import CFSG.Adapters.TauCetiExceptional.BridgeAll
public import CFSG.LocalAnalysis.QuasithinUnique.B1.Interface

public section

namespace CFSG.TauCetiBridge

open TauCeti CFSG.Blueprint CFSG.QuasithinUnique.B1 CFSG.Assembly.LowTwoRank

theorem typewiseBridges :
    TypewiseBridges where
  g2 := chevalleyBridges.g2
  f4 := chevalleyBridges.f4
  e6 := chevalleyBridges.e6
  e7 := chevalleyBridges.e7
  e8 := chevalleyBridges.e8
  twistedE6 := chevalleyBridges.twistedE6
  trialityD4 := chevalleyBridges.trialityD4
  reeG2 := reeG2Bridge

theorem models_oddLieType_of_blueprint_of_odd
    (X : Type) [Group X]
    (h : CFSG.Blueprint.OddLieType X) : CFSG.Models.OddLieType X :=
  models_oddLieType_of_blueprint typewiseBridges X h

theorem componentType_oddLieType_of_blueprint_of_odd
    (X : Type) [Group X]
    (h : CFSG.Blueprint.OddLieType X) : CFSG.Assembly.ComponentType.OddLieType X :=
  componentType_oddLieType_of_typewise typewiseBridges X h

theorem catalogBridgeFor_reeG2
    (a : ℕ) (hv : (LieTypeIndex.reeG2 a).Valid) :
    CatalogBridgeFor (.lie ⟨.reeG2 a, hv⟩) := by
  intro S _ _ _ ⟨e⟩
  have ha : 1 ≤ a := by
    have h := ((LieTypeIndex.valid_iff _).1 hv).1
    simpa [LieTypeIndex.inStandardRange_iff] using h
  have hK : Nat.card (GaloisField 3 (2 * a + 1)) = 3 ^ (2 * a + 1) :=
    GaloisField.card 3 (2 * a + 1) (by omega)
  obtain ⟨φ⟩ := reeG2Bridge a hv (GaloisField 3 (2 * a + 1)) hK
  refine Or.inr (Or.inr (Or.inr (Or.inl (Or.inr (Or.inl
    ⟨.twistedG2, 3, 2 * a + 1, by decide, ⟨Nat.prime_three, by omega, ?_⟩, a, rfl, ?_⟩)))))
  · exact ⟨rfl, rfl, ⟨a, rfl⟩, by omega⟩
  · exact ⟨GaloisField 3 (2 * a + 1), inferInstance, inferInstance, hK, ⟨e.trans φ.symm⟩⟩

end CFSG.TauCetiBridge
