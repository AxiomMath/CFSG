module

public import CFSG.HardMathSupport.Curtis.Coordinator.SeitzCyc.ReeF4Three
public import CFSG.LieType.SeitzGeneration.ExcOuterLeOne.Assembly
public import CFSG.LieType.SeitzGeneration.ExcOuterLeOne.FieldAutData
public import CFSG.LocalAnalysis.AGLEmbedding.SeitzCyc.ExcCyc
public import CFSG.LocalAnalysis.SubfieldPairReeG2.Assembly

open CFSG.LieType.SeitzGeneration
open CFSG.LieType.Chevalley
open TauCeti (LieTypeIndex)

public section

namespace CFSG.LieType.SeitzGeneration.ExcOuterLeOne


theorem seitzExcOuterNarrowE6LeOne_of_maximal (h : SubfieldMaximalLeOne .E6) :
    SeitzExcOuterNarrowE6LeOne :=
  seitzExcOuterNarrowLeOne_of_fieldAutData (c := LieTypeIndex.E6) (X := fun _ => True)
    CFSG.TauCetiBridge.Even.chevalleyBridgesAll.e6 LieTypeIndex.characteristic_E6
    (fun _ _ _ => CFSG.AGLEmbedding.SeitzEqTwo.conj_injective_adjointGroup)
    fun _ _ _ _ hp hp5 hpK hle => fieldAutData_E6_of_maximal h hp hp5 hpK hle

theorem seitzExcOuterNarrowF4LeOne_of_maximal (h : SubfieldMaximalLeOne .F4) :
    SeitzExcOuterNarrowF4LeOne :=
  seitzExcOuterNarrowLeOne_of_fieldAutData (c := LieTypeIndex.F4)
    (X := fun q => ¬ (q.p = 2 ∧ q.exponent = 1))
    CFSG.TauCetiBridge.Even.chevalleyBridgesAll.f4 LieTypeIndex.characteristic_F4
    (fun _ _ _ => CFSG.AGLEmbedding.SeitzEqTwo.conj_injective_adjointGroup)
    fun _ _ _ _ hp hp5 hpK hle => fieldAutData_F4_of_maximal h hp hp5 hpK hle

theorem seitzExcOuterNarrowE7LeOne_of_maximal (h : SubfieldMaximalLeOne .E7) :
    SeitzExcOuterNarrowE7LeOne :=
  seitzExcOuterNarrowLeOne_of_fieldAutData (c := LieTypeIndex.E7) (X := fun _ => True)
    CFSG.TauCetiBridge.Even.chevalleyBridgesAll.e7 LieTypeIndex.characteristic_E7
    (fun _ _ _ => CFSG.AGLEmbedding.SeitzEqTwo.conj_injective_adjointGroup)
    fun _ _ _ _ hp hp5 hpK hle =>
      fieldAutData_E7_of_maximal h hp hp5 hpK hle

theorem seitzExcOuterNarrowE8LeOne_of_maximal (h : SubfieldMaximalLeOne .E8) :
    SeitzExcOuterNarrowE8LeOne :=
  seitzExcOuterNarrowLeOne_of_fieldAutData (c := LieTypeIndex.E8) (X := fun _ => True)
    CFSG.TauCetiBridge.Even.chevalleyBridgesAll.e8 LieTypeIndex.characteristic_E8
    (fun _ _ _ => CFSG.AGLEmbedding.SeitzEqTwo.conj_injective_adjointGroup)
    fun _ _ _ _ hp hp5 hpK hle =>
      fieldAutData_E8_of_maximal h hp hp5 hpK hle

theorem seitzExcOuterNarrowTwistedE6LeOne_of_maximal (h : SubfieldMaximalLeOneTwE6) :
    SeitzExcOuterNarrowTwistedE6LeOne := by
  rintro ⟨d, hv⟩ p hp hp2 hpd hex E hE hc ⟨hout, -, -, hp5, q, rfl, -, hle⟩
  obtain ⟨K, _, σ, hK, hσ, ⟨e⟩⟩ := exists_catEquiv_twistedE6 q hv
  have hpq : p ≠ q.p := by simpa [TauCeti.ValidLieTypeIndex.characteristic] using hpd
  have : Finite K :=
    Nat.finite_of_card_ne_zero (by rw [hK]; exact pow_ne_zero _ (pow_ne_zero _ q.prime_p.ne_zero))
  have hinj : Function.Injective
      (MulAut.conj : twistedE6RootGroup K σ →* MulAut (twistedE6RootGroup K σ)) :=
    mulAut_conj_injective_of_center_eq_bot (center_graphFixedRootGroup_eq_bot σ.surjective)
  have hle' : degCountTw (orderOf (((q.p ^ q.exponent : ℕ)) : ZMod p)) ≤ 1 := by
    rwa [← TauCeti.PrimePower.card_def]
  exact planeGen_outer_of_fieldAutData hinj e hp
    (fieldAutData_twE6_of_maximal h q.prime_p q.exponent_pos hK σ hσ hp hp5 hpq hle') hE hc hout

theorem seitzExcOuterCycResiduals_of_maximal
    (hF4 : SubfieldMaximalLeOne .F4) (hE6 : SubfieldMaximalLeOne .E6)
    (hE7 : SubfieldMaximalLeOne .E7) (hE8 : SubfieldMaximalLeOne .E8)
    (hTw : SubfieldMaximalLeOneTwE6) :
    CFSG.AGLEmbedding.SeitzCyc.SeitzExcOuterCycResiduals :=
  ⟨seitzExcOuterNarrowF4LeOne_of_maximal hF4, seitzExcOuterNarrowE6LeOne_of_maximal hE6,
    seitzExcOuterNarrowE7LeOne_of_maximal hE7, seitzExcOuterNarrowE8LeOne_of_maximal hE8,
    seitzExcOuterNarrowTwistedE6LeOne_of_maximal hTw,
    CFSG.HardMathSupport.Curtis.Coordinator.SeitzCyc.seitzExcOuterNarrowReeG2_of_pair
      CFSG.LocalAnalysis.SubfieldPairReeG2.subfieldPairReeG2_of_pieces,
    CFSG.LieType.SeitzGeneration.seitzExcOuterNarrowReeF4Three_holds⟩

end CFSG.LieType.SeitzGeneration.ExcOuterLeOne
