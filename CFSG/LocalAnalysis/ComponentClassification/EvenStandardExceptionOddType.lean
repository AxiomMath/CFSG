module

public import CFSG.Blueprint.EvenStandardExact
public import CFSG.Blueprint.OddStandardExact
import CFSG.LocalAnalysis.ComponentClassification.StandardRecognitionTypeExceptions
import CFSG.Monster.Existence.Compat.Sp8
import CFSG.Quasithin.EmptyFaithfulMultiple.G2TwoUnitary

public section

namespace CFSG.Blueprint.Recognition.Exact

noncomputable def commutatorCongrEquiv {A B : Type*} [Group A] [Group B] (e : A ≃* B) :
    commutator A ≃* commutator B :=
  (e.subgroupMap (commutator A)).trans (MulEquiv.subgroupCongr (by
    rw [commutator_def, commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
      MonoidHom.range_eq_top.2 e.surjective]))

theorem evenStandardException_oddStandardType
    (X : Type) [Group X] (h : EvenStandardException X) :
    OddStandardType X := by
  rcases h with h | h | h | ⟨K, _, _, hK, ⟨e⟩⟩ | ⟨K, _, _, hK, ⟨e⟩⟩ | h | h | h
  · exact .inl ⟨5, le_rfl, CFSG.LocalAnalysis.ComponentInitial.PSL2_four_alternating_five_model X h⟩
  · exact .inr (.inl ⟨.PSL, 2, 7, 1, Nat.prime_seven, by decide,
      ⟨Nat.prime_seven, le_rfl, le_rfl, by decide, by decide⟩,
      CFSG.LocalAnalysis.ComponentInitial.PSL3_two_PSL2_seven_paired_isomorphism X h⟩)
  · exact .inl ⟨8, by norm_num,
      (CFSG.ComponentClassification.SymmetricLocal.lie_model_linear_four_two_iff X).1 h⟩
  · have hK2 : Nat.card K = 2 := by rw [Nat.card_eq_fintype_card, hK]
    exact .inl ⟨6, by norm_num, ⟨e.trans ((commutatorCongrEquiv
      (CFSG.Monster.Existence.Compat.sympMapEquiv
        (CFSG.Monster.Existence.Compat.ringEquivZMod2 hK2))).trans
          CFSG.ComponentClassification.StandardRecognition.symplecticCommutatorEquivAlternating)⟩⟩
  · have hK2 : Nat.card K = 2 := by rw [Nat.card_eq_fintype_card, hK]
    exact .inr (.inl ⟨.PSU, 3, 3, 1, Nat.prime_three, by decide,
      ⟨Nat.prime_three, le_rfl, le_rfl, by decide⟩, LieModel.of_mulEquiv e.symm
        (CFSG.Quasithin.EmptyFaithfulMultiple.g2TwoDerivedUnitaryTransport_holds K hK2)⟩)
  · exact .inr (.inl ⟨.PSp, 2, 3, 1, Nat.prime_three, by decide,
      ⟨Nat.prime_three, le_rfl, le_rfl, by decide⟩,
      CFSG.GH74.Exceptional.lieModel_PSp_two_three_of_lieModel_PSU_four_two h⟩)
  · exact .inr (.inr (.inl h))
  · exact .inr (.inr (.inr h))

end CFSG.Blueprint.Recognition.Exact
