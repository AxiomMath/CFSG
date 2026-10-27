module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I137Core3Defs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Blueprint.SourceClassicalTransportLinear
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.UnitaryTauCeti
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I137C3

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 TauCeti

@[expose] def pp2 : PrimePower := ⟨2, 1, Nat.prime_two, Nat.one_pos⟩

theorem valid_twistedA_five : (LieTypeIndex.twistedA 5 pp2).Valid := by
  rw [LieTypeIndex.valid_iff, LieTypeIndex.inStandardRange_iff,
    LieTypeIndex.isDuplicateRepresentative_iff]
  simp [pp2]

theorem nonempty_equiv_u6two_of_statedProj {X : Type} [Group X] {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 4) (e : X ≃* StatedProj (StatedSU 6 (2 ^ 1) K)) :
    Nonempty (X ≃* (CFSGIndex.lie ⟨.twistedA 5 pp2, valid_twistedA_five⟩).Group) := by
  have hc2 : ValidLieTypeIndex.characteristic ⟨.twistedA 5 pp2, valid_twistedA_five⟩ = 2 :=
    LieTypeIndex.characteristic_twistedA 5 pp2
  have hf2 : ValidLieTypeIndex.fieldExponent ⟨.twistedA 5 pp2, valid_twistedA_five⟩ = 1 :=
    LieTypeIndex.fieldExponent_twistedA 5 pp2
  have eq := CFSG.QuasithinUnique.SQTK.typeTwistedAGroupEquivStatedProj 5 pp2
    valid_twistedA_five
  have hq : ValidLieTypeIndex.characteristic ⟨.twistedA 5 pp2, valid_twistedA_five⟩ ^
      ValidLieTypeIndex.fieldExponent ⟨.twistedA 5 pp2, valid_twistedA_five⟩ = 2 ^ 1 := by
    rw [hc2, hf2]
  rw [← hq] at e
  haveI : Fintype K := Fintype.ofFinite K
  haveI : Fintype (GaloisField (ValidLieTypeIndex.characteristic
    ⟨.twistedA 5 pp2, valid_twistedA_five⟩)
      (2 * ValidLieTypeIndex.fieldExponent ⟨.twistedA 5 pp2, valid_twistedA_five⟩)) :=
    Fintype.ofFinite _
  have hc : Fintype.card K = Fintype.card (GaloisField (ValidLieTypeIndex.characteristic
      ⟨.twistedA 5 pp2, valid_twistedA_five⟩)
        (2 * ValidLieTypeIndex.fieldExponent ⟨.twistedA 5 pp2, valid_twistedA_five⟩)) := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hK,
      GaloisField.card _ _ (by rw [hf2]; norm_num), hc2, hf2]
    norm_num
  exact ⟨(e.trans (CFSG.Open.StatedSUFieldChange.statedProjSUEquiv
    (FiniteField.ringEquivOfCardEq hc) 6 _)).trans eq.symm⟩

theorem core3Group_of_SU6cover
    (hu62 : Core3At fun d => ∃ q : PrimePower, d = .twistedA 5 q ∧ q.card = 2)
    (Q : Type) [Group Q] [Finite Q] (hL : FullLinearCover true 6 2 Q) :
    Core3Group (Q ⧸ Subgroup.center Q) := by
  obtain ⟨K, _, _, h⟩ := hL
  rw [if_pos rfl] at h
  obtain ⟨hK, ⟨e⟩⟩ := h
  have hK' : Nat.card K = (2 ^ 1) ^ 2 := by rw [hK]; norm_num
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hZ := (CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU
    (CFSG.ClassicalGroups.Unitary.isPerfect_statedSU hK' (by norm_num) (by decide))
    (CFSG.ClassicalGroups.Unitary.isSimpleGroup_statedProj_statedSU K 2 1 hK' 6 (by norm_num)
      (by decide))).2
  let e1 : (Q ⧸ Subgroup.center Q) ≃* StatedProj (StatedSU 6 (2 ^ 1) K) :=
    (QuotientGroup.congr _ _ e (Subgroup.map_center_eq e)).trans
      (QuotientGroup.quotientMulEquivOfEq hZ)
  obtain ⟨e2⟩ := nonempty_equiv_u6two_of_statedProj (by rw [hK]; norm_num) e1
  have hq : pp2.card = 2 := by
    rw [PrimePower.card_def]
    norm_num [pp2]
  exact hu62 ⟨.twistedA 5 pp2, valid_twistedA_five⟩ ⟨pp2, rfl, hq⟩ _ ⟨e2⟩

end CFSG.LocalAnalysis.GLTheoremA.I137C3

end
