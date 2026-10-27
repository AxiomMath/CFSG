module

public import CFSG.HardMathSupport.Curtis.Coordinator.SeitzOuter.FixPlaneSpIndex
public import CFSG.LieType.SeitzGeneration.SpF2.Main
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanP1ThreeLieOffCharOuterCube

public section

namespace CFSG.HardMathSupport.Curtis.Coordinator.SeitzOuter

open CFSG.Open CFSG.LieType.SeitzGeneration CFSG.AGLEmbedding CFSG.RankThree.PartOne.CTP

theorem fieldAutData_symplectic_index
    {d : TauCeti.ValidLieTypeIndex} (hd : IsSymplecticIndex d.1) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) : FieldAutData (Cat d) p := by
  have hpair : SubfieldPairSpOdd := subfieldPairSpOdd subfieldPairSpF2_holds
  obtain ⟨d, hv⟩ := d
  have hrange := (TauCeti.LieTypeIndex.inStandardRange_iff _).1
    ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
  rcases hd with ⟨q, rfl⟩ | ⟨r, q, rfl, hr3, hq2⟩ | ⟨r, q, rfl⟩
  · have : Finite ↥(TauCeti.ValidLieTypeIndex.fixedField ⟨.B 2 q, hv⟩) :=
      CFSG.QuasithinUnique.SQTK.finite_validIndex_fixedField _
    exact (fieldAutData_projectiveSp_odd hpair (le_refl 2) q.prime_p q.exponent_pos
      (CFSG.RankThree.PartOne.CTP.card_fixedField_B 2 q hv) hp hp2).of_mulEquiv
      (CFSG.QuasithinUnique.SQTK.typeB2GroupEquivStatedProj q hv) hp
  · have : Finite ↥(TauCeti.ValidLieTypeIndex.fixedField ⟨.B r q, hv⟩) :=
      CFSG.QuasithinUnique.SQTK.finite_validIndex_fixedField _
    exact (fieldAutData_projectiveSp_odd hpair (by omega : 2 ≤ r) q.prime_p q.exponent_pos
      (CFSG.RankThree.PartOne.CTP.card_fixedField_B r q hv) hp hp2).of_mulEquiv
      (CFSG.RankThree.PartTwo.Census.Carrier.SpinB.typeBGroupEquivStatedProj r q hv hq2 hr3) hp
  · have : Finite ↥(TauCeti.ValidLieTypeIndex.fixedField ⟨.C r q, hv⟩) :=
      CFSG.QuasithinUnique.SQTK.finite_validIndex_fixedField _
    exact (fieldAutData_projectiveSp_odd hpair (by omega : 2 ≤ r) q.prime_p q.exponent_pos
      (card_fixedField_C r q hv) hp hp2).of_mulEquiv
      (CFSG.QuasithinUnique.SQTK.typeCGroupEquivStatedProj r q hv) hp

theorem kFactSeitzOuterCubeRankTwoAtPrime_of_fieldAutData_odd {d : TauCeti.ValidLieTypeIndex}
    {p : ℕ} [Fact p.Prime]
    (h : p ≠ 2 → p ≠ d.1.characteristic → ¬ P1ThreeLieList p d →
      (¬ ∃ E : Subgroup (TauCeti.CFSGIndex.lie d).Group, IsElemAbelian p E ∧
        Nat.card E = p ^ 3) →
      FieldAutData (TauCeti.CFSGIndex.lie d).Group p ∧
        FixPlaneGen (TauCeti.CFSGIndex.lie d).Group p) :
    KFactSeitzOuterCubeRankTwoAtPrime d p := by
  intro hp2 Y _ _ K hKn hC he hpd hl hno E hE hc
  have hp : p.Prime := Fact.out
  obtain ⟨e⟩ := he
  have : K.Normal := hKn
  have hnoC : ¬ ∃ E : Subgroup (TauCeti.CFSGIndex.lie d).Group, IsElemAbelian p E ∧
      Nat.card E = p ^ 3 := by
    rintro ⟨E', hE', hc'⟩
    refine hno ⟨(E'.map e.symm.toMonoidHom).map K.subtype, Subgroup.map_subtype_le _,
      CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_map p
        (CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_map p hE' _) _, ?_⟩
    rw [Subgroup.card_map_of_injective K.subtype_injective,
      Subgroup.card_map_of_injective e.symm.injective, hc']
  obtain ⟨hF, hP⟩ := h hp2 hpd hl hnoC
  exact hyperGen_of_fieldAutData hC hno (hF.of_mulEquiv e hp) (hP.of_mulEquiv e hp) hE hc

theorem kFactSeitzOuterCubeRankTwoAtPrime_symplectic
    {d : TauCeti.ValidLieTypeIndex} (hd : IsSymplecticIndex d.1) {p : ℕ} [Fact p.Prime] :
    KFactSeitzOuterCubeRankTwoAtPrime d p :=
  kFactSeitzOuterCubeRankTwoAtPrime_of_fieldAutData_odd fun hp2 hpd hl hno =>
    ⟨fieldAutData_symplectic_index hd Fact.out hp2, fixPlaneGen_symplectic_index hd hp2 hpd hl hno⟩

end CFSG.HardMathSupport.Curtis.Coordinator.SeitzOuter
