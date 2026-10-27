module

public import CFSG.HardMathSupport.Curtis.Coordinator.SeitzOuter.FixPlaneOrth
public import CFSG.HardMathSupport.Curtis.Coordinator.SeitzOuter.OuterCubeSymplectic

public section

namespace CFSG.HardMathSupport.Curtis.Coordinator.SeitzOuter

open CFSG.Open (IsElemAbelian)
open CFSG.LieType.SeitzGeneration CFSG.AGLEmbedding CFSG.RankThree.PartOne.CTP

theorem fieldAutData_orthogonal_index (hpair : SubfieldPairOmega) {d : TauCeti.ValidLieTypeIndex}
    (hd : IsOrthogonalIndex d.1) {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hpd : p ≠ d.1.characteristic) : FieldAutData (Cat d) p := by
  have := finite_cat_orthogonal hd
  obtain ⟨d, hv⟩ := d
  have hrange := (TauCeti.LieTypeIndex.inStandardRange_iff _).1
    ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
  rcases hd with ⟨r, q, rfl, hr3, hq⟩ | ⟨r, q, rfl⟩ | ⟨r, q, rfl⟩
  · have hq' : p ≠ q.p := by simpa using hpd
    let e := CFSG.RankThree.PartTwo.Census.Carrier.SpinB.typeBGroupEquivStatedProj_odd r q hv hq
      hr3
    have : Finite ↥(TauCeti.ValidLieTypeIndex.fixedField ⟨.B r q, hv⟩) :=
      CFSG.QuasithinUnique.SQTK.finite_validIndex_fixedField _
    have hcardK : Nat.card ↥(TauCeti.ValidLieTypeIndex.fixedField ⟨.B r q, hv⟩) =
        q.p ^ q.exponent := by
      rw [card_fixedField_eq]
      simp [TauCeti.ValidLieTypeIndex.characteristic, TauCeti.ValidLieTypeIndex.fieldExponent]
    exact fieldAutData_of_model hpair (Or.inl rfl) (n := r) (ℓ := q.p) (f := q.exponent)
      ⟨⟨q.prime_p, q.exponent_pos, hr3, hq⟩, _, inferInstance, inferInstance, hcardK, ⟨e⟩⟩ hp hp3
      hq'
  · have hq' : p ≠ q.p := by simpa using hpd
    have hr4 : 4 ≤ r := hrange
    let e := CFSG.RankThree.PartTwo.Census.Carrier.SpinD.typeDGroupEquivStatedProj_of_valid r q hv
    have : Finite ↥(TauCeti.ValidLieTypeIndex.fixedField ⟨.D r q, hv⟩) :=
      CFSG.QuasithinUnique.SQTK.finite_validIndex_fixedField _
    have hcardK : Nat.card ↥(TauCeti.ValidLieTypeIndex.fixedField ⟨.D r q, hv⟩) =
        q.p ^ q.exponent := by
      rw [card_fixedField_eq]
      simp [TauCeti.ValidLieTypeIndex.characteristic, TauCeti.ValidLieTypeIndex.fieldExponent]
    exact fieldAutData_of_model hpair (Or.inr (Or.inl rfl)) (n := r) (ℓ := q.p)
      (f := q.exponent)
      ⟨⟨q.prime_p, q.exponent_pos, hr4⟩, _, inferInstance, inferInstance, hcardK, ⟨e⟩⟩ hp hp3 hq'
  · have hq' : p ≠ q.p := by simpa using hpd
    have hr4 : 4 ≤ r := hrange
    obtain ⟨b, c', hirr, ⟨e⟩⟩ :=
      CFSG.RankThree.PartTwo.Census.Carrier.SpinD.exists_typeTwistedDGroupEquivStatedProj_of_valid
        r q hv
    have : Finite ↥(TauCeti.ValidLieTypeIndex.fixedField ⟨.twistedD r q, hv⟩) :=
      CFSG.QuasithinUnique.SQTK.finite_validIndex_fixedField _
    have hcardK : Nat.card ↥(TauCeti.ValidLieTypeIndex.fixedField ⟨.twistedD r q, hv⟩) =
        q.p ^ q.exponent := by
      rw [card_fixedField_eq]
      simp [TauCeti.ValidLieTypeIndex.characteristic, TauCeti.ValidLieTypeIndex.fieldExponent]
    exact fieldAutData_of_model hpair (Or.inr (Or.inr rfl)) (n := r) (ℓ := q.p)
      (f := q.exponent)
      ⟨⟨q.prime_p, q.exponent_pos, hr4⟩, _, inferInstance, inferInstance, hcardK, b, c', hirr,
        ⟨e⟩⟩ hp hp3 hq'

theorem kFactSeitzOuterCubeRankTwoAtPrime_orthogonal
    (hpair : SubfieldPairOmega) (hNJ : OrthFixedLeDerivedAll)
    {d : TauCeti.ValidLieTypeIndex} (hd : IsOrthogonalIndex d.1) {p : ℕ} [Fact p.Prime] :
    KFactSeitzOuterCubeRankTwoAtPrime d p :=
  kFactSeitzOuterCubeRankTwoAtPrime_of_fieldAutData_odd fun hp2 hpd _ hno => by
    have hp : p.Prime := Fact.out
    by_cases hp3 : 3 < p
    · exact ⟨fieldAutData_orthogonal_index hpair hd hp hp3 hpd,
        fixPlaneGen_orthogonal_index hd hp2 hpd hNJ hno⟩
    · exfalso
      have := finite_cat_orthogonal hd
      have hp3' : p = 3 := by
        have := hp.two_le
        interval_cases p <;> first | rfl | omega
      subst hp3'
      exact not_rankLE2_orthogonal_three d hd (rankLE2_of_not_exists_cube hp hno)

end CFSG.HardMathSupport.Curtis.Coordinator.SeitzOuter
