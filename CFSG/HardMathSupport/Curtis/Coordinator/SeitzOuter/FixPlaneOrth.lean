module

public import CFSG.HardMathSupport.Curtis.Coordinator.SeitzOuter.FixPlaneOrthOdd
public import CFSG.HardMathSupport.Curtis.Coordinator.SeitzOuter.FixPlaneOrthMinus
public import CFSG.HardMathSupport.Curtis.Coordinator.SeitzOuter.RankCube
public import CFSG.LieType.SeitzGeneration.ThreeIndepOrth

public section

namespace CFSG.HardMathSupport.Curtis.Coordinator.SeitzOuter

open Matrix Subgroup CFSG.RankThree.PartOne.KCOrthogonalSubfield
  CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData CFSG.LieType.SeitzGeneration
  CFSG.AGLEmbeddingD2
open CFSG.RankThree.PartOne.CTP (IsOuterOfOrder)
open CFSG.Open (IsElemAbelian)
open CFSG.Assembly.LowTwoRank (StatedProj StatedOmega StatedQuadOdd StatedQuadPlus
  StatedQuadMinus StatedLieAdmissible StatedClassicalModel)

theorem fixPlaneGen_minus_of_model
    {G : Type} [Group G] [Finite G] {n ℓ f p : ℕ}
    (hM : StatedClassicalModel G .POmegaMinus n ℓ f) (hp : p.Prime) (hp3 : 3 < p)
    (hpℓ : p ≠ ℓ) (hNJ : ∀ e, OrthFixedLeDerived .POmegaMinus n ℓ e p) (hrk : RankLE2 p G) :
    FixPlaneGen G p := by
  obtain ⟨hℓ, hf, hn⟩ := id hM.1
  have hn1 : 1 ≤ n := by omega
  by_cases hex : ∃ α : MulAut G, IsOuterOfOrder p α
  · obtain ⟨α, hα⟩ := hex
    obtain ⟨e, K, _, _, k, σ, b, c, he, -, hk, hK, hσ, hfix, hirr, ⟨ψ⟩⟩ :=
      exists_rational_model_minus hn1 hM hp hp3 hpℓ hα
    exact FixPlaneGen.of_mulEquiv ψ hp
      (fixPlaneGen_minus_rational hn hn1 hℓ he hp hp3 hpℓ hk hK hσ hfix b c hirr (hNJ e)
        (rankLE2_of_injective ψ.symm.toMonoidHom ψ.symm.injective hrk))
  · intro σ hσ
    exact absurd ⟨σ, hσ⟩ hex

theorem finite_cat_orthogonal {d : TauCeti.ValidLieTypeIndex} (hd : IsOrthogonalIndex d.1) :
    Finite (Cat d) := by
  obtain ⟨d, hv⟩ := d
  rcases hd with ⟨r, q, rfl, hr3, hq⟩ | ⟨r, q, rfl⟩ | ⟨r, q, rfl⟩
  · have : Finite ↥(TauCeti.ValidLieTypeIndex.fixedField ⟨.B r q, hv⟩) :=
      CFSG.QuasithinUnique.SQTK.finite_validIndex_fixedField _
    exact Finite.of_equiv _
      (CFSG.RankThree.PartTwo.Census.Carrier.SpinB.typeBGroupEquivStatedProj_odd r q hv hq
        hr3).symm.toEquiv
  · have : Finite ↥(TauCeti.ValidLieTypeIndex.fixedField ⟨.D r q, hv⟩) :=
      CFSG.QuasithinUnique.SQTK.finite_validIndex_fixedField _
    exact Finite.of_equiv _
      (CFSG.RankThree.PartTwo.Census.Carrier.SpinD.typeDGroupEquivStatedProj_of_valid r q hv).symm.toEquiv
  · have : Finite ↥(TauCeti.ValidLieTypeIndex.fixedField ⟨.twistedD r q, hv⟩) :=
      CFSG.QuasithinUnique.SQTK.finite_validIndex_fixedField _
    obtain ⟨b, c', hirr, ⟨e⟩⟩ :=
      CFSG.RankThree.PartTwo.Census.Carrier.SpinD.exists_typeTwistedDGroupEquivStatedProj_of_valid
        r q hv
    exact Finite.of_equiv _ e.symm.toEquiv

theorem fixPlaneGen_orthogonal_index
    {d : TauCeti.ValidLieTypeIndex} (hd : IsOrthogonalIndex d.1) {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) (hpd : p ≠ d.1.characteristic) (hNJ : OrthFixedLeDerivedAll)
    (hno : ¬ ∃ E : Subgroup (Cat d), IsElemAbelian p E ∧ Nat.card E = p ^ 3) :
    FixPlaneGen (Cat d) p := by
  have hp : p.Prime := Fact.out
  have := finite_cat_orthogonal hd
  have hrkCat : RankLE2 p (Cat d) := rankLE2_of_not_exists_cube hp hno
  by_cases hp3 : 3 < p
  swap
  ·
    exfalso
    have hp3' : p = 3 := by
      have := hp.two_le
      interval_cases p <;> first | rfl | omega
    subst hp3'
    exact not_rankLE2_orthogonal_three d hd hrkCat
  · obtain ⟨d, hv⟩ := d
    have hrange := (TauCeti.LieTypeIndex.inStandardRange_iff _).1
      ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
    rcases hd with ⟨r, q, rfl, hr3, hq⟩ | ⟨r, q, rfl⟩ | ⟨r, q, rfl⟩
    ·
      have hq' : p ≠ q.p := by simpa using hpd
      let e := CFSG.RankThree.PartTwo.Census.Carrier.SpinB.typeBGroupEquivStatedProj_odd r q hv hq
        hr3
      have : Finite ↥(TauCeti.ValidLieTypeIndex.fixedField ⟨.B r q, hv⟩) :=
        CFSG.QuasithinUnique.SQTK.finite_validIndex_fixedField _
      have hcard : Nat.card ↥(TauCeti.ValidLieTypeIndex.fixedField ⟨.B r q, hv⟩) =
          q.p ^ q.exponent := by
        rw [card_fixedField_eq]
        simp [TauCeti.ValidLieTypeIndex.characteristic, TauCeti.ValidLieTypeIndex.fieldExponent]
      let e' := coordinateOddWitnessEquiv (n := r)
        ↥(TauCeti.ValidLieTypeIndex.fixedField ⟨.B r q, hv⟩) e
      exact FixPlaneGen.of_mulEquiv e' hp
        (fixPlaneGen_orthOdd ⟨q.prime_p, q.exponent_pos, hr3, hq⟩ hcard hp hp3 hq'
          (fun e => (hNJ r q.p e p).1)
          (rankLE2_of_injective e'.symm.toMonoidHom e'.symm.injective hrkCat))
    ·
      have hq' : p ≠ q.p := by simpa using hpd
      have hr4 : 4 ≤ r := hrange
      let e := CFSG.RankThree.PartTwo.Census.Carrier.SpinD.typeDGroupEquivStatedProj_of_valid r q hv
      have : Finite ↥(TauCeti.ValidLieTypeIndex.fixedField ⟨.D r q, hv⟩) :=
        CFSG.QuasithinUnique.SQTK.finite_validIndex_fixedField _
      have hcard : Nat.card ↥(TauCeti.ValidLieTypeIndex.fixedField ⟨.D r q, hv⟩) =
          q.p ^ q.exponent := by
        rw [card_fixedField_eq]
        simp [TauCeti.ValidLieTypeIndex.characteristic, TauCeti.ValidLieTypeIndex.fieldExponent]
      let e' := coordinatePlusWitnessEquiv (n := r)
        ↥(TauCeti.ValidLieTypeIndex.fixedField ⟨.D r q, hv⟩) e
      exact FixPlaneGen.of_mulEquiv e' hp
        (fixPlaneGen_orthPlus ⟨q.prime_p, q.exponent_pos, hr4⟩ hcard hp hp3 hq'
          (fun e => (hNJ r q.p e p).2.1)
          (rankLE2_of_injective e'.symm.toMonoidHom e'.symm.injective hrkCat))
    ·
      have hq' : p ≠ q.p := by simpa using hpd
      have hr4 : 4 ≤ r := hrange
      obtain ⟨b, c', hirr, ⟨e⟩⟩ :=
        CFSG.RankThree.PartTwo.Census.Carrier.SpinD.exists_typeTwistedDGroupEquivStatedProj_of_valid
          r q hv
      have : Finite ↥(TauCeti.ValidLieTypeIndex.fixedField ⟨.twistedD r q, hv⟩) :=
        CFSG.QuasithinUnique.SQTK.finite_validIndex_fixedField _
      have hcard : Nat.card ↥(TauCeti.ValidLieTypeIndex.fixedField ⟨.twistedD r q, hv⟩) =
          q.p ^ q.exponent := by
        rw [card_fixedField_eq]
        simp [TauCeti.ValidLieTypeIndex.characteristic, TauCeti.ValidLieTypeIndex.fieldExponent]
      exact fixPlaneGen_minus_of_model
        ⟨⟨q.prime_p, q.exponent_pos, hr4⟩, _, inferInstance, inferInstance, hcard, b, c', hirr,
          ⟨e⟩⟩ hp hp3 hq' (fun e => (hNJ r q.p e p).2.2) hrkCat

end CFSG.HardMathSupport.Curtis.Coordinator.SeitzOuter
