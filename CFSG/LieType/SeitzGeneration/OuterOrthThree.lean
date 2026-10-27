module

public import CFSG.LieType.SeitzGeneration.OuterOrthThreeData
public import CFSG.LieType.SeitzGeneration.OuterOrthCat

public section

namespace CFSG.LieType.SeitzGeneration

open Module QuadraticMap CFSG.RankThree.PartOne.CTP CFSG.ClassicalGroups.Orthogonal
  CFSG.LieType.Universal.Spin CFSG.Open CFSG.AGLEmbeddingD2
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open CFSG.Assembly.LowTwoRank (StatedProj StatedOmega StatedQuadOdd StatedQuadPlus StatedQuadMinus
  StatedLieTag StatedLieAdmissible StatedClassicalModel)

section Planes

theorem planeGen_outer_orth_model_three (hpair : SubfieldPairOmegaThree)
    {d : TauCeti.ValidLieTypeIndex} {c : StatedLieTag}
    (hc : c = .POmegaOdd ∨ c = .POmegaPlus ∨ c = .POmegaMinus) {n ℓ f p : ℕ}
    (hM : StatedClassicalModel (Cat d) c n ℓ f) (hD4 : c = .POmegaPlus → n ≠ 4)
    (hp : p.Prime) (hp3 : p = 3) (hpℓ : p ≠ ℓ) {E : Subgroup (MulAut (Cat d))}
    (hE : IsElemAbelian p E) (hcard : Nat.card E = p ^ 2) (hout : ¬ InnerPlane d p E) :
    PlaneGen E := by
  obtain ⟨hfin, hnt, hsimple, hperf⟩ := orth_facts_of_model hc hM
  have hnab : ∃ a b : Cat d, a * b ≠ b * a := by
    by_contra hcon
    push Not at hcon
    exact Group.IsPerfect.not_isMulCommutative (Cat d) ⟨⟨fun a b => hcon a b⟩⟩
  have hd : FieldAutData (Cat d) p := fieldAutData_of_model_three hpair hc hM hD4 hp hp3 hpℓ
  have hEi : CFSG.IsElementaryAbelian p E :=
    (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian p _).mpr hE
  have hout' : ¬ ∀ φ ∈ E, ∃ g, φ = MulAut.conj g := fun h =>
    hout fun φ hφ => (h φ hφ).imp fun g hg => hg.symm
  exact (planeGen_iff_closure_fixUnion E).mpr
    (closure_fixUnion_eq_top_of_fieldAutData hnab hp hd E hcard hout')

theorem seitzOuter_orthogonal_three (hpair : SubfieldPairOmegaThree) :
    SeitzPlanes fun d p E => ¬ InnerPlane d p E ∧ p = 3 ∧ IsOrthogonalIndex d.1 ∧
      ¬ IsDFourIndex d.1 := by
  rintro ⟨d, hv⟩ p hp hp2 hpd hex E hE hc ⟨hout, hp3, horth, hD4⟩
  rcases horth with ⟨r, q, rfl, hr3, hq⟩ | ⟨r, q, rfl⟩ | ⟨r, q, rfl⟩
  ·
    have hq' : p ≠ q.p := by simpa using hpd
    let e := CFSG.RankThree.PartTwo.Census.Carrier.SpinB.typeBGroupEquivStatedProj_odd r q hv hq
      hr3
    have : Finite ↥(TauCeti.ValidLieTypeIndex.fixedField ⟨.B r q, hv⟩) :=
      CFSG.QuasithinUnique.SQTK.finite_validIndex_fixedField _
    have hcardK : Nat.card ↥(TauCeti.ValidLieTypeIndex.fixedField ⟨.B r q, hv⟩) =
        q.p ^ q.exponent := by
      rw [card_fixedField_eq]
      simp [TauCeti.ValidLieTypeIndex.characteristic, TauCeti.ValidLieTypeIndex.fieldExponent]
    exact planeGen_outer_orth_model_three hpair (Or.inl rfl) (n := r) (ℓ := q.p)
      (f := q.exponent)
      ⟨⟨q.prime_p, q.exponent_pos, hr3, hq⟩, _, inferInstance, inferInstance, hcardK, ⟨e⟩⟩
      (fun h => nomatch h) hp hp3 hq' hE hc hout
  ·
    have hq' : p ≠ q.p := by simpa using hpd
    have hr4 : 4 ≤ r := ((TauCeti.LieTypeIndex.inStandardRange_iff _).1
      ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1)
    let e := CFSG.RankThree.PartTwo.Census.Carrier.SpinD.typeDGroupEquivStatedProj_of_valid r q hv
    have : Finite ↥(TauCeti.ValidLieTypeIndex.fixedField ⟨.D r q, hv⟩) :=
      CFSG.QuasithinUnique.SQTK.finite_validIndex_fixedField _
    have hcardK : Nat.card ↥(TauCeti.ValidLieTypeIndex.fixedField ⟨.D r q, hv⟩) =
        q.p ^ q.exponent := by
      rw [card_fixedField_eq]
      simp [TauCeti.ValidLieTypeIndex.characteristic, TauCeti.ValidLieTypeIndex.fieldExponent]
    exact planeGen_outer_orth_model_three hpair (Or.inr (Or.inl rfl)) (n := r) (ℓ := q.p)
      (f := q.exponent)
      ⟨⟨q.prime_p, q.exponent_pos, hr4⟩, _, inferInstance, inferInstance, hcardK, ⟨e⟩⟩
      (fun _ h4 => hD4 ⟨q, congrArg (fun r' => TauCeti.LieTypeIndex.D r' q) h4⟩) hp hp3 hq' hE hc
      hout
  ·
    have hq' : p ≠ q.p := by simpa using hpd
    have hr4 : 4 ≤ r := ((TauCeti.LieTypeIndex.inStandardRange_iff _).1
      ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1)
    obtain ⟨b, c', hirr, ⟨e⟩⟩ :=
      CFSG.RankThree.PartTwo.Census.Carrier.SpinD.exists_typeTwistedDGroupEquivStatedProj_of_valid
        r q hv
    have : Finite ↥(TauCeti.ValidLieTypeIndex.fixedField ⟨.twistedD r q, hv⟩) :=
      CFSG.QuasithinUnique.SQTK.finite_validIndex_fixedField _
    have hcardK : Nat.card ↥(TauCeti.ValidLieTypeIndex.fixedField ⟨.twistedD r q, hv⟩) =
        q.p ^ q.exponent := by
      rw [card_fixedField_eq]
      simp [TauCeti.ValidLieTypeIndex.characteristic, TauCeti.ValidLieTypeIndex.fieldExponent]
    exact planeGen_outer_orth_model_three hpair (Or.inr (Or.inr rfl)) (n := r) (ℓ := q.p)
      (f := q.exponent)
      ⟨⟨q.prime_p, q.exponent_pos, hr4⟩, _, inferInstance, inferInstance, hcardK, b, c', hirr,
        ⟨e⟩⟩ (fun h => nomatch h) hp hp3 hq' hE hc hout

end Planes

end CFSG.LieType.SeitzGeneration
