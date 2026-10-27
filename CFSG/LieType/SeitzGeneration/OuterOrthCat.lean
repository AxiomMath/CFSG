module

public import CFSG.LieType.SeitzGeneration.OuterOrthData
public import CFSG.LieType.SeitzGeneration.OuterOrthMinus
public import CFSG.LieType.SeitzGeneration.OuterModel
public import CFSG.LieType.SeitzGeneration.InnerOrthogonal

public section

namespace CFSG.LieType.SeitzGeneration

open Module QuadraticMap CFSG.RankThree.PartOne.CTP CFSG.ClassicalGroups.Orthogonal
  CFSG.LieType.Universal.Spin CFSG.Open CFSG.AGLEmbeddingD2
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open CFSG.Assembly.LowTwoRank (StatedProj StatedOmega StatedQuadOdd StatedQuadPlus StatedQuadMinus
  StatedLieTag StatedLieAdmissible StatedClassicalModel)

section Model

variable {G : Type} [Group G] {n ℓ f p : ℕ}

theorem fieldAutData_of_model (hpair : SubfieldPairOmega) [Finite G] {c : StatedLieTag}
    (hc : c = .POmegaOdd ∨ c = .POmegaPlus ∨ c = .POmegaMinus)
    (hM : StatedClassicalModel G c n ℓ f) (hp : p.Prime) (hp3 : 3 < p) (hpℓ : p ≠ ℓ) :
    FieldAutData G p := by
  rcases hc with rfl | rfl | rfl
  · obtain ⟨hadm, K, _, _, hK, ⟨e⟩⟩ := id hM
    exact (fieldAutData_odd hpair.1 hadm hK hp hp3 hpℓ).of_mulEquiv
      (coordinateOddWitnessEquiv K e) hp
  · obtain ⟨hadm, K, _, _, hK, ⟨e⟩⟩ := id hM
    exact (fieldAutData_plus hpair.2.1 hadm hK hp hp3 hpℓ).of_mulEquiv
      (coordinatePlusWitnessEquiv K e) hp
  · exact fieldAutData_minus hpair.2.2 hM hp hp3 hpℓ

end Model

section Perfect

variable {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]
  {Q : QuadraticForm K (ι → K)} {Q₀ : (ι → K) → K}

theorem isPerfect_statedProj_of_regular (hQ : ⇑Q = Q₀)
    (hE : ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ =
      elementaryGroup Q) (hnd : (polarBilin Q).Nondegenerate) {T : Submodule K (ι → K)}
    (hT : 3 ≤ finrank K T) (hTQ : ∀ x ∈ T, Q x = 0) :
    Group.IsPerfect (StatedProj (StatedOmega Q₀)) := by
  have hcomm : commutator (elementaryGroup Q) = ⊤ := commutator_elementaryGroup_eq_top' hnd hT hTQ
  have hperf : Group.IsPerfect (elementaryGroup Q) := ⟨hcomm⟩
  have hperf' : Group.IsPerfect (ProjElementary Q) :=
    Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' _) (QuotientGroup.mk'_surjective _)
  exact Group.IsPerfect.ofSurjective (f := (statedProjEquiv hQ hE).symm.toMonoidHom)
    (statedProjEquiv hQ hE).symm.surjective

end Perfect

section Facts

variable {G : Type} [Group G] {n ℓ f : ℕ}

theorem orth_facts_of_model {c : StatedLieTag}
    (hc : c = .POmegaOdd ∨ c = .POmegaPlus ∨ c = .POmegaMinus)
    (hM : StatedClassicalModel G c n ℓ f) :
    Finite G ∧ Nontrivial G ∧ IsSimpleGroup G ∧ Group.IsPerfect G := by
  rcases hc with rfl | rfl | rfl
  · obtain ⟨⟨hℓ, hf, hn3, hℓ2⟩, K, _, _, hK, ⟨e⟩⟩ := id hM
    have hq : (ringChar K).Prime := by rw [ringChar_eq_of_card_eq hℓ hf hK]; exact hℓ
    have h2 : (2 : K) ≠ 0 := by
      rw [Ne, two_eq_zero_iff_ringChar_eq_two hq, ringChar_eq_of_card_eq hℓ hf hK]
      exact hℓ2
    obtain ⟨hnd, T, hT, hTQ⟩ := regular_quadOdd h2 hn3
    have := isPerfect_statedProj_of_regular (coe_quadOdd n K)
      (commutator_orthogonalGroup_quadOdd h2 hn3) hnd hT.ge hTQ
    have hs := isSimpleGroup_of_statedClassicalModel_POmegaOdd G n ℓ f hM
    exact ⟨Finite.of_equiv _ e.symm.toEquiv, hs.1, hs.2,
      Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective⟩
  · obtain ⟨⟨-, -, hn4⟩, K, _, _, -, ⟨e⟩⟩ := id hM
    obtain ⟨hnd, T, hT, hTQ⟩ := regular_quadPlus (K := K) (by omega : 3 ≤ n)
    have := isPerfect_statedProj_of_regular (coe_quadPlus n K)
      (commutator_orthogonalGroup_quadPlus (by omega : 3 ≤ n)) hnd hT.ge hTQ
    have hs := isSimpleGroup_of_statedClassicalModel_POmegaPlus G n ℓ f hM
    exact ⟨Finite.of_equiv _ e.symm.toEquiv, hs.1, hs.2,
      Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective⟩
  · obtain ⟨⟨-, -, hn4⟩, K, _, _, -, b, c, hirr, ⟨e⟩⟩ := id hM
    obtain ⟨hnd, T, hT, hTQ⟩ := regular_quadMinus hn4 hirr
    have := isPerfect_statedProj_of_regular (coe_quadMinus n K b c)
      (commutator_orthogonalGroup_quadMinus hn4 hirr) hnd hT.ge hTQ
    have hs := isSimpleGroup_of_statedClassicalModel_POmegaMinus G n ℓ f hM
    exact ⟨Finite.of_equiv _ e.symm.toEquiv, hs.1, hs.2,
      Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective⟩

end Facts

section Planes

theorem planeGen_outer_orth_model (hpair : SubfieldPairOmega) {d : TauCeti.ValidLieTypeIndex}
    {c : StatedLieTag} (hc : c = .POmegaOdd ∨ c = .POmegaPlus ∨ c = .POmegaMinus)
    {n ℓ f p : ℕ} (hM : StatedClassicalModel (Cat d) c n ℓ f) (hp : p.Prime) (hp3 : 3 < p)
    (hpℓ : p ≠ ℓ) {E : Subgroup (MulAut (Cat d))} (hE : IsElemAbelian p E)
    (hcard : Nat.card E = p ^ 2) (hout : ¬ InnerPlane d p E) : PlaneGen E := by
  obtain ⟨hfin, hnt, hsimple, hperf⟩ := orth_facts_of_model hc hM
  have hnab : ∃ a b : Cat d, a * b ≠ b * a := by
    by_contra hcon
    push Not at hcon
    exact Group.IsPerfect.not_isMulCommutative (Cat d) ⟨⟨fun a b => hcon a b⟩⟩
  have hd : FieldAutData (Cat d) p := fieldAutData_of_model hpair hc hM hp hp3 hpℓ
  have hEi : CFSG.IsElementaryAbelian p E :=
    (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian p _).mpr hE
  have hout' : ¬ ∀ φ ∈ E, ∃ g, φ = MulAut.conj g := fun h =>
    hout fun φ hφ => (h φ hφ).imp fun g hg => hg.symm
  exact (planeGen_iff_closure_fixUnion E).mpr
    (closure_fixUnion_eq_top_of_fieldAutData hnab hp hd E hcard hout')

theorem seitzOuter_orthogonal_five (hpair : SubfieldPairOmega) :
    SeitzPlanes fun d p E => ¬ InnerPlane d p E ∧ 5 ≤ p ∧ IsOrthogonalIndex d.1 := by
  rintro ⟨d, hv⟩ p hp hp2 hpd hex E hE hc ⟨hout, hp5, horth⟩
  have hp3 : 3 < p := by omega
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
    exact planeGen_outer_orth_model hpair (Or.inl rfl) (n := r) (ℓ := q.p) (f := q.exponent)
      ⟨⟨q.prime_p, q.exponent_pos, hr3, hq⟩, _, inferInstance, inferInstance, hcardK, ⟨e⟩⟩ hp hp3
      hq' hE hc hout
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
    exact planeGen_outer_orth_model hpair (Or.inr (Or.inl rfl)) (n := r) (ℓ := q.p)
      (f := q.exponent)
      ⟨⟨q.prime_p, q.exponent_pos, hr4⟩, _, inferInstance, inferInstance, hcardK, ⟨e⟩⟩ hp hp3 hq'
      hE hc hout
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
    exact planeGen_outer_orth_model hpair (Or.inr (Or.inr rfl)) (n := r) (ℓ := q.p)
      (f := q.exponent)
      ⟨⟨q.prime_p, q.exponent_pos, hr4⟩, _, inferInstance, inferInstance, hcardK, b, c', hirr,
        ⟨e⟩⟩ hp hp3 hq' hE hc hout

end Planes

end CFSG.LieType.SeitzGeneration
