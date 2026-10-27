module

public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.FamOpen
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.OrthTwoAux.D4
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.CrossLin

public section

namespace CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance Module
  CFSG.HardMathSupport.Timmesfeld.Coordinator CFSG.RankThree.PartOne CFSG.RankThree.Classical2
  CFSG.Assembly.LowTwoRank CFSG.RankThree.PartTwo.Census
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear CFSG.LieType.Universal.Spin
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.LocalTwo
  CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.OrthTwoAux

theorem orthTwoInnerPlaneBalance_D (r : ℕ) (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.D r q).Valid) (hq2 : q.card = 2) :
    InnerPlaneBalance 3 (CatT ⟨.D r q, hv⟩) := by
  have hr4 : 4 ≤ r := (TauCeti.LieTypeIndex.inStandardRange_iff _).mp
    ((TauCeti.LieTypeIndex.valid_iff _).mp hv).1
  set F := ↥(TauCeti.ValidLieTypeIndex.fixedField ⟨.D r q, hv⟩) with hF
  have : Finite F := CFSG.QuasithinUnique.SQTK.finite_validIndex_fixedField _
  have hK : Nat.card F = 2 := card_fixedField_eq_two_of_card (Or.inl rfl) hq2
  rcases (show r = 4 ∨ 5 ≤ r by omega) with rfl | hr5
  · let e₁ := Carrier.SpinD.typeDGroupEquivStatedProj_of_valid 4 q hv
    exact InnerPlaneBalance.of_mulEquiv (coordinatePlusWitnessEquiv F e₁)
      (d4two_innerPlaneBalance hK)
  · obtain ⟨hQ, hT⟩ := CFSG.ClassicalGroups.Orthogonal.regular_quadPlus (n := r) (K := F)
      (by omega)
    let e₁ := Carrier.SpinD.typeDGroupEquivStatedProj_of_valid r q hv
    obtain ⟨e₂⟩ := CFSG.RankThree.CentralLift.nonempty_statedProj_mulEquiv_projOrthDerived
      (coe_quadPlus r F)
    let e : CatT ⟨.D r q, hv⟩ ≃* ProjOrthDerived (quadPlus r F) := e₁.trans e₂
    have hdim : finrank F (Fin r ⊕ Fin r → F) = r + r := by
      rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin]
    exact InnerPlaneBalance.of_mulEquiv e
      (innerPlaneBalance_orth_two hK hQ hT (by omega)
        (fun α => KCOrthogonalAut.orthogonal_aut_semilinear_of_seven_le _ hQ (by omega)
          (fun h8 => by omega) α))

theorem orthTwoInnerPlaneBalance_twistedD (r : ℕ) (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.twistedD r q).Valid) (hq2 : q.card = 2) :
    InnerPlaneBalance 3 (CatT ⟨.twistedD r q, hv⟩) := by
  have hr4 : 4 ≤ r := (TauCeti.LieTypeIndex.inStandardRange_iff _).mp
    ((TauCeti.LieTypeIndex.valid_iff _).mp hv).1
  set F := ↥(TauCeti.ValidLieTypeIndex.fixedField ⟨.twistedD r q, hv⟩) with hF
  have : Finite F := CFSG.QuasithinUnique.SQTK.finite_validIndex_fixedField _
  have hK : Nat.card F = 2 := card_fixedField_eq_two_of_card (Or.inr rfl) hq2
  obtain ⟨b, c, hirr, ⟨e₁⟩⟩ := Carrier.SpinD.exists_typeTwistedDGroupEquivStatedProj_of_valid r q hv
  obtain ⟨hQ, hT⟩ := CFSG.ClassicalGroups.Orthogonal.regular_quadMinus (n := r) (K := F) (b := b)
    (c := c) hr4 hirr
  obtain ⟨e₂⟩ := CFSG.RankThree.CentralLift.nonempty_statedProj_mulEquiv_projOrthDerived
    (coe_quadMinus r F b c)
  let e : CatT ⟨.twistedD r q, hv⟩ ≃* ProjOrthDerived (quadMinus r F b c) := e₁.trans e₂
  have hdim : finrank F (Fin (r - 1) ⊕ Fin (r - 1) ⊕ Fin 2 → F) = (r - 1) + ((r - 1) + 2) := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_sum, Fintype.card_fin,
      Fintype.card_fin]
  exact InnerPlaneBalance.of_mulEquiv e
    (innerPlaneBalance_orth_two hK hQ hT (by omega)
      (orth3_aut_semilinear_quadMinus r hr4 b c hirr))

theorem orthTwoThreeInnerBalance_holds : OrthTwoThreeInnerBalance :=
  ⟨fun r q hv hq2 => orthTwoInnerPlaneBalance_D r q hv hq2,
    fun r q hv hq2 => orthTwoInnerPlaneBalance_twistedD r q hv hq2⟩

end CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross
