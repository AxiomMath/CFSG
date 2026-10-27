module

public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.CrossOrthPlane
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.CrossOrthModel
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.CrossSp
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.OrthFamily

public section

namespace CFSG.HardMathSupport.Timmesfeld.LocalTwo

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance Module
  CFSG.HardMathSupport.Timmesfeld.Coordinator CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.RankThree.PartOne CFSG.RankThree.Classical2 CFSG.Assembly.LowTwoRank
  CFSG.RankThree.PartTwo.Census CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  CFSG.LieType.Universal.Spin

@[expose] def regimeBOrthTwo (idx : TauCeti.ValidLieTypeIndex) (_p : ℕ) : Prop :=
  ∃ (r : ℕ) (q : TauCeti.PrimePower), idx.1 = .B r q ∧ q.p ≠ 2 ∧ 3 ≤ r

open CFSG.RankThree.PartTwo.Census CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  CFSG.LieType.Universal.Spin CFSG.RankThree.PartOne.KCOrthogonal in
theorem crossCharTwoFamAt_B_orth : CrossCharTwoFamAt .B regimeBOrthTwo := by
  rintro ⟨d, hv⟩ _ p hp hp5 hc ⟨r, q, hd, hq2, hr⟩ _
  change d = _ at hd
  subst hd
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  set F := ↥(TauCeti.ValidLieTypeIndex.fixedField ⟨.B r q, hv⟩) with hF
  have : Finite F := CFSG.QuasithinUnique.SQTK.finite_validIndex_fixedField _
  have hcard : Nat.card F = q.p ^ q.exponent :=
    card_fixedField_validIndex_orth ⟨.B r q, hv⟩ r q (Or.inl rfl)
  have hring : ringChar F = q.p :=
    CFSG.ClassicalGroups.Orthogonal.ringChar_eq_of_card_eq q.prime_p q.exponent_pos hcard
  have hpq : p ≠ q.p := fun h => hc (by simp [h])
  have hpl : p ≠ ringChar F := by rw [hring]; exact hpq
  have h2 : (2 : F) ≠ 0 := by
    have : CharP F q.p := ringChar.of_eq hring
    intro h
    have : q.p ∣ 2 := (CharP.cast_eq_zero_iff F q.p 2).mp (by exact_mod_cast h)
    exact hq2 ((Nat.prime_dvd_prime_iff_eq q.prime_p Nat.prime_two).mp this)
  obtain ⟨hQ, hT⟩ := CFSG.ClassicalGroups.Orthogonal.regular_quadOdd (n := r) (K := F) h2 hr
  let e₁ := Carrier.SpinB.typeBGroupEquivStatedProj_odd r q hv hq2 hr
  obtain ⟨e₂⟩ := CFSG.RankThree.CentralLift.nonempty_statedProj_mulEquiv_projOrthDerived
    (coe_quadOdd r F)
  let e : Cat ⟨.B r q, hv⟩ ≃* ProjOrthDerived (quadOdd r F) := e₁.trans e₂
  have hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel (Cat ⟨.B r q, hv⟩) .POmegaOdd r
      q.p q.exponent :=
    statedClassicalModel_typeB_odd r q hv hq2 hr (MulEquiv.refl _)
  have hCLm : CommonLayerCentralizerTrivial
      (CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear.matrixProjectiveDerived
        (coordinateQuadOdd r F)) p :=
    orthogonal_inner_plane_local_components_full_automorphism_centralizer (Cat ⟨.B r q, hv⟩)
      .POmegaOdd (Or.inl rfl) r q.p q.exponent p hmodel hp (by omega) hpq F hcard e₁
  let eP := (KCOrthogonalD4.bridgeEquiv (coordinateQuadOdd r F) (by omega)).trans
        (KCOrthogonalDescent.projOrthDerivedEquiv (coordinateOddIsometry r F).symm.toLinearEquiv 1
          fun v => by
            rw [Units.val_one, one_mul]
            exact (coordinateOddIsometry r F).symm.map_app v)
  have hCL : CommonLayerCentralizerTrivial (ProjOrthDerived (quadOdd r F)) p :=
    CommonLayerCentralizerTrivial.of_mulEquiv eP hCLm
  exact IsLocallyBalancedAbs.of_mulEquiv e
    (isLocallyBalancedAbs_two_projOrth hQ hT hp hp5 hpl hCL eP.symm
      fun [Finite _] hinj => outerFields_matrix_odd hmodel hp (by omega) hpq F hcard e₁ hinj)

theorem crossCharTwoFamCat_D : CrossCharTwoFamCat .D := by
  rintro ⟨d, hv⟩ ⟨r, q, hd⟩ p hp hp5 hc _
  change d = _ at hd
  subst hd
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  have hr : 4 ≤ r := (TauCeti.LieTypeIndex.inStandardRange_iff _).mp
    ((TauCeti.LieTypeIndex.valid_iff _).mp hv).1
  set F := ↥(TauCeti.ValidLieTypeIndex.fixedField ⟨.D r q, hv⟩) with hF
  have : Finite F := CFSG.QuasithinUnique.SQTK.finite_validIndex_fixedField _
  have hcard : Nat.card F = q.p ^ q.exponent :=
    card_fixedField_validIndex_orth ⟨.D r q, hv⟩ r q (Or.inr (Or.inl rfl))
  have hring : ringChar F = q.p :=
    CFSG.ClassicalGroups.Orthogonal.ringChar_eq_of_card_eq q.prime_p q.exponent_pos hcard
  have hpq : p ≠ q.p := fun h => hc (by simp [h])
  have hpl : p ≠ ringChar F := by rw [hring]; exact hpq
  obtain ⟨hQ, hT⟩ := CFSG.ClassicalGroups.Orthogonal.regular_quadPlus (n := r) (K := F)
    (by omega)
  let e₁ := Carrier.SpinD.typeDGroupEquivStatedProj_of_valid r q hv
  obtain ⟨e₂⟩ := CFSG.RankThree.CentralLift.nonempty_statedProj_mulEquiv_projOrthDerived
    (coe_quadPlus r F)
  let e : Cat ⟨.D r q, hv⟩ ≃* ProjOrthDerived (quadPlus r F) := e₁.trans e₂
  have hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel (Cat ⟨.D r q, hv⟩) .POmegaPlus r
      q.p q.exponent :=
    statedClassicalModel_typeD r q hv (MulEquiv.refl _)
  have hCLm : CommonLayerCentralizerTrivial
      (CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear.matrixProjectiveDerived
        (coordinateQuadPlus r F)) p :=
    orthogonal_inner_plane_local_components_full_automorphism_centralizer (Cat ⟨.D r q, hv⟩)
      .POmegaPlus (Or.inr (Or.inl rfl)) r q.p q.exponent p hmodel hp (by omega) hpq F hcard e₁
  let eP := (KCOrthogonalD4.bridgeEquiv (coordinateQuadPlus r F) (by omega)).trans
        (KCOrthogonalDescent.projOrthDerivedEquiv (coordinatePlusIsometry r F).symm.toLinearEquiv 1
          fun v => by
            rw [Units.val_one, one_mul]
            exact (coordinatePlusIsometry r F).symm.map_app v)
  have hCL : CommonLayerCentralizerTrivial (ProjOrthDerived (quadPlus r F)) p :=
    CommonLayerCentralizerTrivial.of_mulEquiv eP hCLm
  exact IsLocallyBalancedAbs.of_mulEquiv e
    (isLocallyBalancedAbs_two_projOrth hQ hT hp hp5 hpl hCL eP.symm
      fun [Finite _] hinj => outerFields_matrix_plus hmodel hp (by omega) hpq F hcard e₁ hinj)

theorem crossCharTwoFamCat_twistedD : CrossCharTwoFamCat .twistedD := by
  rintro ⟨d, hv⟩ ⟨r, q, hd⟩ p hp hp5 hc _
  change d = _ at hd
  subst hd
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  have hr : 4 ≤ r := (TauCeti.LieTypeIndex.inStandardRange_iff _).mp
    ((TauCeti.LieTypeIndex.valid_iff _).mp hv).1
  set F := ↥(TauCeti.ValidLieTypeIndex.fixedField ⟨.twistedD r q, hv⟩) with hF
  have : Finite F := CFSG.QuasithinUnique.SQTK.finite_validIndex_fixedField _
  have hcard : Nat.card F = q.p ^ q.exponent :=
    card_fixedField_validIndex_orth ⟨.twistedD r q, hv⟩ r q (Or.inr (Or.inr rfl))
  have hring : ringChar F = q.p :=
    CFSG.ClassicalGroups.Orthogonal.ringChar_eq_of_card_eq q.prime_p q.exponent_pos hcard
  have hpq : p ≠ q.p := fun h => hc (by simp [h])
  have hpl : p ≠ ringChar F := by rw [hring]; exact hpq
  obtain ⟨b, c, hirr, ⟨e₁⟩⟩ := Carrier.SpinD.exists_typeTwistedDGroupEquivStatedProj_of_valid r q hv
  obtain ⟨hQ, hT⟩ := CFSG.ClassicalGroups.Orthogonal.regular_quadMinus (n := r) (K := F) (b := b)
    (c := c) hr hirr
  obtain ⟨e₂⟩ := CFSG.RankThree.CentralLift.nonempty_statedProj_mulEquiv_projOrthDerived
    (coe_quadMinus r F b c)
  let e : Cat ⟨.twistedD r q, hv⟩ ≃* ProjOrthDerived (quadMinus r F b c) := e₁.trans e₂
  have hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel (Cat ⟨.twistedD r q, hv⟩)
      .POmegaMinus r q.p q.exponent :=
    statedClassicalModel_typeTwistedD r q hv (MulEquiv.refl _)
  have hn : 1 ≤ r := by omega
  have hCLm : CommonLayerCentralizerTrivial
      (CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear.matrixProjectiveDerived
        (coordinateQuadMinus r F hn b c)) p :=
    orthogonal_inner_plane_local_components_full_automorphism_centralizer
      (Cat ⟨.twistedD r q, hv⟩) .POmegaMinus (Or.inr (Or.inr rfl)) r q.p q.exponent p hmodel hp
      (by omega) hpq hn F hcard b c hirr e₁
  let eP := (KCOrthogonalD4.bridgeEquiv (coordinateQuadMinus r F hn b c) (by omega)).trans
        (KCOrthogonalDescent.projOrthDerivedEquiv
          (coordinateMinusIsometry r F hn b c).symm.toLinearEquiv 1 fun v => by
            rw [Units.val_one, one_mul]
            exact (coordinateMinusIsometry r F hn b c).symm.map_app v)
  have hCL : CommonLayerCentralizerTrivial (ProjOrthDerived (quadMinus r F b c)) p :=
    CommonLayerCentralizerTrivial.of_mulEquiv eP hCLm
  exact IsLocallyBalancedAbs.of_mulEquiv e
    (isLocallyBalancedAbs_two_projOrth hQ hT hp hp5 hpl hCL eP.symm
      fun [Finite _] hinj => outerFields_matrix_minus hmodel hn hp (by omega) hpq F hcard b c hirr
        e₁ hinj)

theorem crossCharTwoFamCat_B : CrossCharTwoFamCat .B := by
  refine crossCharTwoFamCat_of_at regimeBOrthTwo crossCharTwoFamAt_B_orth ?_
  rintro ⟨d, hv⟩ hk p hp hp5 hc hR hnexc
  obtain ⟨r, q, hd⟩ := hk
  have hrange := (TauCeti.LieTypeIndex.inStandardRange_iff _).1
    ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
  have hreg : regimeBSpTwo ⟨d, hv⟩ p := by
    refine ⟨r, q, hd, ?_⟩
    by_contra hno
    push Not at hno
    subst hd
    exact hR ⟨r, q, rfl, hno.2, by have := hrange.1; omega⟩
  exact crossCharTwoFamAt_B_symplectic ⟨d, hv⟩ ⟨r, q, hd⟩ p hp hp5 hc hreg hnexc

end CFSG.HardMathSupport.Timmesfeld.LocalTwo
