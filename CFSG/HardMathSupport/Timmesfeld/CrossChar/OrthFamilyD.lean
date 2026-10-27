module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.OrthFamily

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance Module
  CFSG.HardMathSupport.Timmesfeld.Coordinator CFSG.RankThree.PartOne
  CFSG.RankThree.Classical2 CFSG.Assembly.LowTwoRank CFSG.RankThree.PartTwo.Census
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData CFSG.LieType.Universal.Spin

@[expose] def regimeDOrth (idx : TauCeti.ValidLieTypeIndex) (p : ℕ) : Prop :=
  ∃ (r : ℕ) (q : TauCeti.PrimePower), idx.1 = .D r q ∧ 3 < p

@[expose] def regimeTwistedDOrth (idx : TauCeti.ValidLieTypeIndex) (p : ℕ) : Prop :=
  ∃ (r : ℕ) (q : TauCeti.PrimePower), idx.1 = .twistedD r q ∧ 3 < p

theorem crossCharFamAt_D_orth : CrossCharFamAt .D regimeDOrth := by
  rintro ⟨d, hv⟩ _ p hp hp2 hc ⟨r, q, hd, hp3⟩
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
      .POmegaPlus (Or.inr (Or.inl rfl)) r q.p q.exponent p hmodel hp hp3 hpq F hcard e₁
  have hCL : CommonLayerCentralizerTrivial (ProjOrthDerived (quadPlus r F)) p :=
    CommonLayerCentralizerTrivial.of_mulEquiv
      ((KCOrthogonalD4.bridgeEquiv (coordinateQuadPlus r F) (by omega)).trans
        (KCOrthogonalDescent.projOrthDerivedEquiv (coordinatePlusIsometry r F).symm.toLinearEquiv 1
          fun v => by
            rw [Units.val_one, one_mul]
            exact (coordinatePlusIsometry r F).symm.map_app v)) hCLm
  have hmodelT := statedClassicalModel_typeD r q hv e.symm
  have hO : OutStructure.OutPChain p (ProjOrthDerived (quadPlus r F)) := by
    rcases Nat.lt_or_ge r 5 with h5 | h5
    · have h4 : r = 4 := by omega
      have hp5 : 5 ≤ p := by
        rcases (by omega : p = 4 ∨ 5 ≤ p) with h | h
        · exact absurd (h ▸ hp) (by norm_num)
        · exact h
      subst h4
      exact OutStructure.outPChain_POmegaPlus_four_gen hp hp5 hmodelT
    · exact (CFSG.LocalAnalysis.RankThreeTheoremC.outPNice_POmegaPlus_ge_five_of_ne_two hp hp2
        h5 hmodelT).toChain
  exact IsLocallyBalancedAbs.of_mulEquiv e
    (isLocallyBalancedAbs_projOrth hQ hT hp hp3 hpl hCL hO)

theorem crossCharFamAt_twistedD_orth : CrossCharFamAt .twistedD regimeTwistedDOrth := by
  rintro ⟨d, hv⟩ _ p hp hp2 hc ⟨r, q, hd, hp3⟩
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
      hp3 hpq hn F hcard b c hirr e₁
  have hCL : CommonLayerCentralizerTrivial (ProjOrthDerived (quadMinus r F b c)) p :=
    CommonLayerCentralizerTrivial.of_mulEquiv
      ((KCOrthogonalD4.bridgeEquiv (coordinateQuadMinus r F hn b c) (by omega)).trans
        (KCOrthogonalDescent.projOrthDerivedEquiv
          (coordinateMinusIsometry r F hn b c).symm.toLinearEquiv 1 fun v => by
            rw [Units.val_one, one_mul]
            exact (coordinateMinusIsometry r F hn b c).symm.map_app v)) hCLm
  have hO : OutStructure.OutPChain p (ProjOrthDerived (quadMinus r F b c)) :=
    (CFSG.LocalAnalysis.RankThreeTheoremC.outPNice_POmegaMinus_of_ne_two hp hp2
      (statedClassicalModel_typeTwistedD r q hv e.symm)).toChain
  exact IsLocallyBalancedAbs.of_mulEquiv e
    (isLocallyBalancedAbs_projOrth hQ hT hp hp3 hpl hCL hO)

end CFSG.HardMathSupport.Timmesfeld.CrossChar
