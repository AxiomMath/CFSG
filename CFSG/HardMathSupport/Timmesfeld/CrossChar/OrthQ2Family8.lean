module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.OrthQ2Main8
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.OrthQ2Family
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.Orth3FamilyQ

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance Module
  CFSG.HardMathSupport.Timmesfeld.Coordinator CFSG.RankThree.PartOne
  CFSG.RankThree.Classical2 CFSG.Assembly.LowTwoRank CFSG.RankThree.PartTwo.Census
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData CFSG.LieType.Universal.Spin

theorem isLocallyBalancedAbs_orth_two_eight {K : Type} [Field K] [Finite K] {V : Type}
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V}
    (hK : Nat.card K = 2) (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hT : ∃ U : Submodule K V, finrank K U = 3 ∧ ∀ u ∈ U, Q u = 0) (h8 : 8 ≤ finrank K V)
    (hsemi : ∀ α : MulAut (ProjOrthDerived Q), KCOrthogonalAut.InducedBySemilinear Q α) :
    IsLocallyBalancedAbs 3 3 (ProjOrthDerived Q) := by
  intro D hD hcard H hH _
  exact localDeltaIn_eq_bot_orth_two_eight hK hQ hT h8 hsemi hD hcard hH

@[expose] def regimeDTwoFive (idx : TauCeti.ValidLieTypeIndex) (p : ℕ) : Prop :=
  p = 3 ∧ ∃ (r : ℕ) (q : TauCeti.PrimePower), idx.1 = .D r q ∧ q.card = 2 ∧ 5 ≤ r

theorem crossCharFamAt_D_two_five : CrossCharFamAt .D regimeDTwoFive := by
  rintro ⟨d, hv⟩ _ p hp hp2 hc ⟨rfl, r, q, hd, hq2, hr5⟩
  change d = _ at hd
  subst hd
  set F := ↥(TauCeti.ValidLieTypeIndex.fixedField ⟨.D r q, hv⟩) with hF
  have : Finite F := CFSG.QuasithinUnique.SQTK.finite_validIndex_fixedField _
  have hK : Nat.card F = 2 := card_fixedField_eq_two_of_card (Or.inl rfl) hq2
  obtain ⟨hQ, hT⟩ := CFSG.ClassicalGroups.Orthogonal.regular_quadPlus (n := r) (K := F)
    (by omega)
  let e₁ := Carrier.SpinD.typeDGroupEquivStatedProj_of_valid r q hv
  obtain ⟨e₂⟩ := CFSG.RankThree.CentralLift.nonempty_statedProj_mulEquiv_projOrthDerived
    (coe_quadPlus r F)
  let e : Cat ⟨.D r q, hv⟩ ≃* ProjOrthDerived (quadPlus r F) := e₁.trans e₂
  have hdim : finrank F (Fin r ⊕ Fin r → F) = r + r := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin]
  exact IsLocallyBalancedAbs.of_mulEquiv e
    (isLocallyBalancedAbs_orth_two_eight hK hQ hT (by omega)
      (fun α => KCOrthogonalAut.orthogonal_aut_semilinear_of_seven_le _ hQ (by omega)
        (fun h8 => by omega) α))

theorem crossCharFamAt_twistedD_two : CrossCharFamAt .twistedD fun idx p =>
    p = 3 ∧ ∃ (r : ℕ) (q : TauCeti.PrimePower), idx.1 = .twistedD r q ∧ q.card = 2 := by
  rintro ⟨d, hv⟩ _ p hp hp2 hc ⟨rfl, r, q, hd, hq2⟩
  change d = _ at hd
  subst hd
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
  let e : Cat ⟨.twistedD r q, hv⟩ ≃* ProjOrthDerived (quadMinus r F b c) := e₁.trans e₂
  have hdim : finrank F (Fin (r - 1) ⊕ Fin (r - 1) ⊕ Fin 2 → F) = (r - 1) + ((r - 1) + 2) := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_sum, Fintype.card_fin,
      Fintype.card_fin]
  exact IsLocallyBalancedAbs.of_mulEquiv e
    (isLocallyBalancedAbs_orth_two_eight hK hQ hT (by omega)
      (orth3_aut_semilinear_quadMinus r hr4 b c hirr))

end CFSG.HardMathSupport.Timmesfeld.CrossChar
