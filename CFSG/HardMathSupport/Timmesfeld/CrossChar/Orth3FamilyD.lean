module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.Orth3Family

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance Module
  CFSG.HardMathSupport.Timmesfeld.Coordinator CFSG.RankThree.PartOne
  CFSG.RankThree.Classical2 CFSG.Assembly.LowTwoRank CFSG.RankThree.PartTwo.Census
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData CFSG.LieType.Universal.Spin

@[expose] def regimeDOrth3Split (idx : TauCeti.ValidLieTypeIndex) (p : ℕ) : Prop :=
  ∃ (r : ℕ) (q : TauCeti.PrimePower), idx.1 = .D r q ∧ 5 ≤ r ∧ p = 3 ∧ 3 ∣ q.card - 1

@[expose] def regimeTwistedDOrth3Split (idx : TauCeti.ValidLieTypeIndex) (p : ℕ) : Prop :=
  ∃ (r : ℕ) (q : TauCeti.PrimePower), idx.1 = .twistedD r q ∧ p = 3 ∧ 3 ∣ q.card - 1

theorem four_le_card_of_three_dvd_sub_one {q : TauCeti.PrimePower} (h : 3 ∣ q.card - 1) :
    4 ≤ q.card := by
  have hq : q.card = q.p ^ q.exponent := TauCeti.PrimePower.card_def q
  have h2 : 2 ≤ q.card := by
    rw [hq]
    exact q.prime_p.two_le.trans (Nat.le_self_pow q.exponent_pos.ne' _)
  omega

theorem crossCharFamAt_D_orth3_split : CrossCharFamAt .D regimeDOrth3Split := by
  rintro ⟨d, hv⟩ _ p hp hp2 hc ⟨r, q, hd, hr5, rfl, hpq3⟩
  change d = _ at hd
  subst hd
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  have hr : 4 ≤ r := by omega
  set F := ↥(TauCeti.ValidLieTypeIndex.fixedField ⟨.D r q, hv⟩) with hF
  have : Finite F := CFSG.QuasithinUnique.SQTK.finite_validIndex_fixedField _
  have hcard : Nat.card F = q.p ^ q.exponent :=
    card_fixedField_validIndex_orth ⟨.D r q, hv⟩ r q (Or.inr (Or.inl rfl))
  have hring : ringChar F = q.p :=
    CFSG.ClassicalGroups.Orthogonal.ringChar_eq_of_card_eq q.prime_p q.exponent_pos hcard
  have hpq : 3 ≠ q.p := fun h => hc (by simp [h])
  have hpl : 3 ≠ ringChar F := by rw [hring]; exact hpq
  have hqc : q.card = q.p ^ q.exponent := TauCeti.PrimePower.card_def q
  have hK4 : 4 ≤ Nat.card F := by
    rw [hcard, ← hqc]
    exact four_le_card_of_three_dvd_sub_one hpq3
  have hpqF : 3 ∣ Nat.card F - 1 := by
    rw [hcard, ← hqc]
    exact hpq3
  obtain ⟨hQ, hT⟩ := CFSG.ClassicalGroups.Orthogonal.regular_quadPlus (n := r) (K := F)
    (by omega)
  let e₁ := Carrier.SpinD.typeDGroupEquivStatedProj_of_valid r q hv
  obtain ⟨e₂⟩ := CFSG.RankThree.CentralLift.nonempty_statedProj_mulEquiv_projOrthDerived
    (coe_quadPlus r F)
  let e : Cat ⟨.D r q, hv⟩ ≃* ProjOrthDerived (quadPlus r F) := e₁.trans e₂
  have hmodelT := statedClassicalModel_typeD r q hv e.symm
  have hO : OutStructure.OutPChain 3 (ProjOrthDerived (quadPlus r F)) :=
    (CFSG.LocalAnalysis.RankThreeTheoremC.outPNice_POmegaPlus_ge_five_of_ne_two hp hp2
      hr5 hmodelT).toChain
  exact IsLocallyBalancedAbs.of_mulEquiv e
    (isLocallyBalancedAbs_projOrth3 hQ hT hp hp2 hK4 hpl
      (fun A hA hAc g hg => orth3_split_derived_rigid hQ hT hp hp2 hpqF A
        ⟨hA.1, hA.2⟩ hAc g hg) hO)

theorem crossCharFamAt_twistedD_orth3_split :
    CrossCharFamAt .twistedD regimeTwistedDOrth3Split := by
  rintro ⟨d, hv⟩ _ p hp hp2 hc ⟨r, q, hd, rfl, hpq3⟩
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
  have hpq : 3 ≠ q.p := fun h => hc (by simp [h])
  have hpl : 3 ≠ ringChar F := by rw [hring]; exact hpq
  have hqc : q.card = q.p ^ q.exponent := TauCeti.PrimePower.card_def q
  have hK4 : 4 ≤ Nat.card F := by
    rw [hcard, ← hqc]
    exact four_le_card_of_three_dvd_sub_one hpq3
  have hpqF : 3 ∣ Nat.card F - 1 := by
    rw [hcard, ← hqc]
    exact hpq3
  obtain ⟨b, c, hirr, ⟨e₁⟩⟩ := Carrier.SpinD.exists_typeTwistedDGroupEquivStatedProj_of_valid r q hv
  obtain ⟨hQ, hT⟩ := CFSG.ClassicalGroups.Orthogonal.regular_quadMinus (n := r) (K := F) (b := b)
    (c := c) hr hirr
  obtain ⟨e₂⟩ := CFSG.RankThree.CentralLift.nonempty_statedProj_mulEquiv_projOrthDerived
    (coe_quadMinus r F b c)
  let e : Cat ⟨.twistedD r q, hv⟩ ≃* ProjOrthDerived (quadMinus r F b c) := e₁.trans e₂
  have hO : OutStructure.OutPChain 3 (ProjOrthDerived (quadMinus r F b c)) :=
    (CFSG.LocalAnalysis.RankThreeTheoremC.outPNice_POmegaMinus_of_ne_two hp hp2
      (statedClassicalModel_typeTwistedD r q hv e.symm)).toChain
  exact IsLocallyBalancedAbs.of_mulEquiv e
    (isLocallyBalancedAbs_projOrth3 hQ hT hp hp2 hK4 hpl
      (fun A hA hAc g hg => orth3_split_derived_rigid hQ hT hp hp2 hpqF A
        ⟨hA.1, hA.2⟩ hAc g hg) hO)

end CFSG.HardMathSupport.Timmesfeld.CrossChar
