module

public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.FamOpen
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.A
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.AOne
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.AOneEight
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.AQ2
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.TwistedA
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.SympFive
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.OrthFive
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.OrthInnerThree
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.OrthOuterThree
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.D4Dichotomy
public import CFSG.HardMathSupport.Solomon.Coordinator.I19_6D4Outer

public section

namespace CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance Module
  CFSG.HardMathSupport.Timmesfeld.Coordinator CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.RankThree.PartOne CFSG.RankThree.Classical2 CFSG.Assembly.LowTwoRank
  CFSG.HardMathSupport.Timmesfeld.DefChar CFSG.HardMathSupport.Timmesfeld.LocalTwo
  CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.RankThree.PartTwo.Census CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  CFSG.LieType.Universal.Spin CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear

private theorem four_le_card_of_ne {q : TauCeti.PrimePower} (h2 : q.card ≠ 2) (h3 : q.p ≠ 3) :
    4 ≤ q.card := by
  have hq2 : 2 ≤ q.card := by
    have := q.prime_p.two_le
    have : q.p ≤ q.card := by
      rw [TauCeti.PrimePower.card_def]
      exact Nat.le_self_pow q.exponent_pos.ne' _
    omega
  have h3' : q.card ≠ 3 := by
    intro h
    apply h3
    have hd : q.p ∣ 3 := by
      rw [← h, TauCeti.PrimePower.card_def]
      exact dvd_pow_self _ q.exponent_pos.ne'
    exact (Nat.prime_dvd_prime_iff_eq q.prime_p Nat.prime_three).1 hd
  omega

private theorem card_ne_two_of_p_ne_two {q : TauCeti.PrimePower} (h : q.p ≠ 2) : q.card ≠ 2 := by
  intro hc
  apply h
  have hd : q.p ∣ 2 := by
    rw [← hc, TauCeti.PrimePower.card_def]
    exact dvd_pow_self _ q.exponent_pos.ne'
  exact (Nat.prime_dvd_prime_iff_eq q.prime_p Nat.prime_two).1 hd

theorem localTwoCrossFamCat_three_A : LocalTwoCrossFamCat 3 .A := by
  rintro ⟨d, hv⟩ hk hc hnexc
  obtain ⟨m, q, hd⟩ := hk
  change d = _ at hd
  subst hd
  have hm : 1 ≤ m := ((TauCeti.LieTypeIndex.inStandardRange_iff _).1
    ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1).1
  by_cases hm1 : m = 1
  · subst hm1
    by_cases h8 : q.card = 8
    · exact localTwoCrossFamAt_three_A_one_eight ⟨.A 1 q, hv⟩ ⟨1, q, rfl⟩ ⟨q, rfl, h8⟩ hc hnexc
    · exact localTwoCrossFamAt_A_one 3 (Or.inl rfl) ⟨.A 1 q, hv⟩ ⟨1, q, rfl⟩
        ⟨q, rfl, fun _ => h8⟩ hc hnexc
  · have hm2 : 2 ≤ m := by omega
    by_cases h2 : q.card = 2
    · exact localTwoCrossFamAt_three_A_two ⟨.A m q, hv⟩ ⟨m, q, rfl⟩ ⟨m, q, rfl, hm2, h2⟩ hc hnexc
    · exact localTwoCrossFamAt_A_ge_two 3 (Or.inl rfl) ⟨.A m q, hv⟩ ⟨m, q, rfl⟩
        ⟨m, q, rfl, hm2, fun _ => h2⟩ hc hnexc

theorem localTwoCrossFamCat_five_A : LocalTwoCrossFamCat 5 .A := by
  rintro ⟨d, hv⟩ hk hc hnexc
  obtain ⟨m, q, hd⟩ := hk
  change d = _ at hd
  subst hd
  have hm : 1 ≤ m := ((TauCeti.LieTypeIndex.inStandardRange_iff _).1
    ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1).1
  by_cases hm1 : m = 1
  · subst hm1
    exact localTwoCrossFamAt_A_one 5 (Or.inr rfl) ⟨.A 1 q, hv⟩ ⟨1, q, rfl⟩
      ⟨q, rfl, fun h => absurd h (by norm_num)⟩ hc hnexc
  · exact localTwoCrossFamAt_A_ge_two 5 (Or.inr rfl) ⟨.A m q, hv⟩ ⟨m, q, rfl⟩
      ⟨m, q, rfl, by omega, fun h => absurd h (by norm_num)⟩ hc hnexc

theorem localTwoCrossFamCat_three_twistedA (hU2 : PSUTwoThreeBalance) :
    LocalTwoCrossFamCat 3 .twistedA := by
  rintro ⟨d, hv⟩ hk hc hnexc
  obtain ⟨m, q, hd⟩ := hk
  change d = _ at hd
  subst hd
  by_cases h2 : q.card = 2
  · exact hU2 ⟨.twistedA m q, hv⟩ ⟨m, q, rfl⟩ ⟨m, q, rfl, h2⟩ hc hnexc
  · exact localTwoCrossFamAt_twistedA_odd 3 (Or.inl rfl) ⟨.twistedA m q, hv⟩ ⟨m, q, rfl⟩
      ⟨m, q, rfl, fun _ => h2⟩ hc hnexc

theorem localTwoCrossFamCat_five_twistedA : LocalTwoCrossFamCat 5 .twistedA := by
  rintro ⟨d, hv⟩ hk hc hnexc
  obtain ⟨m, q, hd⟩ := hk
  change d = _ at hd
  subst hd
  exact localTwoCrossFamAt_twistedA_odd 5 (Or.inr rfl) ⟨.twistedA m q, hv⟩ ⟨m, q, rfl⟩
    ⟨m, q, rfl, fun h => absurd h (by norm_num)⟩ hc hnexc

theorem isLocallyBalancedAbs_two_psp_three {ℓ f r : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f) {K : Type}
    [Field K] (hK : Nat.card K = ℓ ^ f) (hr : 2 ≤ r) (hq : 4 ≤ ℓ ^ f) (hpℓ : 3 ≠ ℓ) :
    IsLocallyBalancedAbs 3 2 (StatedProj (StatedSp r K)) := by
  classical
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; exact pow_ne_zero f hℓ.ne_zero)
  have hrq : ¬ (r = 2 ∧ ℓ ^ f = 2) := fun h => by omega
  have hinj := CFSG.RankThree.PartOne.KCSpFull.spConj_injective hℓ hf hK hr hrq
  refine isLocallyBalancedAbs_two_of_planes_and_fields Nat.prime_three hinj ?_
    (outerFields_psp_odd hℓ hf hK hr Nat.prime_three (by norm_num) hpℓ)
  intro E hEin hE hEc H hH
  exact localDeltaIn_eq_bot_psp_q hℓ hf hK hq Nat.prime_three (by norm_num) hpℓ hr E hEin hE hEc hH

theorem localTwoCrossFamAt_three_B_symplectic :
    LocalTwoCrossFamAt 3 .B fun idx =>
      ∃ (r : ℕ) (q : TauCeti.PrimePower), idx.1 = .B r q ∧ (r = 2 ∨ q.p = 2) ∧ q.card ≠ 2 := by
  rintro ⟨d, hv⟩ hk ⟨r, q, hd, hsp, hq2c⟩ hc hnexc
  change d = _ at hd
  subst hd
  have hrange := (TauCeti.LieTypeIndex.inStandardRange_iff _).1
    ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
  have := CFSG.QuasithinUnique.SQTK.finite_validIndex_fixedField
    (⟨.B r q, hv⟩ : TauCeti.ValidLieTypeIndex)
  have hK : Nat.card ↥(TauCeti.ValidLieTypeIndex.fixedField
      (⟨.B r q, hv⟩ : TauCeti.ValidLieTypeIndex)) = q.p ^ q.exponent := by
    rw [TauCeti.ValidLieTypeIndex.card_fixedField]
    simp [TauCeti.ValidLieTypeIndex.fieldOrder]
  have hpq : 3 ≠ q.p := fun h => hc (by simp [h])
  have hq4 : 4 ≤ q.p ^ q.exponent := by
    have := four_le_card_of_ne hq2c (fun h => hpq h.symm)
    rwa [TauCeti.PrimePower.card_def] at this
  by_cases hr2 : r = 2
  · subst hr2
    exact IsLocallyBalancedAbs.of_mulEquiv
      (CFSG.QuasithinUnique.SQTK.typeB2GroupEquivStatedProj q hv)
      (isLocallyBalancedAbs_two_psp_three q.prime_p q.exponent_pos hK le_rfl hq4 hpq)
  · have hq2 : q.p = 2 := hsp.resolve_left hr2
    have hr3 : 3 ≤ r := by
      have := hrange.1
      omega
    exact IsLocallyBalancedAbs.of_mulEquiv
      (CFSG.RankThree.PartTwo.Census.Carrier.SpinB.typeBGroupEquivStatedProj r q hv hq2 hr3)
      (isLocallyBalancedAbs_two_psp_three q.prime_p q.exponent_pos hK (by omega) hq4 hpq)

theorem localTwoCrossFamCat_three_C : LocalTwoCrossFamCat 3 .C := by
  rintro ⟨d, hv⟩ ⟨r, q, hd⟩ hc _
  change d = _ at hd
  subst hd
  have hrange := (TauCeti.LieTypeIndex.inStandardRange_iff _).1
    ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
  have hr : 3 ≤ r := hrange.1
  have hq2 : q.p ≠ 2 := hrange.2
  have := CFSG.QuasithinUnique.SQTK.finite_validIndex_fixedField
    (⟨.C r q, hv⟩ : TauCeti.ValidLieTypeIndex)
  have hK : Nat.card ↥(TauCeti.ValidLieTypeIndex.fixedField
      (⟨.C r q, hv⟩ : TauCeti.ValidLieTypeIndex)) = q.p ^ q.exponent := by
    rw [TauCeti.ValidLieTypeIndex.card_fixedField]
    simp [TauCeti.ValidLieTypeIndex.fieldOrder]
  have hpq : 3 ≠ q.p := fun h => hc (by simp [h])
  have hq4 : 4 ≤ q.p ^ q.exponent := by
    have := four_le_card_of_ne (card_ne_two_of_p_ne_two hq2) (fun h => hpq h.symm)
    rwa [TauCeti.PrimePower.card_def] at this
  exact IsLocallyBalancedAbs.of_mulEquiv
    (CFSG.QuasithinUnique.SQTK.typeCGroupEquivStatedProj r q hv)
    (isLocallyBalancedAbs_two_psp_three q.prime_p q.exponent_pos hK (by omega) hq4 hpq)

theorem localTwoCrossFamAt_three_B_orth :
    LocalTwoCrossFamAt 3 .B fun idx => regimeBOrthTwo idx 3 := by
  rintro ⟨d, hv⟩ hk ⟨r, q, hd, hq2, hr⟩ hc hnexc
  change d = _ at hd
  subst hd
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  set F := ↥(TauCeti.ValidLieTypeIndex.fixedField ⟨.B r q, hv⟩) with hF
  have : Finite F := CFSG.QuasithinUnique.SQTK.finite_validIndex_fixedField _
  have hcard : Nat.card F = q.p ^ q.exponent :=
    card_fixedField_validIndex_orth ⟨.B r q, hv⟩ r q (Or.inl rfl)
  have hpq : 3 ≠ q.p := fun h => hc (by simp [h])
  let e₁ := Carrier.SpinB.typeBGroupEquivStatedProj_odd r q hv hq2 hr
  have hmodel : StatedClassicalModel (Cat ⟨.B r q, hv⟩) .POmegaOdd r q.p q.exponent :=
    statedClassicalModel_typeB_odd r q hv hq2 hr (MulEquiv.refl _)
  obtain ⟨-, hnd, hT, -, -, -⟩ := coordinate_model_witness_odd hmodel F hcard e₁
  have hinjP := CFSG.RankThree.PartOne.K133C.conj_injective_of_center_bot
    (CFSG.RankThree.PartOne.KCOrthogonalSubfield.center_matrix_eq_bot (by omega) hnd hT)
  have hfin : Finite (matrixProjectiveDerived (coordinateQuadOdd r F)) := inferInstance
  have hout := outerFields_matrix_odd_three hmodel hpq F hcard e₁ hinjP
  have hin := (innerPlaneBalance_three_B_orth r q hv hq2 hr (fun h => hpq h.symm)).of_mulEquiv
    (coordinateOddWitnessEquiv F e₁).symm
  exact isLocallyBalancedAbs_two_of_model (coordinateOddWitnessEquiv F e₁) Nat.prime_three hinjP
    hin hout

theorem localTwoCrossFamCat_three_B (hSp : SpTwoThreeBalance) : LocalTwoCrossFamCat 3 .B := by
  rintro ⟨d, hv⟩ hk hc hnexc
  obtain ⟨r, q, hd⟩ := hk
  change d = _ at hd
  subst hd
  have hrange := (TauCeti.LieTypeIndex.inStandardRange_iff _).1
    ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
  by_cases hq2 : q.p = 2
  · by_cases hcard : q.card = 2
    · have hr3 : 3 ≤ r := by
        have h1 := hrange.1
        have h2 := hrange.2
        omega
      exact hSp ⟨.B r q, hv⟩ ⟨r, q, rfl⟩ ⟨r, q, rfl, hr3, hcard⟩ hc hnexc
    · exact localTwoCrossFamAt_three_B_symplectic ⟨.B r q, hv⟩ ⟨r, q, rfl⟩
        ⟨r, q, rfl, Or.inr hq2, hcard⟩ hc hnexc
  · by_cases hr2 : r = 2
    · subst hr2
      have hcard : q.card ≠ 2 := fun h => hrange.2 ⟨rfl, h⟩
      exact localTwoCrossFamAt_three_B_symplectic ⟨.B 2 q, hv⟩ ⟨2, q, rfl⟩
        ⟨2, q, rfl, Or.inl rfl, hcard⟩ hc hnexc
    · have hr3 : 3 ≤ r := by
        have := hrange.1
        omega
      exact localTwoCrossFamAt_three_B_orth ⟨.B r q, hv⟩ ⟨r, q, rfl⟩ ⟨r, q, rfl, hq2, hr3⟩ hc hnexc

theorem localTwoCrossFamCat_five_B : LocalTwoCrossFamCat 5 .B := by
  rintro ⟨d, hv⟩ hk hc hnexc
  obtain ⟨r, q, hd⟩ := hk
  change d = _ at hd
  subst hd
  have hrange := (TauCeti.LieTypeIndex.inStandardRange_iff _).1
    ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
  by_cases hq2 : q.p = 2
  · exact localTwoCrossFamAt_five_B_symplectic ⟨.B r q, hv⟩ ⟨r, q, rfl⟩
      ⟨r, q, rfl, Or.inr hq2⟩ hc hnexc
  · by_cases hr2 : r = 2
    · exact localTwoCrossFamAt_five_B_symplectic ⟨.B r q, hv⟩ ⟨r, q, rfl⟩
        ⟨r, q, rfl, Or.inl hr2⟩ hc hnexc
    · have hr3 : 3 ≤ r := by
        have := hrange.1
        omega
      exact localTwoCrossFamAt_five_B_orth ⟨.B r q, hv⟩ ⟨r, q, rfl⟩ ⟨r, q, rfl, hq2, hr3⟩ hc hnexc

private theorem not_three_dvd_card_of_p_ne {q : TauCeti.PrimePower} (h3 : q.p ≠ 3) :
    ¬ 3 ∣ q.p ^ q.exponent := fun h =>
  h3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three q.prime_p).1
    (Nat.prime_three.dvd_of_dvd_pow h)).symm

theorem innerPlaneBalance_three_D_all (hR6 : OrthTwoThreeInnerBalance) (r : ℕ)
    (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.D r q).Valid) (h3 : q.p ≠ 3) :
    InnerPlaneBalance 3 (CatT ⟨.D r q, hv⟩) := by
  by_cases h2 : q.card = 2
  · exact hR6.1 r q hv h2
  · exact innerPlaneBalance_three_D r q hv h3 (four_le_card_of_ne h2 h3)

theorem innerPlaneBalance_three_twistedD_all (hR6 : OrthTwoThreeInnerBalance) (r : ℕ)
    (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.twistedD r q).Valid) (h3 : q.p ≠ 3) :
    InnerPlaneBalance 3 (CatT ⟨.twistedD r q, hv⟩) := by
  by_cases h2 : q.card = 2
  · exact hR6.2 r q hv h2
  · exact innerPlaneBalance_three_twistedD r q hv h3 (four_le_card_of_ne h2 h3)

theorem isLocallyBalancedAbs_three_D_ge_five (hR6 : OrthTwoThreeInnerBalance) (r : ℕ)
    (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.D r q).Valid) (hr5 : 5 ≤ r)
    (h3 : q.p ≠ 3) : IsLocallyBalancedAbs 3 2 (Cat ⟨.D r q, hv⟩) := by
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  set F := ↥(TauCeti.ValidLieTypeIndex.fixedField ⟨.D r q, hv⟩) with hF
  have : Finite F := CFSG.QuasithinUnique.SQTK.finite_validIndex_fixedField _
  have hcard : Nat.card F = q.p ^ q.exponent :=
    card_fixedField_validIndex_orth ⟨.D r q, hv⟩ r q (Or.inr (Or.inl rfl))
  have hpq : 3 ≠ q.p := fun h => h3 h.symm
  let e₁ := Carrier.SpinD.typeDGroupEquivStatedProj_of_valid r q hv
  have hmodel : StatedClassicalModel (Cat ⟨.D r q, hv⟩) .POmegaPlus r q.p q.exponent :=
    statedClassicalModel_typeD r q hv (MulEquiv.refl _)
  obtain ⟨-, hnd, hT, -⟩ := coordinate_model_witness_plus hmodel F hcard e₁
  have hinjP := CFSG.RankThree.PartOne.K133C.conj_injective_of_center_bot
    (CFSG.RankThree.PartOne.KCOrthogonalSubfield.center_matrix_eq_bot (by omega) hnd hT)
  have hfin : Finite (matrixProjectiveDerived (coordinateQuadPlus r F)) := inferInstance
  have hout := outerFields_matrix_plus_three hmodel (by omega) hpq F hcard e₁ hinjP
  have hin := (innerPlaneBalance_three_D_all hR6 r q hv h3).of_mulEquiv
    (coordinatePlusWitnessEquiv F e₁).symm
  exact isLocallyBalancedAbs_two_of_model (coordinatePlusWitnessEquiv F e₁) Nat.prime_three hinjP
    hin hout

theorem isLocallyBalancedAbs_three_D_four (hR6 : OrthTwoThreeInnerBalance)
    (hR7 : D4TrialityPlaneThreeBalance) (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.D 4 q).Valid) (h3 : q.p ≠ 3) :
    IsLocallyBalancedAbs 3 2 (Cat ⟨.D 4 q, hv⟩) := by
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  set F := ↥(TauCeti.ValidLieTypeIndex.fixedField ⟨.D 4 q, hv⟩) with hF
  have : Finite F := CFSG.QuasithinUnique.SQTK.finite_validIndex_fixedField _
  have hcard : Nat.card F = q.p ^ q.exponent :=
    card_fixedField_validIndex_orth ⟨.D 4 q, hv⟩ 4 q (Or.inr (Or.inl rfl))
  let e₁ := Carrier.SpinD.typeDGroupEquivStatedProj_of_valid 4 q hv
  have hmodel : StatedClassicalModel (Cat ⟨.D 4 q, hv⟩) .POmegaPlus 4 q.p q.exponent :=
    statedClassicalModel_typeD 4 q hv (MulEquiv.refl _)
  have hin' : InnerPlaneBalance 3 (matrixProjectiveDerived (coordinateQuadPlus 4 F)) :=
    (innerPlaneBalance_three_D_all hR6 4 q hv h3).of_mulEquiv (coordinatePlusWitnessEquiv F e₁).symm
  have hnF : ¬ 3 ∣ Nat.card F := by
    rw [hcard]
    exact not_three_dvd_card_of_p_ne h3
  refine IsLocallyBalancedAbs.of_mulEquiv (coordinatePlusWitnessEquiv F e₁) ?_
  intro D hD hcard9 H hH hDH
  rcases d4_plane_trichotomy (Cat ⟨.D 4 q, hv⟩) hmodel F hcard e₁ D hD hcard9 with
    hin1 | ⟨a, haD, haE, haL, ha3⟩ | ⟨t, htD, htE, hDE⟩
  · exact hin' D hin1 hD hcard9 H hH
  · exact i196_d4_localDeltaIn_eq_bot_of_field (Cat ⟨.D 4 q, hv⟩) hmodel F hcard e₁ a haE haL ha3
      haD hH
  · exact hR7 F hnF D hD hcard9 ⟨t, htD, htE⟩ hDE H hH hDH

theorem localTwoCrossFamCat_three_D (hR6 : OrthTwoThreeInnerBalance)
    (hR7 : D4TrialityPlaneThreeBalance) : LocalTwoCrossFamCat 3 .D := by
  rintro ⟨d, hv⟩ ⟨r, q, hd⟩ hc _
  change d = _ at hd
  subst hd
  have hr4 : 4 ≤ r := (TauCeti.LieTypeIndex.inStandardRange_iff _).mp
    ((TauCeti.LieTypeIndex.valid_iff _).mp hv).1
  have h3 : q.p ≠ 3 := fun h => hc (by simp [h])
  by_cases hr : r = 4
  · subst hr
    exact isLocallyBalancedAbs_three_D_four hR6 hR7 q hv h3
  · exact isLocallyBalancedAbs_three_D_ge_five hR6 r q hv (by omega) h3

theorem localTwoCrossFamCat_three_twistedD (hR6 : OrthTwoThreeInnerBalance) :
    LocalTwoCrossFamCat 3 .twistedD := by
  rintro ⟨d, hv⟩ ⟨r, q, hd⟩ hc _
  change d = _ at hd
  subst hd
  have hr4 : 4 ≤ r := (TauCeti.LieTypeIndex.inStandardRange_iff _).mp
    ((TauCeti.LieTypeIndex.valid_iff _).mp hv).1
  have h3 : q.p ≠ 3 := fun h => hc (by simp [h])
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  set F := ↥(TauCeti.ValidLieTypeIndex.fixedField ⟨.twistedD r q, hv⟩) with hF
  have : Finite F := CFSG.QuasithinUnique.SQTK.finite_validIndex_fixedField _
  have hcard : Nat.card F = q.p ^ q.exponent :=
    card_fixedField_validIndex_orth ⟨.twistedD r q, hv⟩ r q (Or.inr (Or.inr rfl))
  have hpq : 3 ≠ q.p := fun h => h3 h.symm
  obtain ⟨b, c, hirr, ⟨e₁⟩⟩ := Carrier.SpinD.exists_typeTwistedDGroupEquivStatedProj_of_valid r q hv
  have hmodel : StatedClassicalModel (Cat ⟨.twistedD r q, hv⟩) .POmegaMinus r q.p q.exponent :=
    statedClassicalModel_typeTwistedD r q hv (MulEquiv.refl _)
  have hn : 1 ≤ r := by omega
  obtain ⟨-, hnd, hT, -⟩ := coordinate_model_witness_minus hmodel F hcard b c hirr e₁
  have hinjP := CFSG.RankThree.PartOne.K133C.conj_injective_of_center_bot
    (CFSG.RankThree.PartOne.KCOrthogonalSubfield.center_matrix_eq_bot (by omega) hnd hT)
  have hfin : Finite (matrixProjectiveDerived (coordinateQuadMinus r F hn b c)) := inferInstance
  have hout := outerFields_matrix_minus_three hmodel hn hpq F hcard b c hirr e₁ hinjP
  have hin := (innerPlaneBalance_three_twistedD_all hR6 r q hv h3).of_mulEquiv
    (coordinateMinusWitnessEquiv F hn b c e₁).symm
  exact isLocallyBalancedAbs_two_of_model (coordinateMinusWitnessEquiv F hn b c e₁)
    Nat.prime_three hinjP hin hout

end CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross
