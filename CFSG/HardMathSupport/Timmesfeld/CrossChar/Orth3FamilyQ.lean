module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.Orth3QPlus
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.Orth3ResidualD

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance Module
  CFSG.HardMathSupport.Timmesfeld.Coordinator CFSG.RankThree.PartOne
  CFSG.RankThree.Classical2 CFSG.Assembly.LowTwoRank CFSG.RankThree.PartTwo.Census
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData CFSG.LieType.Universal.Spin

@[expose] def regimeBOrth3Nonsplit (idx : TauCeti.ValidLieTypeIndex) (p : ℕ) : Prop :=
  ∃ (r : ℕ) (q : TauCeti.PrimePower), idx.1 = .B r q ∧ q.p ≠ 2 ∧ 3 ≤ r ∧ p = 3 ∧
    3 ∣ q.card + 1

@[expose] def regimeDOrth3Nonsplit (idx : TauCeti.ValidLieTypeIndex) (p : ℕ) : Prop :=
  ∃ (r : ℕ) (q : TauCeti.PrimePower), idx.1 = .D r q ∧ 5 ≤ r ∧ p = 3 ∧ 3 ∣ q.card + 1 ∧
    q.card ≠ 2

@[expose] def regimeTwistedDOrth3Nonsplit (idx : TauCeti.ValidLieTypeIndex) (p : ℕ) : Prop :=
  ∃ (r : ℕ) (q : TauCeti.PrimePower), idx.1 = .twistedD r q ∧ p = 3 ∧ 3 ∣ q.card + 1 ∧
    q.card ≠ 2

theorem four_le_card_of_three_dvd_add_one {q : TauCeti.PrimePower} (h : 3 ∣ q.card + 1)
    (h2 : q.card ≠ 2) : 4 ≤ q.card := by
  have hq : q.card = q.p ^ q.exponent := TauCeti.PrimePower.card_def q
  have : 2 ≤ q.card := by
    rw [hq]
    exact q.prime_p.two_le.trans (Nat.le_self_pow q.exponent_pos.ne' _)
  omega

theorem orth3_aut_semilinear_quadMinus {K : Type} [Field K] [Finite K] (n : ℕ) (hn4 : 4 ≤ n)
    (b c : K) (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (α : MulAut (ProjOrthDerived (quadMinus n K b c))) :
    KCOrthogonalAut.InducedBySemilinear (quadMinus n K b c) α := by
  let S := (coordinateMinusIsometry n K (by omega) b c).toLinearEquiv
  refine KCOrthogonalAut.inducedBySemilinear_of_similarity S 1 (fun v => ?_)
    (KCOrthogonalAut.inducedBySemilinear_of_image_eq_top (by omega) _
      (KCOrthogonalAut.matrixProjectiveImage_eq_top_minus K n hn4 b c hirr)) α
  change coordinateQuadMinus n K (by omega) b c
    ((coordinateMinusIsometry n K (by omega) b c) v) = ((1 : Kˣ) : K) * quadMinus n K b c v
  rw [(coordinateMinusIsometry n K (by omega) b c).map_app, Units.val_one, one_mul]

theorem crossCharFamAt_B_orth3_nonsplit : CrossCharFamAt .B regimeBOrth3Nonsplit := by
  rintro ⟨d, hv⟩ _ p hp hp2 hc ⟨r, q, hd, hq2, hr, rfl, hpq3⟩
  change d = _ at hd
  subst hd
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  set F := ↥(TauCeti.ValidLieTypeIndex.fixedField ⟨.B r q, hv⟩) with hF
  have : Finite F := CFSG.QuasithinUnique.SQTK.finite_validIndex_fixedField _
  have hcard : Nat.card F = q.p ^ q.exponent :=
    card_fixedField_validIndex_orth ⟨.B r q, hv⟩ r q (Or.inl rfl)
  have hring : ringChar F = q.p :=
    CFSG.ClassicalGroups.Orthogonal.ringChar_eq_of_card_eq q.prime_p q.exponent_pos hcard
  have hpq : 3 ≠ q.p := fun h => hc (by simp [h])
  have hpl : 3 ≠ ringChar F := by rw [hring]; exact hpq
  have h2 : (2 : F) ≠ 0 := by
    have : CharP F q.p := ringChar.of_eq hring
    intro h
    have : q.p ∣ 2 := (CharP.cast_eq_zero_iff F q.p 2).mp (by exact_mod_cast h)
    exact hq2 ((Nat.prime_dvd_prime_iff_eq q.prime_p Nat.prime_two).mp this)
  have hqc : q.card = q.p ^ q.exponent := TauCeti.PrimePower.card_def q
  have hK4 : 4 ≤ Nat.card F := by
    rw [hcard]
    have h1 : q.p ≤ q.p ^ q.exponent := Nat.le_self_pow q.exponent_pos.ne' _
    have h5 := q.prime_p.two_le
    have : q.p ≠ 3 := fun h => hpq h.symm
    omega
  have hpqF : 3 ∣ Nat.card F + 1 := by
    rw [hcard, ← hqc]
    exact hpq3
  obtain ⟨hQ, hT⟩ := CFSG.ClassicalGroups.Orthogonal.regular_quadOdd (n := r) (K := F) h2 hr
  let e₁ := Carrier.SpinB.typeBGroupEquivStatedProj_odd r q hv hq2 hr
  obtain ⟨e₂⟩ := CFSG.RankThree.CentralLift.nonempty_statedProj_mulEquiv_projOrthDerived
    (coe_quadOdd r F)
  let e : Cat ⟨.B r q, hv⟩ ≃* ProjOrthDerived (quadOdd r F) := e₁.trans e₂
  have hO : OutStructure.OutPChain 3 (ProjOrthDerived (quadOdd r F)) :=
    (CFSG.LocalAnalysis.RankThreeTheoremC.outPNice_POmegaOdd_of_ne_two hp hp2
      (statedClassicalModel_typeB_odd r q hv hq2 hr e.symm)).toChain
  have hdim : finrank F (Fin r ⊕ Fin r ⊕ Unit → F) = 2 * r + 1 := by
    simp [Module.finrank_fintype_fun_eq_card]
    omega
  have hnat : ∀ α : MulAut (ProjOrthDerived (quadOdd r F)),
      KCOrthogonalAut.InducedBySemilinear (quadOdd r F) α := fun α =>
    KCOrthogonalAut.orthogonal_aut_semilinear_of_seven_le _ hQ (by omega)
      (fun h8 => by omega) α
  exact IsLocallyBalancedAbs.of_mulEquiv e
    (isLocallyBalancedAbs_projOrth3 hQ hT hp hp2 hK4 hpl
      (fun A hA hAc g hg => orth3_qplus_derived_rigid hQ hT hp hp2 hK4 hpl hpqF hnat A
        ⟨hA.1, hA.2⟩ hAc g hg) hO)

theorem crossCharFamAt_D_orth3_nonsplit : CrossCharFamAt .D regimeDOrth3Nonsplit := by
  rintro ⟨d, hv⟩ _ p hp hp2 hc ⟨r, q, hd, hr5, rfl, hpq3, hq2⟩
  change d = _ at hd
  subst hd
  have : Fact q.p.Prime := ⟨q.prime_p⟩
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
    exact four_le_card_of_three_dvd_add_one hpq3 hq2
  have hpqF : 3 ∣ Nat.card F + 1 := by
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
  have hdim : finrank F (Fin r ⊕ Fin r → F) = 2 * r := by
    simp [Module.finrank_fintype_fun_eq_card]
    omega
  have hnat : ∀ α : MulAut (ProjOrthDerived (quadPlus r F)),
      KCOrthogonalAut.InducedBySemilinear (quadPlus r F) α := fun α =>
    KCOrthogonalAut.orthogonal_aut_semilinear_of_seven_le _ hQ (by omega)
      (fun h8 => by omega) α
  exact IsLocallyBalancedAbs.of_mulEquiv e
    (isLocallyBalancedAbs_projOrth3 hQ hT hp hp2 hK4 hpl
      (fun A hA hAc g hg => orth3_qplus_derived_rigid hQ hT hp hp2 hK4 hpl hpqF hnat A
        ⟨hA.1, hA.2⟩ hAc g hg) hO)

theorem crossCharFamAt_twistedD_orth3_nonsplit :
    CrossCharFamAt .twistedD regimeTwistedDOrth3Nonsplit := by
  rintro ⟨d, hv⟩ _ p hp hp2 hc ⟨r, q, hd, rfl, hpq3, hq2⟩
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
    exact four_le_card_of_three_dvd_add_one hpq3 hq2
  have hpqF : 3 ∣ Nat.card F + 1 := by
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
      (fun A hA hAc g hg => orth3_qplus_derived_rigid hQ hT hp hp2 hK4 hpl hpqF
        (orth3_aut_semilinear_quadMinus r hr b c hirr) A ⟨hA.1, hA.2⟩ hAc g hg) hO)

end CFSG.HardMathSupport.Timmesfeld.CrossChar
