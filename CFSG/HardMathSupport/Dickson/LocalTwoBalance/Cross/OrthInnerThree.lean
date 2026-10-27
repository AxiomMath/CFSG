module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.Orth3FamilyQ
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.CrossLin
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.OrthD4Plane

public section

namespace CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance Module
  CFSG.HardMathSupport.Timmesfeld.Coordinator CFSG.RankThree.PartOne CFSG.RankThree.Classical2
  CFSG.Assembly.LowTwoRank CFSG.RankThree.PartTwo.Census
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear CFSG.LieType.Universal.Spin
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.LocalTwo

theorem innerPlaneBalance_three_B_orth (r : ℕ) (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.B r q).Valid) (hq2 : q.p ≠ 2) (hr3 : 3 ≤ r) (h3 : q.p ≠ 3) :
    InnerPlaneBalance 3 (Cat ⟨.B r q, hv⟩) := by
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  set F := ↥(TauCeti.ValidLieTypeIndex.fixedField ⟨.B r q, hv⟩) with hF
  have : Finite F := CFSG.QuasithinUnique.SQTK.finite_validIndex_fixedField _
  have hcard : Nat.card F = q.p ^ q.exponent :=
    card_fixedField_validIndex_orth ⟨.B r q, hv⟩ r q (Or.inl rfl)
  have hqc : q.card = q.p ^ q.exponent := TauCeti.PrimePower.card_def q
  have hring : ringChar F = q.p :=
    CFSG.ClassicalGroups.Orthogonal.ringChar_eq_of_card_eq q.prime_p q.exponent_pos hcard
  have hpl : 3 ≠ ringChar F := by
    rw [hring]
    exact fun h => h3 h.symm
  have h2 : (2 : F) ≠ 0 := by
    have : CharP F q.p := ringChar.of_eq hring
    intro h
    have : q.p ∣ 2 := (CharP.cast_eq_zero_iff F q.p 2).mp (by exact_mod_cast h)
    exact hq2 ((Nat.prime_dvd_prime_iff_eq q.prime_p Nat.prime_two).mp this)
  have hK4 : 4 ≤ Nat.card F := by
    rw [hcard]
    have h1 : q.p ≤ q.p ^ q.exponent := Nat.le_self_pow q.exponent_pos.ne' _
    have h5 := q.prime_p.two_le
    omega
  have hdich : 3 ∣ Nat.card F - 1 ∨ 3 ∣ Nat.card F + 1 := by
    rw [hcard, ← hqc]
    exact three_dvd_card_sub_or_add_one h3
  obtain ⟨hQ, hT⟩ := CFSG.ClassicalGroups.Orthogonal.regular_quadOdd (n := r) (K := F) h2 hr3
  let e₁ := Carrier.SpinB.typeBGroupEquivStatedProj_odd r q hv hq2 hr3
  obtain ⟨e₂⟩ := CFSG.RankThree.CentralLift.nonempty_statedProj_mulEquiv_projOrthDerived
    (coe_quadOdd r F)
  let e : Cat ⟨.B r q, hv⟩ ≃* ProjOrthDerived (quadOdd r F) := e₁.trans e₂
  have hdim : Module.finrank F (Fin r ⊕ Fin r ⊕ Unit → F) = 2 * r + 1 := by
    simp [Module.finrank_fintype_fun_eq_card]
    omega
  have hnat : ∀ α : MulAut (ProjOrthDerived (quadOdd r F)),
      KCOrthogonalAut.InducedBySemilinear (quadOdd r F) α := fun α =>
    KCOrthogonalAut.orthogonal_aut_semilinear_of_seven_le _ hQ (by omega)
      (fun h8 => by omega) α
  have hplanes : InnerPlanesBalanced 3 (ProjOrthDerived (quadOdd r F)) := by
    rcases hdich with h1 | h1
    · exact innerPlanesBalanced_projOrth3 hQ hT Nat.prime_three (by norm_num) hK4 hpl
        (fun A hA hAc g hg => orth3_split_derived_rigid hQ hT Nat.prime_three (by norm_num) h1
          A ⟨hA.1, hA.2⟩ hAc g hg)
    · exact innerPlanesBalanced_projOrth3 hQ hT Nat.prime_three (by norm_num) hK4 hpl
        (fun A hA hAc g hg => orth3_qplus_derived_rigid hQ hT Nat.prime_three (by norm_num) hK4
          hpl h1 hnat A ⟨hA.1, hA.2⟩ hAc g hg)
  exact InnerPlaneBalance.of_mulEquiv e hplanes

private theorem innerPlaneBalance_three_D_four (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.D 4 q).Valid) (h3 : q.p ≠ 3) (hq4 : 4 ≤ q.card) :
    InnerPlaneBalance 3 (Cat ⟨.D 4 q, hv⟩) := by
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  set F := ↥(TauCeti.ValidLieTypeIndex.fixedField ⟨.D 4 q, hv⟩) with hF
  have : Finite F := CFSG.QuasithinUnique.SQTK.finite_validIndex_fixedField _
  have hcard : Nat.card F = q.p ^ q.exponent :=
    card_fixedField_validIndex_orth ⟨.D 4 q, hv⟩ 4 q (Or.inr (Or.inl rfl))
  have hqc : q.card = q.p ^ q.exponent := TauCeti.PrimePower.card_def q
  have hring : ringChar F = q.p :=
    CFSG.ClassicalGroups.Orthogonal.ringChar_eq_of_card_eq q.prime_p q.exponent_pos hcard
  have hpl : 3 ≠ ringChar F := by
    rw [hring]
    exact fun h => h3 h.symm
  have hK4 : 4 ≤ Nat.card F := by
    rw [hcard, ← hqc]
    exact hq4
  have hdich : 3 ∣ Nat.card F - 1 ∨ 3 ∣ Nat.card F + 1 := by
    rw [hcard, ← hqc]
    exact three_dvd_card_sub_or_add_one h3
  let e₁ := Carrier.SpinD.typeDGroupEquivStatedProj_of_valid 4 q hv
  have hmodel : StatedClassicalModel (Cat ⟨.D 4 q, hv⟩) .POmegaPlus 4 q.p q.exponent :=
    statedClassicalModel_typeD 4 q hv (MulEquiv.refl _)
  obtain ⟨-, hnd, hT, -⟩ := coordinate_model_witness_plus hmodel F hcard e₁
  have hbal : InnerPlanesBalanced 3 (ProjOrthDerived (coordinateQuadPlus 4 F)) := by
    rcases hdich with h1 | h1
    · exact innerPlanesBalanced_projOrth3 hnd hT Nat.prime_three (by norm_num) hK4 hpl
        (fun A hA hAc g hg => orth3_split_derived_rigid hnd hT Nat.prime_three (by norm_num) h1
          A ⟨hA.1, hA.2⟩ hAc g hg)
    · exact innerPlanesBalanced_projOrth3 hnd hT Nat.prime_three (by norm_num) hK4 hpl
        (fun A hA hAc g hg => d4_qplus_derived_rigid (Cat ⟨.D 4 q, hv⟩) hmodel F hcard e₁
          Nat.prime_three (by norm_num) hK4 hpl h1 A ⟨hA.1, hA.2⟩ hAc g hg)
  have hd : 0 < 2 * 4 := by norm_num
  have hbal' : InnerPlanesBalanced 3 (matrixProjectiveDerived (coordinateQuadPlus 4 F)) :=
    InnerPlanesBalanced.of_mulEquiv (KCOrthogonalAut.coordBridge (coordinateQuadPlus 4 F) hd) hbal
  exact InnerPlaneBalance.of_mulEquiv (coordinatePlusWitnessEquiv F e₁) hbal'

private theorem innerPlaneBalance_three_D_ge_five (r : ℕ) (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.D r q).Valid) (hr5 : 5 ≤ r) (h3 : q.p ≠ 3) (hq4 : 4 ≤ q.card) :
    InnerPlaneBalance 3 (Cat ⟨.D r q, hv⟩) := by
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  set F := ↥(TauCeti.ValidLieTypeIndex.fixedField ⟨.D r q, hv⟩) with hF
  have : Finite F := CFSG.QuasithinUnique.SQTK.finite_validIndex_fixedField _
  have hcard : Nat.card F = q.p ^ q.exponent :=
    card_fixedField_validIndex_orth ⟨.D r q, hv⟩ r q (Or.inr (Or.inl rfl))
  have hqc : q.card = q.p ^ q.exponent := TauCeti.PrimePower.card_def q
  have hring : ringChar F = q.p :=
    CFSG.ClassicalGroups.Orthogonal.ringChar_eq_of_card_eq q.prime_p q.exponent_pos hcard
  have hpl : 3 ≠ ringChar F := by
    rw [hring]
    exact fun h => h3 h.symm
  have hK4 : 4 ≤ Nat.card F := by
    rw [hcard, ← hqc]
    exact hq4
  have hdich : 3 ∣ Nat.card F - 1 ∨ 3 ∣ Nat.card F + 1 := by
    rw [hcard, ← hqc]
    exact three_dvd_card_sub_or_add_one h3
  obtain ⟨hQ, hT⟩ := CFSG.ClassicalGroups.Orthogonal.regular_quadPlus (n := r) (K := F)
    (by omega)
  let e₁ := Carrier.SpinD.typeDGroupEquivStatedProj_of_valid r q hv
  obtain ⟨e₂⟩ := CFSG.RankThree.CentralLift.nonempty_statedProj_mulEquiv_projOrthDerived
    (coe_quadPlus r F)
  let e : Cat ⟨.D r q, hv⟩ ≃* ProjOrthDerived (quadPlus r F) := e₁.trans e₂
  have hdim : Module.finrank F (Fin r ⊕ Fin r → F) = 2 * r := by
    simp [Module.finrank_fintype_fun_eq_card]
    omega
  have hnat : ∀ α : MulAut (ProjOrthDerived (quadPlus r F)),
      KCOrthogonalAut.InducedBySemilinear (quadPlus r F) α := fun α =>
    KCOrthogonalAut.orthogonal_aut_semilinear_of_seven_le _ hQ (by omega)
      (fun h8 => by omega) α
  have hplanes : InnerPlanesBalanced 3 (ProjOrthDerived (quadPlus r F)) := by
    rcases hdich with h1 | h1
    · exact innerPlanesBalanced_projOrth3 hQ hT Nat.prime_three (by norm_num) hK4 hpl
        (fun A hA hAc g hg => orth3_split_derived_rigid hQ hT Nat.prime_three (by norm_num) h1
          A ⟨hA.1, hA.2⟩ hAc g hg)
    · exact innerPlanesBalanced_projOrth3 hQ hT Nat.prime_three (by norm_num) hK4 hpl
        (fun A hA hAc g hg => orth3_qplus_derived_rigid hQ hT Nat.prime_three (by norm_num) hK4
          hpl h1 hnat A ⟨hA.1, hA.2⟩ hAc g hg)
  exact InnerPlaneBalance.of_mulEquiv e hplanes

theorem innerPlaneBalance_three_D (r : ℕ) (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.D r q).Valid) (h3 : q.p ≠ 3) (hq4 : 4 ≤ q.card) :
    InnerPlaneBalance 3 (Cat ⟨.D r q, hv⟩) := by
  have hr4 : 4 ≤ r := (TauCeti.LieTypeIndex.inStandardRange_iff _).mp
    ((TauCeti.LieTypeIndex.valid_iff _).mp hv).1
  rcases (show r = 4 ∨ 5 ≤ r by omega) with h | hr5
  · subst h
    exact innerPlaneBalance_three_D_four q hv h3 hq4
  · exact innerPlaneBalance_three_D_ge_five r q hv hr5 h3 hq4

theorem innerPlaneBalance_three_twistedD (r : ℕ) (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.twistedD r q).Valid) (h3 : q.p ≠ 3) (hq4 : 4 ≤ q.card) :
    InnerPlaneBalance 3 (Cat ⟨.twistedD r q, hv⟩) := by
  have hr : 4 ≤ r := (TauCeti.LieTypeIndex.inStandardRange_iff _).mp
    ((TauCeti.LieTypeIndex.valid_iff _).mp hv).1
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  set F := ↥(TauCeti.ValidLieTypeIndex.fixedField ⟨.twistedD r q, hv⟩) with hF
  have : Finite F := CFSG.QuasithinUnique.SQTK.finite_validIndex_fixedField _
  have hcard : Nat.card F = q.p ^ q.exponent :=
    card_fixedField_validIndex_orth ⟨.twistedD r q, hv⟩ r q (Or.inr (Or.inr rfl))
  have hqc : q.card = q.p ^ q.exponent := TauCeti.PrimePower.card_def q
  have hring : ringChar F = q.p :=
    CFSG.ClassicalGroups.Orthogonal.ringChar_eq_of_card_eq q.prime_p q.exponent_pos hcard
  have hpl : 3 ≠ ringChar F := by
    rw [hring]
    exact fun h => h3 h.symm
  have hK4 : 4 ≤ Nat.card F := by
    rw [hcard, ← hqc]
    exact hq4
  have hdich : 3 ∣ Nat.card F - 1 ∨ 3 ∣ Nat.card F + 1 := by
    rw [hcard, ← hqc]
    exact three_dvd_card_sub_or_add_one h3
  obtain ⟨b, c, hirr, ⟨e₁⟩⟩ :=
    Carrier.SpinD.exists_typeTwistedDGroupEquivStatedProj_of_valid r q hv
  obtain ⟨hQ, hT⟩ := CFSG.ClassicalGroups.Orthogonal.regular_quadMinus (n := r) (K := F)
    (b := b) (c := c) hr hirr
  obtain ⟨e₂⟩ := CFSG.RankThree.CentralLift.nonempty_statedProj_mulEquiv_projOrthDerived
    (coe_quadMinus r F b c)
  let e : Cat ⟨.twistedD r q, hv⟩ ≃* ProjOrthDerived (quadMinus r F b c) := e₁.trans e₂
  have hplanes : InnerPlanesBalanced 3 (ProjOrthDerived (quadMinus r F b c)) := by
    rcases hdich with h1 | h1
    · exact innerPlanesBalanced_projOrth3 hQ hT Nat.prime_three (by norm_num) hK4 hpl
        (fun A hA hAc g hg => orth3_split_derived_rigid hQ hT Nat.prime_three (by norm_num) h1
          A ⟨hA.1, hA.2⟩ hAc g hg)
    · exact innerPlanesBalanced_projOrth3 hQ hT Nat.prime_three (by norm_num) hK4 hpl
        (fun A hA hAc g hg => orth3_qplus_derived_rigid hQ hT Nat.prime_three (by norm_num) hK4
          hpl h1 (orth3_aut_semilinear_quadMinus r hr b c hirr) A ⟨hA.1, hA.2⟩ hAc g hg)
  exact InnerPlaneBalance.of_mulEquiv e hplanes

end CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross
