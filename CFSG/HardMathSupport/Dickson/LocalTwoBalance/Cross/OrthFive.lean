module

public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.Split
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.CrossOrthFamilies

public section

namespace CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance Module
  CFSG.HardMathSupport.Timmesfeld.Coordinator CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.RankThree.PartOne CFSG.RankThree.Classical2 CFSG.Assembly.LowTwoRank
  CFSG.HardMathSupport.Timmesfeld.DefChar CFSG.HardMathSupport.Timmesfeld.LocalTwo
  CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.RankThree.PartTwo.Census CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  CFSG.LieType.Universal.Spin

private theorem isLocallyBalancedAbs_two_projOrth_of_three_lt
    {K : Type} [Field K] [Finite K] {V : Type} [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] {Q : QuadraticForm K V}
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hT : ∃ U : Submodule K V, finrank K U = 3 ∧ ∀ u ∈ U, Q u = 0)
    {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) (hpl : p ≠ ringChar K)
    (hCL : CommonLayerCentralizerTrivial (ProjOrthDerived Q) p)
    {P : Type*} [Group P] (Ψ : ProjOrthDerived Q ≃* P)
    (hP : ∀ [Finite P], Function.Injective (MulAut.conj : P →* MulAut P) → OuterFields p P) :
    IsLocallyBalancedAbs p 2 (ProjOrthDerived Q) := by
  have : Finite V := Module.finite_of_finite K
  have : Finite (V ≃ₗ[K] V) := Finite.of_injective (fun e : V ≃ₗ[K] V => (e : V → V))
    fun e₁ e₂ h => LinearEquiv.ext (congrFun h)
  obtain ⟨-, -, -, hsimple, hnonab, -⟩ :=
    CFSG.RankThree.Classical.orthogonal_high_Witt_derived_quotient_and_odd_lifts hQ hT
  have hcenter : Subgroup.center (ProjOrthDerived Q) = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center (ProjOrthDerived Q)) with
      h | h
    · exact h
    · exfalso
      obtain ⟨c, d, hcd⟩ := hnonab
      exact hcd (Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top d) c)
  have hinj := conj_injective_of_center_eq_bot_orth hcenter
  have : Finite P := Finite.of_equiv _ Ψ.toEquiv
  refine isLocallyBalancedAbs_two_of_planes_and_fields hp hinj ?_
    ((hP (conj_injective_of_mulEquiv Ψ hinj)).of_mulEquiv Ψ)
  intro E hEin hE hEc H hH
  set E₁ : Subgroup (ProjOrthDerived Q) :=
    E.comap (MulAut.conj : ProjOrthDerived Q →* MulAut (ProjOrthDerived Q)) with hE₁
  have hmap : E₁.map (MulAut.conj : ProjOrthDerived Q →* MulAut (ProjOrthDerived Q)) = E :=
    Subgroup.map_comap_eq_self hEin
  have hE₁el : IsElemAbelian p E₁ := by
    refine ⟨⟨⟨fun a b => Subtype.ext (hinj ?_)⟩⟩, fun x hx => hinj ?_⟩
    · have h2 : MulAut.conj (a : ProjOrthDerived Q) * MulAut.conj (b : ProjOrthDerived Q) =
          MulAut.conj (b : ProjOrthDerived Q) * MulAut.conj (a : ProjOrthDerived Q) :=
        congrArg Subtype.val (hE.1.is_comm.comm ⟨_, a.2⟩ ⟨_, b.2⟩)
      rw [Subgroup.coe_mul, Subgroup.coe_mul, map_mul, map_mul]
      exact h2
    · rw [map_pow, map_one]
      exact hE.2 _ hx
  have hE₁c : Nat.card E₁ = p ^ 2 := by
    rw [← Subgroup.card_map_of_injective hinj, hmap, hEc]
  have hbot := localDeltaIn_eq_bot_projOrth hQ hT hp hp3 hpl hCL E₁ hE₁el hE₁c hH
  rwa [hmap] at hbot

open CFSG.RankThree.PartTwo.Census CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  CFSG.LieType.Universal.Spin CFSG.RankThree.PartOne.KCOrthogonal in
private theorem localTwoCrossFamAt_B_orth_of_three_lt {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) :
    ∀ idx : TauCeti.ValidLieTypeIndex, regimeBOrthTwo idx p → idx.1.characteristic ≠ p →
      IsLocallyBalancedAbs p 2 (Cat idx) := by
  rintro ⟨d, hv⟩ ⟨r, q, hd, hq2, hr⟩ hc
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
      .POmegaOdd (Or.inl rfl) r q.p q.exponent p hmodel hp hp3 hpq F hcard e₁
  let eP := (KCOrthogonalD4.bridgeEquiv (coordinateQuadOdd r F) (by omega)).trans
        (KCOrthogonalDescent.projOrthDerivedEquiv (coordinateOddIsometry r F).symm.toLinearEquiv 1
          fun v => by
            rw [Units.val_one, one_mul]
            exact (coordinateOddIsometry r F).symm.map_app v)
  have hCL : CommonLayerCentralizerTrivial (ProjOrthDerived (quadOdd r F)) p :=
    CommonLayerCentralizerTrivial.of_mulEquiv eP hCLm
  exact IsLocallyBalancedAbs.of_mulEquiv e
    (isLocallyBalancedAbs_two_projOrth_of_three_lt hQ hT hp hp3 hpl hCL eP.symm
      fun [Finite _] hinj => outerFields_matrix_odd hmodel hp hp3 hpq F hcard e₁ hinj)

private theorem localTwoCrossFamCat_D_of_three_lt {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) :
    ∀ idx : TauCeti.ValidLieTypeIndex, LieFamily.Matches .D idx.1 →
      idx.1.characteristic ≠ p → IsLocallyBalancedAbs p 2 (Cat idx) := by
  rintro ⟨d, hv⟩ ⟨r, q, hd⟩ hc
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
  let eP := (KCOrthogonalD4.bridgeEquiv (coordinateQuadPlus r F) (by omega)).trans
        (KCOrthogonalDescent.projOrthDerivedEquiv (coordinatePlusIsometry r F).symm.toLinearEquiv 1
          fun v => by
            rw [Units.val_one, one_mul]
            exact (coordinatePlusIsometry r F).symm.map_app v)
  have hCL : CommonLayerCentralizerTrivial (ProjOrthDerived (quadPlus r F)) p :=
    CommonLayerCentralizerTrivial.of_mulEquiv eP hCLm
  exact IsLocallyBalancedAbs.of_mulEquiv e
    (isLocallyBalancedAbs_two_projOrth_of_three_lt hQ hT hp hp3 hpl hCL eP.symm
      fun [Finite _] hinj => outerFields_matrix_plus hmodel hp hp3 hpq F hcard e₁ hinj)

private theorem localTwoCrossFamCat_twistedD_of_three_lt {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) :
    ∀ idx : TauCeti.ValidLieTypeIndex, LieFamily.Matches .twistedD idx.1 →
      idx.1.characteristic ≠ p → IsLocallyBalancedAbs p 2 (Cat idx) := by
  rintro ⟨d, hv⟩ ⟨r, q, hd⟩ hc
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
  let eP := (KCOrthogonalD4.bridgeEquiv (coordinateQuadMinus r F hn b c) (by omega)).trans
        (KCOrthogonalDescent.projOrthDerivedEquiv
          (coordinateMinusIsometry r F hn b c).symm.toLinearEquiv 1 fun v => by
            rw [Units.val_one, one_mul]
            exact (coordinateMinusIsometry r F hn b c).symm.map_app v)
  have hCL : CommonLayerCentralizerTrivial (ProjOrthDerived (quadMinus r F b c)) p :=
    CommonLayerCentralizerTrivial.of_mulEquiv eP hCLm
  exact IsLocallyBalancedAbs.of_mulEquiv e
    (isLocallyBalancedAbs_two_projOrth_of_three_lt hQ hT hp hp3 hpl hCL eP.symm
      fun [Finite _] hinj => outerFields_matrix_minus hmodel hn hp hp3 hpq F hcard b c hirr
        e₁ hinj)

theorem localTwoCrossFamAt_five_B_orth : LocalTwoCrossFamAt 5 .B fun idx => regimeBOrthTwo idx 5 := by
  intro idx _ hR hc _
  exact localTwoCrossFamAt_B_orth_of_three_lt (p := 5) (by norm_num) (by norm_num) idx hR hc

theorem localTwoCrossFamCat_five_D : LocalTwoCrossFamCat 5 .D := by
  intro idx hk hc _
  exact localTwoCrossFamCat_D_of_three_lt (p := 5) (by norm_num) (by norm_num) idx hk hc

theorem localTwoCrossFamCat_five_twistedD : LocalTwoCrossFamCat 5 .twistedD := by
  intro idx hk hc _
  exact localTwoCrossFamCat_twistedD_of_three_lt (p := 5) (by norm_num) (by norm_num) idx hk hc

end CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross
