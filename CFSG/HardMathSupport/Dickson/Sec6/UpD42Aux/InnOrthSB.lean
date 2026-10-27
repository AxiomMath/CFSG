module

public import CFSG.HardMathSupport.Dickson.Sec6.UpD42Aux.InnOrthType
public import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.InnUniBlock
public import CFSG.HardMathSupport.Solomon.LocalBalance.I1433.SympOrthOrthIdent
public import CFSG.RankThree.PartOne.KC.OrthogonalFactorization

public section

namespace CFSG.HardMathSupport.Dickson.Sec6

open Polynomial Module CFSG.Open CFSG.Blueprint CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.RankThree.PartOne.KCOrthogonal CFSG.RankThree.PartOne.KCPrimary
  CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2 CFSG.LocalAnalysis.ComponentInitial
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma27Ns.I1433

theorem card_centerQuotient_of_isD42 {F : Type} [Group F]
    (hD : IsCatalogLieIso (F ⧸ Subgroup.center F) IsD42Index) :
    Nat.card (F ⧸ Subgroup.center F) = 174182400 := by
  have hmodel := lieModel_of_isD42 hD
  rw [CFSG.SeitzReduction.OmegaPilot.card_of_lieModel_POmega_two (Or.inl rfl) hmodel]
  norm_num [CFSG.SeitzReduction.F4Pilot.evenLieOrder, CFSG.Open.ordD,
    Finset.prod_Icc_succ_top]

theorem false_of_centerQuotient_card_le {F : Type} [Group F] [Finite F]
    (hD : IsCatalogLieIso (F ⧸ Subgroup.center F) IsD42Index)
    {N : ℕ} (hN : N < 174182400)
    (hle : Nat.card (F ⧸ Subgroup.center F) ≤ N) : False := by
  have hcard := card_centerQuotient_of_isD42 hD
  omega

theorem false_of_specialBlock_isD42_paired
    {K : Type} [Field K] [Finite K] {V : Type} [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] {Q : QuadraticForm K V} {x : V ≃ₗ[K] V}
    {f₀ : ℕ} (hK : Nat.card K = 2 ^ f₀)
    (hx : OddOrderIsometry Q 3 x) {h : K[X]}
    (hh : h ∈ primaryFactors x.toLinearMap) (hne : h ≠ reciprocalPolynomial h)
    (hq : CFSG.IsQuasisimple ↥(specialBlock Q x h))
    (hD : IsCatalogLieIso
      (↥(specialBlock Q x h) ⧸ Subgroup.center ↥(specialBlock Q x h)) IsD42Index) :
    False := by
  classical
  have : Fact (Irreducible h) := ⟨irreducible_of_mem_primaryFactors hh⟩
  haveI : Finite ↥(specialBlock Q x h) := by
    have : Finite V := Module.finite_of_finite K
    have : Finite (V ≃ₗ[K] V) :=
      Finite.of_injective (fun e : V ≃ₗ[K] V => (e : V → V))
        fun e₁ e₂ h => LinearEquiv.ext (congrFun h)
    exact Finite.of_injective (fun g : ↥(specialBlock Q x h) => (g.1 : V ≃ₗ[K] V))
      Subtype.val_injective
  set m : ℕ := primaryMultiplicity x.toLinearMap h with hm
  let E := AdjoinRoot h
  let b : Module.Basis (Fin m) E (primaryComponent x.toLinearMap h) :=
    Module.finBasisOfFinrankEq _ _ rfl
  let eSL : ↥(specialBlock Q x h) ≃* Matrix.SpecialLinearGroup (Fin m) E :=
    (MulEquiv.ofBijective (specialToSL Q x h)
      ⟨hx.specialToSL_injective hh, hx.specialToSL_surjective_paired hh hne⟩).trans
      (Matrix.SpecialLinearGroup.toLin_equiv b).symm
  have hmpos : 1 ≤ m := hx.primaryMultiplicity_pos hh
  have hle : Nat.card (↥(specialBlock Q x h) ⧸
      Subgroup.center ↥(specialBlock Q x h)) ≤ Nat.card ↥(specialBlock Q x h) :=
    Nat.card_le_card_of_surjective _ (QuotientGroup.mk'_surjective _)
  by_cases hm1 : m = 1
  · have hbot : specialBlock Q x h = ⊥ := hx.specialBlock_eq_bot_of_finrank_eq_one hh hm1
    haveI : Subsingleton ↥(specialBlock Q x h) := by rw [hbot]; infer_instance
    haveI : Subsingleton (↥(specialBlock Q x h) ⧸ Subgroup.center ↥(specialBlock Q x h)) :=
      by infer_instance
    obtain ⟨a, b, hab⟩ := hq.2.2
    exact hab (Subsingleton.elim (a * b) (b * a))
  · have hm2 : 2 ≤ m := by omega
    obtain ⟨e', he'pos, hEcard⟩ :=
      exists_card_adjoinRoot_eq_pow_c2 (k := K) (p := 2) (f := f₀) (h := h)
        Nat.prime_two hK
    have hEcard' : Nat.card E = 2 ^ e' := by simpa [E] using hEcard
    by_cases hsmall : m = 2 ∧ e' = 1
    · have hm2' : m = 2 := hsmall.1
      have he'1 : e' = 1 := hsmall.2
      rw [hm2'] at eSL
      rw [he'1] at hEcard'
      have hE2 : Nat.card E = 2 := by simpa using hEcard'
      have eSt : ↥(specialBlock Q x h) ≃* ↥(StatedSL 2 E) :=
        eSL.trans (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 E)
      have hcardF : Nat.card ↥(specialBlock Q x h) = 6 := by
        rw [Nat.card_congr eSt.toEquiv, CFSG.Open.StatedAPI.card_statedSL_two, hE2]
        norm_num
      exact false_of_centerQuotient_card_le hD (by norm_num) (hle.trans (le_of_eq hcardF))
    · have hadm : StatedLieAdmissible .PSL m 2 e' := by
        refine ⟨Nat.prime_two, he'pos, hm2, ?_, ?_⟩
        · intro h
          have hm2' : m = 2 := (Prod.mk.inj h).1
          have h2e : 2 ^ e' = 2 := (Prod.mk.inj h).2
          have he'1 : e' = 1 := by
            have hle1 : e' ≤ 1 := by
              by_contra hgt
              have h2 : 2 ≤ e' := by omega
              have : 4 ≤ 2 ^ e' := by
                calc 4 = 2 ^ 2 := by norm_num
                  _ ≤ 2 ^ e' := Nat.pow_le_pow_right (by norm_num) h2
              omega
            omega
          exact hsmall ⟨hm2', he'1⟩
        · intro h
          have h3 : 2 ^ e' = 3 := (Prod.mk.inj h).2
          have h2dvd : 2 ∣ 2 ^ e' := dvd_pow_self 2 (by omega)
          rw [h3] at h2dvd
          norm_num at h2dvd
      have hmodel := lieModel_centerQuotient_of_equiv_SL_c2 hadm hEcard' eSL
      exact absurd (classical_type_of_isD42 (t := .PSL) (n := m) (f := e')
        (by decide) hmodel hD).1 (by decide)

theorem false_of_specialBlock_isD42_selfDual
    {K : Type} [Field K] [Finite K] {V : Type} [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] {Q : QuadraticForm K V} {x : V ≃ₗ[K] V}
    {f₀ : ℕ} (hf₀ : 1 ≤ f₀) (hK : Nat.card K = 2 ^ f₀)
    (hx : OddOrderIsometry Q 3 x) {h : K[X]}
    (hh : h ∈ primaryFactors x.toLinearMap) (hne1 : h ≠ X - 1)
    (hself : h = reciprocalPolynomial h)
    (hq : CFSG.IsQuasisimple ↥(specialBlock Q x h))
    (hD : IsCatalogLieIso
      (↥(specialBlock Q x h) ⧸ Subgroup.center ↥(specialBlock Q x h)) IsD42Index) :
    False := by
  classical
  have : Fact (Irreducible h) := ⟨irreducible_of_mem_primaryFactors hh⟩
  have hirr := irreducible_of_mem_primaryFactors hh
  have hp2' : Odd 3 := by decide
  obtain ⟨d, H, hdeg, hroot, hH, hadd1, hadd2, hleft, hright, hsymm⟩ :=
    hx.exists_selfDual_hermitian hp2' hh hne1 hself
  have hpos : 0 < h.natDegree := hirr.natDegree_pos
  have hle2 : h.natDegree ≤ 2 := natDegree_le_two_of_order_three hx hh hne1
  have hdpos : 0 < d := by
    rcases Nat.eq_zero_or_pos d with rfl | hd
    · simp at hdeg; omega
    · exact hd
  have hd1 : d = 1 := by omega
  have hdeg2 : h.natDegree = 2 := by omega
  subst d
  have hd2 : Module.finrank K (AdjoinRoot h) = 2 := by
    rw [(AdjoinRoot.powerBasis hirr.ne_zero).finrank, AdjoinRoot.powerBasis_dim, hdeg2]
  obtain ⟨ℓ, f, hU₀, hqcard, hbar₀⟩ :=
    exists_unitaryFieldData (K := K) (E := AdjoinRoot h) (d := 1) (by simpa using hd2)
  have hU : UnitaryFieldData ℓ f (AdjoinRoot h) := by simpa using hU₀
  have hfpos : 1 ≤ f := hU.one_le
  have hbar : ∀ z, hU.bar z = z ^ Nat.card K := by
    intro z
    simpa using hbar₀ z
  have hℓ2 : ℓ = 2 := by
    have hdvd : ℓ ∣ 2 ^ f₀ := by
      rw [← hK, hqcard]
      exact dvd_pow_self ℓ (by omega : f ≠ 0)
    exact (Nat.prime_dvd_prime_iff_eq hU.prime Nat.prime_two).1
      (hU.prime.dvd_of_dvd_pow hdvd)
  subst hℓ2
  have hbar' : ∀ z, frobPow K (AdjoinRoot h) 1 z = hU.bar z := by
    intro z
    rw [hbar, frobPow_apply, Nat.pow_one]
  let B : primaryComponent x.toLinearMap h →ₛₗ[hU.bar]
      primaryComponent x.toLinearMap h →ₗ[AdjoinRoot h] AdjoinRoot h :=
    LinearMap.mk₂'ₛₗ hU.bar (RingHom.id _) H hadd1
      (fun c u w => by rw [hleft, smul_eq_mul, hbar']) hadd2
      (fun c u w => by rw [hright, smul_eq_mul, RingHom.id_apply])
  have hBH : ∀ u w, B u w = H u w := fun u w => rfl
  have hBsymm : B.IsSymm := ⟨fun u w => by rw [hBH, hBH, hsymm u w, hbar']⟩
  have hBl : B.SeparatingLeft := by
    intro u hu
    refine Subtype.ext (hx.eq_zero_of_polar_selfdual hh hself u.2 fun w hw => ?_)
    have h1 := hH u ⟨w, hw⟩ 1
    rw [mul_one, one_smul] at h1
    have h2 : H u ⟨w, hw⟩ = 0 := by rw [← hBH]; exact hu _
    rw [h2, map_zero] at h1
    exact h1.symm
  have hrange : (specialBlockGL Q x h).range = sesqSpecialUnitaryGroup B := by
    rw [range_specialBlockGL, sesqSpecialUnitaryGroup]
    congr 1
    ext γ
    rw [hx.mem_range_blockGL_selfDual_iff hh hne1 hself H hH, mem_sesqUnitaryGroup]
    exact Iff.rfl
  let e₁ : ↥(specialBlock Q x h) ≃* ↥(sesqSpecialUnitaryGroup B) :=
    (MonoidHom.ofInjective (hx.specialBlockGL_injective hh)).trans
      (MulEquiv.subgroupCongr hrange)
  haveI : Finite ↥(specialBlock Q x h) := by
    have : Finite V := Module.finite_of_finite K
    have : Finite (V ≃ₗ[K] V) :=
      Finite.of_injective (fun e : V ≃ₗ[K] V => (e : V → V))
        fun e₁ e₂ h => LinearEquiv.ext (congrFun h)
    exact Finite.of_injective (fun g : ↥(specialBlock Q x h) => (g.1 : V ≃ₗ[K] V))
      Subtype.val_injective
  have hle : Nat.card (↥(specialBlock Q x h) ⧸
      Subgroup.center ↥(specialBlock Q x h)) ≤ Nat.card ↥(specialBlock Q x h) :=
    Nat.card_le_card_of_surjective _ (QuotientGroup.mk'_surjective _)
  set m : ℕ := primaryMultiplicity x.toLinearMap h with hm
  have hmpos : 1 ≤ m := hx.primaryMultiplicity_pos hh
  by_cases hm1 : m = 1
  · have hbot : specialBlock Q x h = ⊥ :=
      hx.specialBlock_eq_bot_of_finrank_eq_one hh (by rw [← hm]; exact hm1)
    haveI : Subsingleton ↥(specialBlock Q x h) := by rw [hbot]; infer_instance
    haveI : Subsingleton (↥(specialBlock Q x h) ⧸ Subgroup.center ↥(specialBlock Q x h)) :=
      by infer_instance
    obtain ⟨a, b, hab⟩ := hq.2.2
    exact hab (Subsingleton.elim (a * b) (b * a))
  · have hm2 : 2 ≤ m := by omega
    by_cases hm2eq : m = 2
    · have hV : Module.finrank (AdjoinRoot h)
          (primaryComponent x.toLinearMap h) = 2 := by
        rw [show Module.finrank (AdjoinRoot h) (primaryComponent x.toLinearMap h) = m by rw [hm]]
        exact hm2eq
      obtain ⟨e2⟩ :=
        CFSG.RankThree.Classical.nonempty_sesqSpecialUnitaryGroup_mulEquiv_SL2 hU hBsymm hBl hV
      let eSL : ↥(specialBlock Q x h) ≃* Matrix.SpecialLinearGroup (Fin 2) hU.fixedField :=
        e₁.trans e2
      by_cases hfix2 : Nat.card hU.fixedField = 2
      · have eSt : ↥(specialBlock Q x h) ≃* ↥(StatedSL 2 hU.fixedField) :=
          eSL.trans (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 hU.fixedField)
        have hcardF : Nat.card ↥(specialBlock Q x h) = 6 := by
          rw [Nat.card_congr eSt.toEquiv, CFSG.Open.StatedAPI.card_statedSL_two, hfix2]
          norm_num
        exact false_of_centerQuotient_card_le hD (by norm_num) (hle.trans (le_of_eq hcardF))
      · have hfixpow : Nat.card hU.fixedField = 2 ^ f := hU.card_fixedField
        have hf2 : 2 ≤ f := by
          by_contra hlt
          have hf1 : f = 1 := by omega
          exact hfix2 (by rw [hfixpow, hf1, pow_one])
        have hadm : StatedLieAdmissible .PSL 2 2 f := by
          refine ⟨Nat.prime_two, hU.one_le, le_rfl, ?_, ?_⟩
          · intro h
            have : 2 ^ f = 2 := (Prod.mk.inj h).2
            have hf1 : f = 1 := by
              have hle1 : f ≤ 1 := by
                by_contra hgt
                have h2 : 2 ≤ f := by omega
                have : 4 ≤ 2 ^ f := by
                  calc 4 = 2 ^ 2 := by norm_num
                    _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) h2
                omega
              omega
            omega
          · intro h
            have h3 : 2 ^ f = 3 := (Prod.mk.inj h).2
            have h2dvd : 2 ∣ 2 ^ f := dvd_pow_self 2 (by omega : f ≠ 0)
            rw [h3] at h2dvd
            norm_num at h2dvd
        have hmodel := lieModel_centerQuotient_of_equiv_SL_c2 hadm hU.card_fixedField eSL
        exact absurd (classical_type_of_isD42 (t := .PSL) (n := 2) (f := f)
          (by decide) hmodel hD).1 (by decide)
    · have hm3 : 3 ≤ m := by omega
      by_cases h32 : m = 3 ∧ f = 1
      · have hV : Module.finrank (AdjoinRoot h)
            (primaryComponent x.toLinearMap h) = 3 := by
          rw [show Module.finrank (AdjoinRoot h) (primaryComponent x.toLinearMap h) = m by rw [hm]]
          exact h32.1
        have hf1 : f = 1 := h32.2
        subst f
        have hcardSU : Nat.card ↥(sesqSpecialUnitaryGroup B) = 216 := by
          have h := (CFSG.LinearGroups.unitary_full_group_order hU hBsymm hBl
            (n := 3) hV (by omega)).2.1
          norm_num [Finset.prod_Icc_succ_top] at h
          exact_mod_cast h
        have hcardF : Nat.card ↥(specialBlock Q x h) = 216 := by
          rw [Nat.card_congr e₁.toEquiv, hcardSU]
        exact false_of_centerQuotient_card_le hD (by norm_num) (hle.trans (le_of_eq hcardF))
      · have hq' : ¬(m = 3 ∧ 2 ^ f = 2) := by
          rintro ⟨hm3', h2f⟩
          have hf1 : f = 1 := by
            have hle1 : f ≤ 1 := by
              by_contra hgt
              have h2 : 2 ≤ f := by omega
              have : 4 ≤ 2 ^ f := by
                calc 4 = 2 ^ 2 := by norm_num
                  _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) h2
              omega
            omega
          exact h32 ⟨hm3', hf1⟩
        obtain ⟨b, hb⟩ := hU.exists_orthonormal_basis hBsymm hBl
        obtain ⟨e2⟩ :=
          CFSG.RankThree.CentralLift.nonempty_sesqSpecialUnitaryGroup_mulEquiv_gramSU hU b
            (G := (1 : Matrix (Fin (Module.finrank (AdjoinRoot h)
              (primaryComponent x.toLinearMap h)))
              (Fin (Module.finrank (AdjoinRoot h)
              (primaryComponent x.toLinearMap h))) (AdjoinRoot h)))
            (fun i j => by rw [hb i j, Matrix.one_apply])
        have hmodel := lieModel_centerQuotient_of_equiv_gramSU hU hm3 hq' (e₁.trans e2)
        exact absurd (classical_type_of_isD42 (t := .PSU) (n := m) (f := f)
          (by decide) hmodel hD).1 (by decide)

theorem false_of_specialBlock_isD42
    {K : Type} [Field K] [Finite K] {V : Type} [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] {Q : QuadraticForm K V} {x : V ≃ₗ[K] V}
    {f₀ : ℕ} (hf₀ : 1 ≤ f₀) (hK : Nat.card K = 2 ^ f₀)
    (hx : OddOrderIsometry Q 3 x) {h : K[X]}
    (hh : h ∈ primaryFactors x.toLinearMap) (hne1 : h ≠ X - 1)
    (hq : CFSG.IsQuasisimple ↥(specialBlock Q x h))
    (hD : IsCatalogLieIso
      (↥(specialBlock Q x h) ⧸ Subgroup.center ↥(specialBlock Q x h)) IsD42Index) :
    False := by
  by_cases hself : h = reciprocalPolynomial h
  · exact false_of_specialBlock_isD42_selfDual hf₀ hK hx hh hne1 hself hq hD
  · exact false_of_specialBlock_isD42_paired hK hx hh hself hq hD

end CFSG.HardMathSupport.Dickson.Sec6

end
