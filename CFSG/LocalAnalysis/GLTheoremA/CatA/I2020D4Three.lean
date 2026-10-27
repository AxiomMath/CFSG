module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I2020D4Defs
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I2020OrthOuter
public import CFSG.LocalAnalysis.GLTheoremA.CatA.D4ThreeOuterNormalForm
public import CFSG.LocalAnalysis.GLTheoremA.CatA.FRCore
public import CFSG.HardMathSupport.Lang.E6Descent.OuterFixed27D4AmbientGraphField
public import CFSG.LocalAnalysis.GLTheoremA.CatA.FQ
public import CFSG.LocalAnalysis.GLTheoremA.CatA.FRLift

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I2020

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.HardMathSupport.Lang.D4Three CFSG.HardMathSupport.Lang.E6Descent
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.CatLeaf
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open CFSG.HardMathSupport.Dickson.Bal207.D4Graph


private theorem fixedSubgroup_twistedEntrywiseAut_D4_one_simple {K : Type} [Field K] [Finite K]
    {q e : ℕ} [Fact q.Prime] [CharP K q] (he : 1 ≤ e) (hK : Nat.card K = (q ^ e) ^ 3)
    (σ : K ≃+* K) (r : ℕ) (hr : r = 1 ∨ r = 2)
    (hσ : ∀ c, σ c = c ^ ((q ^ e) ^ r)) :
    IsSimpleGroup ↥(fixedSubgroup (twistedEntrywiseAut TwistTag.D4 1 σ)) ∧
      ∃ a b : ↥(fixedSubgroup (twistedEntrywiseAut TwistTag.D4 1 σ)), a * b ≠ b * a := by
  classical
  haveI : CharP (AlgebraicClosure K) q :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective q
  obtain ⟨-, -, hfixeq, hsimple, hnc⟩ :=
    triality_both_field_orientations_simple_full_ambient_fixed_group q e (Fact.out : q.Prime) he K
      hK (AlgebraicClosure K) r hr σ.toRingHom (fun c => hσ c)
      (iterateFrobenius (AlgebraicClosure K) q e) (fun c => by simp [iterateFrobenius_def])
  let eΓ : ↥(fixedSubgroup (twistedEntrywiseAut TwistTag.D4 1 σ)) ≃*
      graphFixedRootGroup TwistTag.D4 K σ.toRingHom :=
    (fixedSubgroupTwistedEntrywiseAutOneEquiv TwistTag.D4 σ).trans
      (MulEquiv.subgroupCongr hfixeq)
  haveI := hsimple
  refine ⟨eΓ.isSimpleGroup, ?_⟩
  obtain ⟨x, y, hxy⟩ := hnc
  refine ⟨eΓ.symm x, eΓ.symm y, fun h => hxy ?_⟩
  calc x * y = eΓ (eΓ.symm x) * eΓ (eΓ.symm y) := by
        rw [eΓ.apply_symm_apply, eΓ.apply_symm_apply]
    _ = eΓ (eΓ.symm x * eΓ.symm y) := (map_mul eΓ _ _).symm
    _ = eΓ (eΓ.symm y * eΓ.symm x) := congrArg eΓ h
    _ = eΓ (eΓ.symm y) * eΓ (eΓ.symm x) := map_mul eΓ _ _
    _ = y * x := by rw [eΓ.apply_symm_apply, eΓ.apply_symm_apply]

private theorem card_fixedSubgroup_twistedEntrywiseAut_D4_one {K : Type} [Field K] [Finite K]
    {q e : ℕ} [Fact q.Prime] [CharP K q] (he : 1 ≤ e) (hK : Nat.card K = (q ^ e) ^ 3)
    (σ : K ≃+* K) (r : ℕ) (hr : r = 1 ∨ r = 2)
    (hσ : ∀ c, σ c = c ^ ((q ^ e) ^ r)) :
    Nat.card ↥(fixedSubgroup (twistedEntrywiseAut TwistTag.D4 1 σ)) =
      (q ^ e) ^ 12 * ((q ^ e) ^ 8 + (q ^ e) ^ 4 + 1) * ((q ^ e) ^ 6 - 1) *
        ((q ^ e) ^ 2 - 1) := by
  classical
  haveI : CharP (AlgebraicClosure K) q :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective q
  obtain ⟨-, -, hfixeq, -⟩ :=
    triality_both_field_orientations_simple_full_ambient_fixed_group q e (Fact.out : q.Prime) he K
      hK (AlgebraicClosure K) r hr σ.toRingHom (fun c => hσ c)
      (iterateFrobenius (AlgebraicClosure K) q e) (fun c => by simp [iterateFrobenius_def])
  rw [card_fixedSubgroup_twistedEntrywiseAut_one, hfixeq]
  rw [(triality_both_orientations_exact_finite_order q e (Fact.out : q.Prime) he K hK r hr
    σ.toRingHom (fun c => hσ c)).1]
  ring

theorem exists_orientation_twistedEntrywiseAut_D4 {K : Type} [Field K] [Finite K]
    {q e : ℕ} [Fact q.Prime] [CharP K q] (hK : Nat.card K = (q ^ e) ^ 3)
    (T : K ≃+* K) (hT : ∀ c, T c = c ^ (q ^ e)) (j : ℤ) (hj : j = 1 ∨ j = 2) :
    ∃ (σ : K ≃+* K) (r : ℕ), (r = 1 ∨ r = 2) ∧
      (∀ c, σ c = c ^ ((q ^ e) ^ r)) ∧
        fixedSubgroup (twistedEntrywiseAut TwistTag.D4 j T) =
          fixedSubgroup (twistedEntrywiseAut TwistTag.D4 1 σ) := by
  rcases hj with rfl | rfl
  · exact ⟨T, 1, Or.inl rfl, fun c => by rw [hT, pow_one], rfl⟩
  · have hT3 : T ^ 3 = 1 := by
      refine RingEquiv.ext fun c => ?_
      exact CFSG.LieType.Chevalley.ringEquiv_cube_apply_eq hK hT c
    have hTinv : T⁻¹ = T ^ 2 := CFSG.RankThree.Chevalley.symm_eq_sq_of_pow_three T hT3
    have hinv : ∀ c, T⁻¹ c = c ^ ((q ^ e) ^ 2) := by
      intro c
      rw [hTinv, pow_two]
      change T (T c) = _
      rw [hT, hT, ← pow_mul, sq]
    exact ⟨T⁻¹, 2, Or.inr rfl, hinv, fixedSubgroup_twistedEntrywiseAut_D4_two T⟩

private theorem fixedSubgroup_twistedEntrywiseAut_D4_simple {K : Type} [Field K] [Finite K]
    {q e : ℕ} [Fact q.Prime] [CharP K q] (he : 1 ≤ e) (hK : Nat.card K = (q ^ e) ^ 3)
    (T : K ≃+* K) (hT : ∀ c, T c = c ^ (q ^ e)) (j : ℤ) (hj : j = 1 ∨ j = 2) :
    IsSimpleGroup ↥(fixedSubgroup (twistedEntrywiseAut TwistTag.D4 j T)) ∧
      ∃ a b : ↥(fixedSubgroup (twistedEntrywiseAut TwistTag.D4 j T)), a * b ≠ b * a := by
  obtain ⟨σ, r, hr, hσ, hfix⟩ :=
    exists_orientation_twistedEntrywiseAut_D4 hK T hT j hj
  rw [hfix]
  exact fixedSubgroup_twistedEntrywiseAut_D4_one_simple he hK σ r hr hσ

private theorem card_fixedSubgroup_twistedEntrywiseAut_D4 {K : Type} [Field K] [Finite K]
    {q e : ℕ} [Fact q.Prime] [CharP K q] (he : 1 ≤ e) (hK : Nat.card K = (q ^ e) ^ 3)
    (T : K ≃+* K) (hT : ∀ c, T c = c ^ (q ^ e)) (j : ℤ) (hj : j = 1 ∨ j = 2) :
    Nat.card ↥(fixedSubgroup (twistedEntrywiseAut TwistTag.D4 j T)) =
      (q ^ e) ^ 12 * ((q ^ e) ^ 8 + (q ^ e) ^ 4 + 1) * ((q ^ e) ^ 6 - 1) *
        ((q ^ e) ^ 2 - 1) := by
  obtain ⟨σ, r, hr, hσ, hfix⟩ :=
    exists_orientation_twistedEntrywiseAut_D4 hK T hT j hj
  rw [hfix]
  exact card_fixedSubgroup_twistedEntrywiseAut_D4_one he hK σ r hr hσ

private theorem noJTypeComponent_twistedEntrywiseAut_D4 {K : Type} [Field K] [Finite K]
    {q e : ℕ} [Fact q.Prime] [CharP K q] (hq2 : q ≠ 2) (hq3 : q ≠ 3) (he : 1 ≤ e)
    (hK : Nat.card K = (q ^ e) ^ 3) (T : K ≃+* K) (hT : ∀ c, T c = c ^ (q ^ e))
    (j : ℤ) (hj : j = 1 ∨ j = 2) :
    NoJTypeComponent 3 q (twistedEntrywiseAut TwistTag.D4 j T) := by
  have h3q : ¬ 3 ∣ q ^ e := by
    intro h
    exact hq3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three (Fact.out : q.Prime)).1
      (Nat.prime_three.dvd_of_dvd_pow h)).symm
  obtain ⟨hsimple, hnc⟩ := fixedSubgroup_twistedEntrywiseAut_D4_simple he hK T hT j hj
  have hcard := card_fixedSubgroup_twistedEntrywiseAut_D4 he hK T hT j hj
  have h27 := twentySeven_dvd_card_fixedSubgroup_twistedEntrywiseAut_D4
    (Fact.out : q.Prime) he h3q K hK T hT j hj
  have h3dvd : 3 ∣ Nat.card ↥(fixedSubgroup (twistedEntrywiseAut TwistTag.D4 j T)) :=
    (by norm_num : (3 : ℕ) ∣ 27).trans h27
  have hcore := CFSG.HardMathSupport.Dickson.I271.glaPPrimeCore_eq_bot_of_simple
    Nat.prime_three h3dvd
  have hZ := CFSG.HardMathSupport.Dickson.I271.center_eq_bot_of_simple_nonab hnc
  have hcardPS : Nat.card (PSimple 3 (fixedSubgroup
      (twistedEntrywiseAut TwistTag.D4 j T))) =
      Nat.card ↥(fixedSubgroup (twistedEntrywiseAut TwistTag.D4 j T)) :=
    Nat.card_congr (CFSG.HardMathSupport.Dickson.I271.pSimpleEquivSelf
      (fixedSubgroup (twistedEntrywiseAut TwistTag.D4 j T)) hcore hZ).toEquiv
  intro J hJ hJT
  have hJeq : J = fixedSubgroup (twistedEntrywiseAut TwistTag.D4 j T) :=
    CFSG.LocalAnalysis.GLTheoremA.FR.eq_core_of_glaPComponent
      (C := fixSubgroup (twistedEntrywiseAut TwistTag.D4 j T))
      (E := fixedSubgroup (twistedEntrywiseAut TwistTag.D4 j T))
      hsimple (fun x hx => hx) (fun _ hT _ => hT) hJ
  rw [hJeq] at hJT
  have htn : NotJTypeTag .trialityD4 0 := by simp [NotJTypeTag]
  have hcard' : Nat.card (PSimple 3 (fixedSubgroup
      (twistedEntrywiseAut TwistTag.D4 j T))) * lieOrderDivisor .trialityD4 0 (q ^ e) =
      lieOrderNumerator .trialityD4 0 (q ^ e) := by
    rw [hcardPS, hcard, show lieOrderDivisor .trialityD4 0 (q ^ e) = 1 from rfl, mul_one]
    simp only [lieOrderNumerator]
  exact not_jType_of_card (p := 3) (q := q) (J := fixedSubgroup
    (twistedEntrywiseAut TwistTag.D4 j T)) (t := .trialityD4) (n := 0) (f := e)
    (Fact.out : q.Prime) hq2 htn he hcard' hJT

theorem noJTypeComponent_d4_graphField {K : Type} [Field K] [Finite K] {q f : ℕ}
    (hq : q.Prime) (hq2 : q ≠ 2) (hq3 : q ≠ 3) (hK : Nat.card K = q ^ f)
    {α : MulAut (adjointGroup Tag.D4 K)} (hα3 : α ^ 3 = 1)
    (g : adjointGroup Tag.D4 K) (a : Fin Tag.D4.rank → Kˣ) (σ : K ≃+* K) (ε : ℕ)
    (hε : ε < 3) (hε0 : ε ≠ 0) (hσ : σ ≠ 1)
    (hα : α = MulAut.conj g * (exactNormalAut Tag.D4 K a σ 0 * d4Graph K ε)) :
    NoJTypeComponent 3 q α := by
  classical
  haveI : Fact q.Prime := ⟨hq⟩
  haveI : Fintype K := Fintype.ofFinite K
  haveI : CharP K q := charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card, hK])
  haveI : Finite (ModGL Tag.D4 K) := finite_modGL
  haveI : Finite (adjointGroup Tag.D4 K) := Subtype.finite
  have hf : 1 ≤ f := by
    by_contra hf
    have hf0 : f = 0 := by omega
    have := Finite.one_lt_card (α := K)
    rw [hK, hf0, pow_zero] at this
    omega
  have hσ3 := sigma_pow_three_eq_one_of_cube α hα3 g a σ ε hα
  have hord : orderOf σ = 3 := orderOf_eq_prime hσ3 hσ
  obtain ⟨e, T, he, hef, hT, hσT⟩ :=
    exists_frobenius_eq_or_inv_of_orderOf_three hq hf K hK σ hord
  have hK4 : 4 ≤ Nat.card K := by
    rw [hK]
    calc 4 ≤ q ^ 1 := by
          rw [pow_one]
          have h2 := hq.two_le
          omega
      _ ≤ q ^ f := Nat.pow_le_pow_right hq.pos hf
  have hK' : Nat.card K = (q ^ e) ^ 3 := by rw [hK, ← hef, pow_mul]
  rcases hσT with hσT | hσT
  · subst σ
    obtain ⟨ψ, hψ⟩ := exists_conj_eq_twistedEntrywiseAut_of_normalForm K hK hK4 he hef T hT α
      hα3 g a ε hα
    have hε12 : ε = 1 ∨ ε = 2 := by omega
    have hεj : (ε : ℤ) = 1 ∨ (ε : ℤ) = 2 := by
      rcases hε12 with rfl | rfl <;> norm_num
    have htw := noJTypeComponent_twistedEntrywiseAut_D4 hq2 hq3 he hK' T hT (ε : ℤ) hεj
    have hγ : NoJTypeComponent 3 q (ψ * α * ψ⁻¹) := by rw [hψ]; exact htw
    have hconj := noJTypeComponent_conj Nat.prime_three ψ⁻¹ hγ
    have hαeq : ψ⁻¹ * (ψ * α * ψ⁻¹) * (ψ⁻¹)⁻¹ = α := by group
    rwa [hαeq] at hconj
  · subst σ
    obtain ⟨ψ, hψ⟩ := exists_conj_inv_eq_twistedEntrywiseAut_of_normalForm K hK hK4 he hef T T⁻¹
      hT (mul_inv_cancel T) α hα3 g a ε hα
    have hshift : twistedEntrywiseAut TwistTag.D4 (-(ε : ℤ)) T =
        twistedEntrywiseAut TwistTag.D4 (3 - (ε : ℤ)) T := by
      have h := twistedEntrywiseAut_add_mul_order TwistTag.D4 (-(ε : ℤ)) 1 T
      rw [show -(ε : ℤ) + 1 * ((TwistTag.D4.order : ℕ) : ℤ) = 3 - (ε : ℤ) by
        change -(ε : ℤ) + 1 * 3 = _
        ring] at h
      exact h.symm
    have hε12 : ε = 1 ∨ ε = 2 := by omega
    have hj : 3 - (ε : ℤ) = 1 ∨ 3 - (ε : ℤ) = 2 := by
      rcases hε12 with rfl | rfl <;> norm_num
    have htw := noJTypeComponent_twistedEntrywiseAut_D4 hq2 hq3 he hK' T hT (3 - (ε : ℤ)) hj
    have hγ : NoJTypeComponent 3 q (ψ * α⁻¹ * ψ⁻¹) := by rw [hψ, hshift]; exact htw
    have hconj := noJTypeComponent_conj Nat.prime_three ψ⁻¹ hγ
    have hαeq : ψ⁻¹ * (ψ * α⁻¹ * ψ⁻¹) * (ψ⁻¹)⁻¹ = α⁻¹ := by group
    rw [hαeq] at hconj
    simpa using noJTypeComponent_inv hconj

theorem i2020D4Three_of_graphType (h : I2020D4GraphType) : I2020D4Three := by
  intro q hq hq2 hq3 G _instG _instFin f hG β hβ hnot J hJ hJT
  obtain ⟨-, hf, -⟩ := hG.1
  obtain ⟨K, hfieldK, hfinK, hK, ⟨e⟩⟩ := hG.2
  letI := hfieldK
  letI := hfinK
  haveI : Fact q.Prime := ⟨hq⟩
  haveI : Fintype K := Fintype.ofFinite K
  haveI : CharP K q := charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card, hK])
  haveI : Finite (ModGL Tag.D4 K) := finite_modGL
  haveI : Finite (adjointGroup Tag.D4 K) := Subtype.finite
  let Φ : adjointGroup Tag.D4 K ≃* matrixProjectiveDerived (coordinateQuadPlus 4 K) :=
    coordinatePlusWitnessEquiv K (isoAdj K).symm
  let e' : G ≃* matrixProjectiveDerived (coordinateQuadPlus 4 K) :=
    coordinatePlusWitnessEquiv K e
  haveI : Finite (matrixProjectiveDerived (coordinateQuadPlus 4 K)) := Finite.of_equiv _ e'.toEquiv
  let β' : MulAut (matrixProjectiveDerived (coordinateQuadPlus 4 K)) := MulAut.congr e' β
  have hβ' : β' ^ 3 = 1 := by rw [← map_pow, hβ, map_one]
  have hno : NoJTypeComponent 3 q β := by
    by_cases hE : β' ∈ matrixProjectiveImage (coordinateQuadPlus 4 K)
    · intro J' hJ' hJT'
      exact orthOuter_plus_of_mem_image 3 q Nat.prime_three (by norm_num) hq hq2 hq3 G f hG K hK e
        β hβ hnot hE hJ' hJT'
    · obtain ⟨g, a, σ, ε, hε, hε0, hσ3, hαnf⟩ :=
        exists_d4ThreeOuter_normalForm hq hq2 hq3 hK β' hβ' hE
      let α : MulAut (adjointGroup Tag.D4 K) := MulAut.congr Φ.symm β'
      have hα3 : α ^ 3 = 1 := by
        rw [show α = MulAut.congr Φ.symm β' from rfl, ← map_pow, hβ', map_one]
      have hαno : NoJTypeComponent 3 q α := by
        by_cases hσ1 : σ = 1
        · subst σ
          exact h K q f hq hq2 hq3 hK α hα3 g a ε hε hε0 hαnf
        · exact noJTypeComponent_d4_graphField hq hq2 hq3 hK hα3 g a σ ε hε hε0 hσ1 hαnf
      have hβ'no : NoJTypeComponent 3 q β' := by
        have hconj := noJTypeComponent_congr Nat.prime_three Φ hαno
        have hΦα : MulAut.congr Φ α = β' := by
          ext x
          simp [α, MulAut.congr_apply]
        rwa [hΦα] at hconj
      have hconj := noJTypeComponent_congr Nat.prime_three e'.symm hβ'no
      have he' : MulAut.congr e'.symm β' = β := by
        ext x
        simp [β', MulAut.congr_apply]
      rwa [he'] at hconj
  exact i2020FixCent_of_noJTypeComponent hno J hJ hJT

end CFSG.LocalAnalysis.GLTheoremA.I2020

end
