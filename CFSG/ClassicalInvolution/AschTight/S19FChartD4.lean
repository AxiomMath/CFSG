module

public import CFSG.ClassicalInvolution.AschTight.S19FChartG2
public import CFSG.ClassicalInvolution.ModelFacts.G2D4TD4Lin

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.S19F

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.ClassicalInvolution.G2D4Models
  CFSG.ClassicalInvolution.Generic CFSG.LieType.Steinberg.TwistedD4 CFSG.LieType.Steinberg.Adjoint
  Matrix
open scoped MatrixGroups

section Restrict

variable {K : Type} [Field K] {σ : K →+* K}

@[expose] def fixRestrict (δ : K ≃+* K) (hδσ : ∀ c, δ (σ c) = σ (δ c)) :
    fixedField σ ≃+* fixedField σ where
  toFun x := ⟨δ x, by
    change σ (δ x) = δ x
    rw [← hδσ]
    exact congrArg δ x.2⟩
  invFun x := ⟨δ.symm x, by
    change σ (δ.symm x) = δ.symm x
    apply δ.injective
    rw [hδσ, RingEquiv.apply_symm_apply]
    exact x.2⟩
  left_inv x := Subtype.ext (δ.symm_apply_apply x)
  right_inv x := Subtype.ext (δ.apply_symm_apply x)
  map_mul' x y := Subtype.ext (map_mul δ (x : K) y)
  map_add' x y := Subtype.ext (map_add δ (x : K) y)

theorem coe_fixRestrict (δ : K ≃+* K) (hδσ : ∀ c, δ (σ c) = σ (δ c)) (x : fixedField σ) :
    ((fixRestrict δ hδσ x : fixedField σ) : K) = δ x :=
  rfl

end Restrict

section Chart

variable {K : Type} [Field K] {σ : K →+* K} (hσ : ∀ c, σ (σ (σ c)) = c)

theorem coe_xPar_single_d4 (j : Fin d4.rank) (c : K) :
    ((xPar (rootOperatorFamily d4) (Pi.single j 1) c : adjointGroup d4 K) : ModGL d4 K) =
      xUnit d4 K j c := by
  rw [xPar_simple, RootOperatorFamily.coe_eltElement, RootOperatorFamily.eltUnit_simple]

theorem coe_xPar_neg_single_d4 (j : Fin d4.rank) (c : K) :
    ((xPar (rootOperatorFamily d4) (-Pi.single j 1) c : adjointGroup d4 K) : ModGL d4 K) =
      yUnit d4 K j c := by
  rw [xPar_neg_simple, RootOperatorFamily.coe_eltElement, RootOperatorFamily.eltUnit_neg_simple]

theorem coe_xOuter_one (c d e : K) :
    ((xOuter 1 c d e : adjointGroup d4 K) : ModGL d4 K) =
      xUnit d4 K (nd 0) c * xUnit d4 K (nd 1) d * xUnit d4 K (nd 3) e := by
  rw [xOuter, Subgroup.coe_mul, Subgroup.coe_mul, one_smul, one_smul, one_smul,
    coe_xPar_single_d4, coe_xPar_single_d4, coe_xPar_single_d4]

theorem coe_xOuter_neg_one (c d e : K) :
    ((xOuter (-1) c d e : adjointGroup d4 K) : ModGL d4 K) =
      yUnit d4 K (nd 0) c * yUnit d4 K (nd 1) d * yUnit d4 K (nd 3) e := by
  rw [xOuter, Subgroup.coe_mul, Subgroup.coe_mul, neg_one_smul, neg_one_smul, neg_one_smul,
    coe_xPar_neg_single_d4, coe_xPar_neg_single_d4, coe_xPar_neg_single_d4]

theorem slMap_uSL {L : Type} [Field L] (f : L →+* L) (c : L) :
    SpecialLinearGroup.map f (uSL c) = uSL (f c) := Subtype.ext (by
  rw [SpecialLinearGroup.map_apply_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [uSL])

theorem slMap_vSL {L : Type} [Field L] (f : L →+* L) (c : L) :
    SpecialLinearGroup.map f (vSL c) = vSL (f c) := Subtype.ext (by
  rw [SpecialLinearGroup.map_apply_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [vSL])

include hσ in
theorem slLong_entrywise (δ : K ≃+* K) (hδσ : ∀ c, δ (σ c) = σ (δ c))
    (A : SL(2, fixedField σ)) :
    Units.map (entrywiseHom δ.toRingHom) (twistedIncl σ (slLong σ hσ A)) =
      twistedIncl σ (slLong σ hσ (SpecialLinearGroup.map (fixRestrict δ hδσ).toRingHom A)) := by
  have h : (Units.map (entrywiseHom δ.toRingHom)).comp ((twistedIncl σ).comp (slLong σ hσ)) =
      ((twistedIncl σ).comp (slLong σ hσ)).comp
        (SpecialLinearGroup.map (fixRestrict δ hδσ).toRingHom) := by
    refine MonoidHom.eq_of_eqOn_dense
      (CFSG.LocalAnalysis.ComponentInitial.sl2_closure_upper_lower (K := fixedField σ)) ?_
    rintro M (⟨c, rfl⟩ | ⟨c, rfl⟩)
    · change Units.map (entrywiseHom δ.toRingHom) (twistedIncl σ (slLong σ hσ (uSL c))) =
        twistedIncl σ (slLong σ hσ (SpecialLinearGroup.map (fixRestrict δ hδσ).toRingHom (uSL c)))
      rw [slMap_uSL, twistedIncl_slLong_upper, twistedIncl_slLong_upper, coe_xPar_single_d4,
        coe_xPar_single_d4, units_map_entrywiseHom_xUnit]
      rfl
    · change Units.map (entrywiseHom δ.toRingHom) (twistedIncl σ (slLong σ hσ (vSL c))) =
        twistedIncl σ (slLong σ hσ (SpecialLinearGroup.map (fixRestrict δ hδσ).toRingHom (vSL c)))
      rw [slMap_vSL, twistedIncl_slLong_lower, twistedIncl_slLong_lower, coe_xPar_neg_single_d4,
        coe_xPar_neg_single_d4, units_map_entrywiseHom_yUnit]
      rfl
  exact DFunLike.congr_fun h A

include hσ in
theorem slShort_entrywise (δ : K ≃+* K) (hδσ : ∀ c, δ (σ c) = σ (δ c)) (A : SL(2, K)) :
    Units.map (entrywiseHom δ.toRingHom) (twistedIncl σ (slShort σ hσ A)) =
      twistedIncl σ (slShort σ hσ (SpecialLinearGroup.map δ.toRingHom A)) := by
  have h : (Units.map (entrywiseHom δ.toRingHom)).comp ((twistedIncl σ).comp (slShort σ hσ)) =
      ((twistedIncl σ).comp (slShort σ hσ)).comp (SpecialLinearGroup.map δ.toRingHom) := by
    refine MonoidHom.eq_of_eqOn_dense
      (CFSG.LocalAnalysis.ComponentInitial.sl2_closure_upper_lower (K := K)) ?_
    rintro M (⟨c, rfl⟩ | ⟨c, rfl⟩)
    · change Units.map (entrywiseHom δ.toRingHom) (twistedIncl σ (slShort σ hσ (uSL c))) =
        twistedIncl σ (slShort σ hσ (SpecialLinearGroup.map δ.toRingHom (uSL c)))
      rw [slMap_uSL, twistedIncl_slShort_upper, twistedIncl_slShort_upper, coe_xOuter_one,
        coe_xOuter_one, map_mul, map_mul, units_map_entrywiseHom_xUnit,
        units_map_entrywiseHom_xUnit, units_map_entrywiseHom_xUnit]
      change xUnit d4 K (nd 0) (δ c) * xUnit d4 K (nd 1) (δ (σ c)) *
          xUnit d4 K (nd 3) (δ (σ (σ c))) = _
      rw [hδσ, hδσ, hδσ]
      rfl
    · change Units.map (entrywiseHom δ.toRingHom) (twistedIncl σ (slShort σ hσ (vSL c))) =
        twistedIncl σ (slShort σ hσ (SpecialLinearGroup.map δ.toRingHom (vSL c)))
      rw [slMap_vSL, twistedIncl_slShort_lower, twistedIncl_slShort_lower, coe_xOuter_neg_one,
        coe_xOuter_neg_one, map_mul, map_mul, units_map_entrywiseHom_yUnit,
        units_map_entrywiseHom_yUnit, units_map_entrywiseHom_yUnit]
      change yUnit d4 K (nd 0) (δ c) * yUnit d4 K (nd 1) (δ (σ c)) *
          yUnit d4 K (nd 3) (δ (σ (σ c))) = _
      rw [hδσ, hδσ, hδσ]
      rfl
  exact DFunLike.congr_fun h A

end Chart

section Node

variable {K : Type} [Field K] [Finite K] {σ : K →+* K} (hσ3 : ∀ c, σ (σ (σ c)) = c)

include hσ3 in
theorem fieldInvolution_fixes_nonabelian_node {rK rF : ℕ} (hKr : Nat.card K = rK ^ 2)
    (hFr : Nat.card (fixedField σ) = rF ^ 2) (hoddK : Odd (Nat.card K))
    (hoddF : Odd (Nat.card (fixedField σ)))
    (hC₀ : graphFixedRootGroup TwistTag.D4 K σ ≤ (twistedIncl σ).range)
    (hgF : ∀ g : twistedGroup σ, twistedIncl σ g ∈ graphFixedRootGroup TwistTag.D4 K σ)
    (δ : K ≃+* K) (hδ : ∀ c, δ c = c ^ rK) (hδσ : ∀ c, δ (σ c) = σ (δ c))
    (hδF : ∀ c : K, σ c = c → δ c = c ^ rF) (β : MulAut ↥(twistedGroup σ))
    (hβ : ∀ u, twistedIncl σ (β u) = Units.map (entrywiseHom δ.toRingHom) (twistedIncl σ u))
    (i : Fin (Tag.rank .G2)) (g : twistedGroup σ)
    (hβR : (conjSub g (CFSG.LieType.CurtisTits.rankOne (twistedRootGroup σ) i)).map
      β.toMonoidHom = conjSub g (CFSG.LieType.CurtisTits.rankOne (twistedRootGroup σ) i)) :
    ∃ P : Subgroup ↥(twistedGroup σ), IsPGroup 2 P ∧
      P ≤ conjSub g (CFSG.LieType.CurtisTits.rankOne (twistedRootGroup σ) i) ∧
      (∀ x ∈ P, β x = x) ∧ ∃ x ∈ P, ∃ y ∈ P, x * y ≠ y * x := by
  have hδid : δ.toRingHom.comp δ.toRingHom = RingHom.id K :=
    RingHom.ext fun c => frob_frob hKr hδ c
  have hβ2 : ∀ x, β (β x) = x := fun x =>
    twistedIncl_injective σ (by rw [hβ, hβ, units_map_entrywiseHom_invol hδid])
  have hK1 : (-1 : Kˣ) ≠ 1 := fun h => two_ne_zero_of_odd hoddK (by
    have h' := congrArg Units.val h
    rw [Units.val_neg, Units.val_one] at h'
    linear_combination -h')
  have hi : (i : ℕ) < 2 := i.2
  rcases (by omega : (i : ℕ) = 0 ∨ (i : ℕ) = 1) with h0 | h1
  · have hi' : i = ng 0 := Fin.ext h0
    subst hi'
    have hδF' : ∀ c : fixedField σ, fixRestrict δ hδσ c = c ^ rF := fun c =>
      Subtype.ext (by rw [coe_fixRestrict, SubmonoidClass.coe_pow]; exact hδF c c.2)
    rw [ModelFacts.rankOne_long_eq_range hσ3] at hβR ⊢
    exact exists_fixed_quaternion_of_stable hFr hδF' hoddF β hβ2 (slLong σ hσ3)
      (slLong_injective hσ3)
      (fun A => twistedIncl_injective σ (by rw [hβ, slLong_entrywise hσ3 δ hδσ]))
      (fun c hc => linAct_of_centralizes_long hσ3 hK1 (two_ne_zero_of_odd hoddF) hC₀ hgF hc) g
      hβR
  · have hi' : i = ng 1 := Fin.ext h1
    subst hi'
    rw [ModelFacts.rankOne_short_eq_range hσ3] at hβR ⊢
    exact exists_fixed_quaternion_of_stable hKr hδ hoddK β hβ2 (slShort σ hσ3)
      (slShort_injective hσ3)
      (fun A => twistedIncl_injective σ (by rw [hβ, slShort_entrywise hσ3 δ hδσ]))
      (fun c hc => linAct_of_centralizes_short hσ3 hK1 (two_ne_zero_of_odd hoddK) hC₀ hgF hc) g
      hβR

end Node

section Model

variable {p : ℕ} [Fact p.Prime]

theorem fieldInvolution_fixes_nonabelian_d4 (hp2 : p ≠ 2) {e a : ℕ} (hea : e = 2 * a)
    (ha : 1 ≤ a) (δ : GaloisField p (3 * e) ≃+* GaloisField p (3 * e))
    (hδ : ∀ c, δ c = c ^ (p ^ (3 * a)))
    (β : MulAut ↥(twistedGroup (iterateFrobenius (GaloisField p (3 * e)) p e)))
    (hβ : ∀ u, twistedIncl _ (β u) = Units.map (entrywiseHom δ.toRingHom) (twistedIncl _ u))
    {R : Subgroup ↥(twistedGroup (iterateFrobenius (GaloisField p (3 * e)) p e))}
    (hR : R ∈ fundamentalSubgroups .trialityD4
      (twistedDatum (iterateFrobenius (GaloisField p (3 * e)) p e)))
    (hβR : R.map β.toMonoidHom = R) :
    ∃ P : Subgroup ↥(twistedGroup (iterateFrobenius (GaloisField p (3 * e)) p e)),
      IsPGroup 2 P ∧ P ≤ R ∧ (∀ x ∈ P, β x = x) ∧ ∃ x ∈ P, ∃ y ∈ P, x * y ≠ y * x := by
  classical
  have he : 1 ≤ e := by omega
  have hK3 : Nat.card (GaloisField p (3 * e)) = (p ^ e) ^ 3 := by
    rw [GaloisField.card p (3 * e) (by omega), pow_mul']
  have hfin : Finite (GaloisField p (3 * e)) := Nat.finite_of_card_ne_zero (by
    rw [hK3]
    exact (pow_pos (pow_pos (Fact.out : p.Prime).pos e) _).ne')
  have hσq : ∀ c : GaloisField p (3 * e), iterateFrobenius (GaloisField p (3 * e)) p e c =
      c ^ (p ^ e) := fun c => iterateFrobenius_def p e c
  have hσ3 := sigma_three_of_card hK3 hσq
  have hpodd : Odd p := (Fact.out : p.Prime).odd_of_ne_two hp2
  have hK2 : Nat.card (GaloisField p (3 * e)) = (p ^ (3 * a)) ^ 2 := by
    rw [hK3, ← pow_mul, ← pow_mul]
    congr 1
    omega
  have hoddK : Odd (Nat.card (GaloisField p (3 * e))) := by rw [hK3]; exact hpodd.pow.pow
  have hcardF : Nat.card (fixedField (iterateFrobenius (GaloisField p (3 * e)) p e)) =
      (p ^ a) ^ 2 := by
    refine (ModelFacts.card_fixedField_iterateFrobenius (p := p) he).trans ?_
    rw [← pow_mul]
    congr 1
    omega
  have hoddF : Odd (Nat.card (fixedField (iterateFrobenius (GaloisField p (3 * e)) p e))) := by
    rw [hcardF]
    exact hpodd.pow.pow
  have hδσ : ∀ c, δ (iterateFrobenius (GaloisField p (3 * e)) p e c) =
      iterateFrobenius (GaloisField p (3 * e)) p e (δ c) := fun c => by
    rw [hσq, hσq, hδ, hδ, ← pow_mul, ← pow_mul, mul_comm (p ^ e) (p ^ (3 * a))]
  have hδF : ∀ c, iterateFrobenius (GaloisField p (3 * e)) p e c = c → δ c = c ^ (p ^ a) :=
    fun c hc => by
      rw [hσq] at hc
      rw [hδ, show 3 * a = e + a by omega, pow_add, pow_mul, hc]
  have h3 := RouteD.G2D4.map_twistedGroup_eq_graphFixedRootGroup p e hp2 he
  obtain ⟨i, g, rfl⟩ := Asc77.exists_conj_rankOne_node_of_trialityD4 0 p e ⟨Fact.out, he, rfl⟩ hR
  refine fieldInvolution_fixes_nonabelian_node hσ3 hK2 hcardF hoddK hoddF ?_ ?_ δ hδ hδσ hδF β hβ
    i g hβR
  · rw [← h3]
    rintro _ ⟨y, hy, rfl⟩
    exact ⟨⟨y, hy⟩, rfl⟩
  · intro x
    rw [← h3]
    exact ⟨x, x.2, rfl⟩

end Model

end CFSG.ClassicalInvolution.Disconnected.AschTight.S19F
