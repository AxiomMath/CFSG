module

public import CFSG.HardMathSupport.Lang.E6Descent.OuterFixed27D4AmbientDescent
public import CFSG.HardMathSupport.Lang.D4Three.Outer

public noncomputable section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Lang.E6Descent

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.GroupTheory
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.OuterAutomorphisms (inner)


section FixedSubfield

variable {ℓ f : ℕ} [Fact ℓ.Prime] {K K₃ : Type} [Field K] [Finite K] [Field K₃] [Algebra K K₃]

theorem graphType_frobenius_algebraMap (hK : Nat.card K = ℓ ^ f) (Fr : K₃ ≃+* K₃)
    (hFr : ∀ c, Fr c = c ^ (ℓ ^ f)) (c : K) : Fr (algebraMap K K₃ c) = algebraMap K K₃ c := by
  have : Fintype K := Fintype.ofFinite K
  rw [hFr, ← map_pow, ← hK, Nat.card_eq_fintype_card, FiniteField.pow_card]

@[expose] def graphTypeFixedEquiv (hf : 1 ≤ f) (hK : Nat.card K = ℓ ^ f) [Finite K₃]
    (hK₃ : Nat.card K₃ = (ℓ ^ f) ^ 3) (Fr : K₃ ≃+* K₃) (hFr : ∀ c, Fr c = c ^ (ℓ ^ f)) :
    K ≃+* fixSubfield Fr := by
  have hcard := CFSG.RankThree.PartOne.KGD.card_fixSubfield_cube (Fact.out : ℓ.Prime) hf hK₃ Fr hFr
  let φ : K →+* fixSubfield Fr := (algebraMap K K₃).codRestrict (fixSubfield Fr)
    fun c => (mem_fixSubfield Fr).2 (graphType_frobenius_algebraMap hK Fr hFr c)
  have hφ : Function.Injective φ := fun a b h => (algebraMap K K₃).injective
    (congrArg Subtype.val h)
  have : Finite (fixSubfield Fr) := Nat.finite_of_card_ne_zero (by
    rw [hcard]; exact (pow_pos (Fact.out : ℓ.Prime).pos f).ne')
  exact RingEquiv.ofBijective φ (hφ.bijective_of_nat_card_le (by rw [hcard, hK]))

theorem graphTypeFixedEquiv_apply (hf : 1 ≤ f) (hK : Nat.card K = ℓ ^ f) [Finite K₃]
    (hK₃ : Nat.card K₃ = (ℓ ^ f) ^ 3) (Fr : K₃ ≃+* K₃) (hFr : ∀ c, Fr c = c ^ (ℓ ^ f)) (c : K) :
    ((graphTypeFixedEquiv hf hK hK₃ Fr hFr c : fixSubfield Fr) : K₃) = algebraMap K K₃ c := rfl

end FixedSubfield

section Group

variable {G : Type*} [Group G]

theorem graphType_commute_of_conj_eq (A B W : G) (h : A * W * A⁻¹ = B * W * B⁻¹) :
    A⁻¹ * B * W = W * (A⁻¹ * B) := by
  calc A⁻¹ * B * W = A⁻¹ * (B * W * B⁻¹) * B := by group
    _ = A⁻¹ * (A * W * A⁻¹) * B := by rw [h]
    _ = W * (A⁻¹ * B) := by group

theorem graphType_twisted_fixed (P a b c x : G) (hx : x = a⁻¹ * (P * b * P⁻¹))
    (hF : b⁻¹ * (P * c * P⁻¹) = x) : P * (b * c⁻¹) * P⁻¹ = a * b⁻¹ := by
  have h1 : P * c * P⁻¹ = b * (a⁻¹ * (P * b * P⁻¹)) := by
    rw [← hx, ← hF]; group
  calc P * (b * c⁻¹) * P⁻¹ = (P * b * P⁻¹) * (P * c * P⁻¹)⁻¹ := by group
    _ = (P * b * P⁻¹) * (b * (a⁻¹ * (P * b * P⁻¹)))⁻¹ := by rw [h1]
    _ = a * b⁻¹ := by group

end Group

section Core

theorem twentySeven_dvd_card_fixedSubgroup_graph_ambient {ℓ f : ℕ} [Fact ℓ.Prime] (hf : 1 ≤ f)
    (K : Type) [Field K] [Finite K] (hK : Nat.card K = ℓ ^ f)
    (K₃ : Type) [Field K₃] [Finite K₃] [CharP K₃ ℓ] [Algebra K K₃]
    (hK₃ : Nat.card K₃ = (ℓ ^ f) ^ 3) (Fr : K₃ ≃+* K₃) (hFr : ∀ c, Fr c = c ^ (ℓ ^ f))
    (L : Type) [Field L] [CharP L ℓ] [Algebra K₃ L] [IsAlgClosure K₃ L]
    (x : ModGL TwistTag.D4.tag L) (hx : x ∈ adjointGroup TwistTag.D4.tag L)
    (hxF : Units.map (entrywiseHom (iterateFrobenius L ℓ f)) x = x)
    (hxP : (x * diagramMap TwistTag.D4 L) ^ 3 = 1)
    (β : MulAut (adjointGroup TwistTag.D4.tag K₃))
    (hβ : ∀ u : adjointGroup TwistTag.D4.tag K₃,
      baseChangeGL (algebraMap K₃ L) (β u : ModGL TwistTag.D4.tag K₃) =
        x * baseChangeGL (algebraMap K₃ L)
          (twistedEntrywiseAut TwistTag.D4 1 Fr u : ModGL TwistTag.D4.tag K₃) * x⁻¹)
    (α : MulAut (adjointGroup TwistTag.D4.tag K))
    (hα : ∀ u : adjointGroup TwistTag.D4.tag K,
      baseChangeGL ((algebraMap K₃ L).comp (algebraMap K K₃)) (α u : ModGL TwistTag.D4.tag K) =
        x * (diagramMap TwistTag.D4 L *
          baseChangeGL ((algebraMap K₃ L).comp (algebraMap K K₃)) (u : ModGL TwistTag.D4.tag K) *
            (diagramMap TwistTag.D4 L)⁻¹) * x⁻¹) :
    27 ∣ Nat.card (fixedSubgroup α) := by
  classical
  have hℓ : ℓ.Prime := Fact.out
  have : Fintype K₃ := Fintype.ofFinite K₃
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K₃
  have hFr3 : ∀ c, Fr (Fr (Fr c)) = c := fun c => by
    rw [hFr, hFr, hFr, ← pow_mul, ← pow_mul, show ℓ ^ f * (ℓ ^ f * ℓ ^ f) = (ℓ ^ f) ^ 3 by ring,
      ← hK₃, Nat.card_eq_fintype_card, FiniteField.pow_card]
  have hK₃4 : 4 ≤ Nat.card K₃ := by
    rw [hK₃]
    have h2 : 2 ≤ ℓ ^ f := le_trans hℓ.two_le (Nat.le_self_pow (by omega) ℓ)
    calc 4 ≤ 2 ^ 3 := by norm_num
      _ ≤ (ℓ ^ f) ^ 3 := Nat.pow_le_pow_left h2 3
  obtain ⟨FrL, hFrLdef⟩ : ∃ FrL : L →+* L, FrL = iterateFrobenius L ℓ f := ⟨_, rfl⟩
  have hFrc : FrL.comp (algebraMap K₃ L) = (algebraMap K₃ L).comp Fr.toRingHom := by
    ext c
    simp [hFrLdef, iterateFrobenius_def, hFr, map_pow]
  have hFι : ∀ w : ModGL TwistTag.D4.tag K₃,
      Units.map (entrywiseHom FrL) (baseChangeGL (algebraMap K₃ L) w) =
        baseChangeGL (algebraMap K₃ L) (Units.map (entrywiseHom Fr.toRingHom) w) := fun w => by
    rw [units_map_entrywiseHom_eq_baseChangeGL, units_map_entrywiseHom_eq_baseChangeGL,
      baseChangeGL_baseChangeGL, baseChangeGL_baseChangeGL, hFrc]
  have hFP : Units.map (entrywiseHom FrL) (diagramMap TwistTag.D4 L) = diagramMap TwistTag.D4 L :=
    units_map_entrywiseHom_diagramMap (t := TwistTag.D4) FrL
  have hα₀ : ∀ w : adjointGroup TwistTag.D4.tag K₃,
      baseChangeGL (algebraMap K₃ L) (twistedEntrywiseAut TwistTag.D4 1 Fr w : ModGL TwistTag.D4.tag K₃) =
        diagramMap TwistTag.D4 L * Units.map (entrywiseHom FrL)
          (baseChangeGL (algebraMap K₃ L) (w : ModGL TwistTag.D4.tag K₃)) *
            (diagramMap TwistTag.D4 L)⁻¹ := by
    intro w
    rw [coe_twistedEntrywiseAut, zpow_one, map_mul, map_mul, map_inv, baseChangeGL_diagramMap, hFι]
  have hstep : ∀ w : adjointGroup TwistTag.D4.tag K₃,
      baseChangeGL (algebraMap K₃ L) (β w : ModGL TwistTag.D4.tag K₃) =
        (x * diagramMap TwistTag.D4 L) * Units.map (entrywiseHom FrL)
          (baseChangeGL (algebraMap K₃ L) (w : ModGL TwistTag.D4.tag K₃)) *
            (x * diagramMap TwistTag.D4 L)⁻¹ := by
    intro w
    rw [hβ, hα₀]
    group
  rw [← hFrLdef] at hxF
  have hMF : Units.map (entrywiseHom FrL) (x * diagramMap TwistTag.D4 L) =
      x * diagramMap TwistTag.D4 L := by
    rw [map_mul, hFP, hxF]
  have hFr3U : ∀ w : ModGL TwistTag.D4.tag K₃, Units.map (entrywiseHom Fr.toRingHom)
      (Units.map (entrywiseHom Fr.toRingHom) (Units.map (entrywiseHom Fr.toRingHom) w)) = w := by
    intro w
    rw [units_map_entrywiseHom_comp, units_map_entrywiseHom_comp]
    have h1 : (Fr.toRingHom.comp Fr.toRingHom).comp Fr.toRingHom = RingHom.id K₃ :=
      RingHom.ext hFr3
    rw [h1]
    exact Units.ext (entrywise_id (R := K₃) _)
  have hF3 : ∀ v : ModGL TwistTag.D4.tag K₃, Units.map (entrywiseHom FrL) (Units.map
      (entrywiseHom FrL) (Units.map (entrywiseHom FrL) (baseChangeGL (algebraMap K₃ L) v))) =
        baseChangeGL (algebraMap K₃ L) v := by
    intro v
    rw [hFι, hFι, hFι, hFr3U]
  have hM3 : (x * diagramMap TwistTag.D4 L) * (x * diagramMap TwistTag.D4 L) *
      (x * diagramMap TwistTag.D4 L) = 1 := by
    rw [← pow_three']
    exact hxP
  have hβ3 : β ^ 3 = 1 := by
    refine MulEquiv.ext fun w => Subtype.ext (baseChangeGL_injective (algebraMap K₃ L) ?_)
    have h3 : (β ^ 3) w = β (β (β w)) := by
      simp only [pow_succ, pow_zero, one_mul, MulAut.mul_apply]
    rw [h3, hstep, hstep, hstep]
    simp only [map_mul, map_inv, hMF, hF3]
    calc _ = ((x * diagramMap TwistTag.D4 L) * (x * diagramMap TwistTag.D4 L) *
          (x * diagramMap TwistTag.D4 L)) * baseChangeGL (algebraMap K₃ L) (w : ModGL TwistTag.D4.tag K₃) *
          ((x * diagramMap TwistTag.D4 L) * (x * diagramMap TwistTag.D4 L) *
          (x * diagramMap TwistTag.D4 L))⁻¹ := by group
      _ = _ := by rw [hM3]; simp
  have hK₃' : Nat.card K₃ = ℓ ^ (f * 3) := by rw [hK₃, ← pow_mul]
  obtain ⟨ψ, h, hhF, hψι, hψβ⟩ := exists_conj_eq_twistedEntrywiseAut_of_ambient TwistTag.D4 K₃ hK₃'
    hK₃4 hf (rfl : f * 3 = f * 3) Fr hFr 1 L x hx β hβ hβ3
  rw [← hFrLdef] at hhF
  have hFrL' : ∀ c, FrL c = c ^ (ℓ ^ f) := fun c => by rw [hFrLdef, iterateFrobenius_def]
  have hcomm : ∀ u, twistedEntrywiseAut TwistTag.D4 1 Fr (ψ u) = ψ (β u) := fun u => by
    have := congrArg (fun φ : MulAut (adjointGroup TwistTag.D4.tag K₃) => φ (ψ u)) hψβ
    simpa [MulAut.mul_apply, MulAut.inv_apply_self] using this.symm
  have hE : ∀ u : adjointGroup TwistTag.D4.tag K₃,
      (diagramMap TwistTag.D4 L * Units.map (entrywiseHom FrL) (h : ModGL TwistTag.D4.tag L) *
          (diagramMap TwistTag.D4 L)⁻¹) *
        baseChangeGL (algebraMap K₃ L) (twistedEntrywiseAut TwistTag.D4 1 Fr u : ModGL TwistTag.D4.tag K₃) *
          (diagramMap TwistTag.D4 L * Units.map (entrywiseHom FrL) (h : ModGL TwistTag.D4.tag L) *
            (diagramMap TwistTag.D4 L)⁻¹)⁻¹ =
        ((h : ModGL TwistTag.D4.tag L) * x) *
          baseChangeGL (algebraMap K₃ L) (twistedEntrywiseAut TwistTag.D4 1 Fr u : ModGL TwistTag.D4.tag K₃) *
            ((h : ModGL TwistTag.D4.tag L) * x)⁻¹ := by
    intro u
    have h1 := hα₀ (ψ u)
    rw [hcomm u, hψι (β u), hψι u] at h1
    simp only [map_mul, map_inv] at h1
    calc _ = diagramMap TwistTag.D4 L * (Units.map (entrywiseHom FrL) (h : ModGL TwistTag.D4.tag L) *
          Units.map (entrywiseHom FrL) (baseChangeGL (algebraMap K₃ L)
            (u : ModGL TwistTag.D4.tag K₃)) *
          (Units.map (entrywiseHom FrL) (h : ModGL TwistTag.D4.tag L))⁻¹) *
          (diagramMap TwistTag.D4 L)⁻¹ := by rw [hα₀ u]; group
      _ = (h : ModGL TwistTag.D4.tag L) * baseChangeGL (algebraMap K₃ L)
          (β u : ModGL TwistTag.D4.tag K₃) * (h : ModGL TwistTag.D4.tag L)⁻¹ := h1.symm
      _ = _ := by rw [hβ u]; group
  have hAad : diagramMap TwistTag.D4 L * Units.map (entrywiseHom FrL) (h : ModGL TwistTag.D4.tag L) *
      (diagramMap TwistTag.D4 L)⁻¹ ∈ adjointGroup TwistTag.D4.tag L := by
    have hconj := map_conj_diagramMap_zpow TwistTag.D4 L 1
    rw [zpow_one] at hconj
    refine conj_mem_adjointGroup_of_map_eq hconj _ ?_
    rw [hFrLdef]
    exact entrywiseFrobGL_mem ℓ f h.2
  have hN1 : (diagramMap TwistTag.D4 L * Units.map (entrywiseHom FrL)
      (h : ModGL TwistTag.D4.tag L) * (diagramMap TwistTag.D4 L)⁻¹)⁻¹ * ((h : ModGL TwistTag.D4.tag L) * x)
        = 1 := by
    obtain ⟨-, -, hfaith, -⟩ :=
      Chevalley_large_finite_root_centralizer_faithfulness_of_four_le TwistTag.D4.tag K₃ hK₃4 L
        (algebraMap K₃ L)
    refine hfaith _ (mul_mem (inv_mem hAad) (mul_mem h.2 hx)) fun w hw => ?_
    obtain ⟨w', hw', rfl⟩ := hw
    have h2 := hE ((twistedEntrywiseAut TwistTag.D4 1 Fr)⁻¹ ⟨w', hw'⟩)
    rw [MulAut.apply_inv_self] at h2
    exact graphType_commute_of_conj_eq _ _ _ h2
  have hxh : x = (h : ModGL TwistTag.D4.tag L)⁻¹ * (diagramMap TwistTag.D4 L *
      Units.map (entrywiseHom FrL) (h : ModGL TwistTag.D4.tag L) * (diagramMap TwistTag.D4 L)⁻¹) := by
    calc x = (h : ModGL TwistTag.D4.tag L)⁻¹ * ((diagramMap TwistTag.D4 L *
        Units.map (entrywiseHom FrL) (h : ModGL TwistTag.D4.tag L) * (diagramMap TwistTag.D4 L)⁻¹) *
          ((diagramMap TwistTag.D4 L * Units.map (entrywiseHom FrL)
            (h : ModGL TwistTag.D4.tag L) * (diagramMap TwistTag.D4 L)⁻¹)⁻¹ *
              ((h : ModGL TwistTag.D4.tag L) * x))) := by group
      _ = _ := by rw [hN1, mul_one]
  have hFhad : Units.map (entrywiseHom FrL) (h : ModGL TwistTag.D4.tag L) ∈
      adjointGroup TwistTag.D4.tag L := by
    rw [hFrLdef]
    exact entrywiseFrobGL_mem ℓ f h.2
  have hzfix : diagramMap TwistTag.D4 L * Units.map (entrywiseHom FrL)
      ((h : ModGL TwistTag.D4.tag L) * (Units.map (entrywiseHom FrL)
        (h : ModGL TwistTag.D4.tag L))⁻¹) * (diagramMap TwistTag.D4 L)⁻¹ =
      (h : ModGL TwistTag.D4.tag L) * (Units.map (entrywiseHom FrL)
        (h : ModGL TwistTag.D4.tag L))⁻¹ := by
    have hFx := hxF
    rw [hxh] at hFx
    simp only [map_mul, map_inv, hFP] at hFx
    rw [map_mul, map_inv]
    exact graphType_twisted_fixed _ _ _ _ _ rfl hFx
  have hzad : (h : ModGL TwistTag.D4.tag L) * (Units.map (entrywiseHom FrL)
      (h : ModGL TwistTag.D4.tag L))⁻¹ ∈ adjointGroup TwistTag.D4.tag L :=
    mul_mem h.2 (inv_mem hFhad)
  have hset := (triality_both_field_orientations_simple_full_ambient_fixed_group (ℓ := ℓ) (d := f) hℓ hf K₃ hK₃ L 1
    (Or.inl rfl) Fr.toRingHom (fun c => by simpa using hFr c) FrL hFrL').2.1
  have hzmem : (h : ModGL TwistTag.D4.tag L) * (Units.map (entrywiseHom FrL)
      (h : ModGL TwistTag.D4.tag L))⁻¹ ∈ ((graphFixedRootGroup TwistTag.D4 K₃ Fr.toRingHom).map
        (baseChangeGL (algebraMap K₃ L)) : Set (ModGL TwistTag.D4.tag L)) := by
    rw [← hset]
    exact ⟨hzad, by rw [pow_one]; exact hzfix⟩
  obtain ⟨z₀, hz₀, hz₀eq⟩ := hzmem
  set z' : ↥(graphFixedRootGroup TwistTag.D4 K₃ Fr.toRingHom) := ⟨z₀, hz₀⟩ with hz'
  set δ₀ : MulAut ↥(graphFixedRootGroup TwistTag.D4 K₃ Fr.toRingHom) :=
    fieldActor (t := TwistTag.D4) Fr Fr with hδ₀def
  have hδcoe : ∀ g : ↥(graphFixedRootGroup TwistTag.D4 K₃ Fr.toRingHom),
      ((δ₀ g : ↥(graphFixedRootGroup TwistTag.D4 K₃ Fr.toRingHom)) : ModGL TwistTag.D4.tag K₃) =
        Units.map (entrywiseHom Fr.toRingHom) (g : ModGL TwistTag.D4.tag K₃) :=
    fun g => coe_fieldActor (t := TwistTag.D4) Fr Fr g
  have hδ3 : δ₀ ^ 3 = 1 := D4Three.fieldActor_cube (D4Three.sigma_cube hK₃ Fr hFr)
  have hδ3' : ∀ y, δ₀ (δ₀ (δ₀ y)) = y := fun y => by
    have h3 : (δ₀ ^ 3) y = δ₀ (δ₀ (δ₀ y)) := by
      rw [pow_three, MulAut.mul_apply, MulAut.mul_apply]
    rw [← h3, hδ3]
    rfl
  have hF3h : Units.map (entrywiseHom FrL) (Units.map (entrywiseHom FrL)
      (Units.map (entrywiseHom FrL) (h : ModGL TwistTag.D4.tag L))) = h := by
    rw [units_map_entrywiseHom_comp, units_map_entrywiseHom_comp]
    have hpow : (FrL.comp FrL).comp FrL = FrL ^ TwistTag.D4.order :=
      RingHom.ext fun c => by rw [RingHom.coe_pow]; rfl
    rw [hpow]
    exact hhF
  have hN : z' * δ₀ z' * δ₀ (δ₀ z') = 1 := by
    refine Subtype.ext (baseChangeGL_injective (algebraMap K₃ L) ?_)
    have hz : baseChangeGL (algebraMap K₃ L) (z' : ModGL TwistTag.D4.tag K₃) =
        (h : ModGL TwistTag.D4.tag L) * (Units.map (entrywiseHom FrL)
          (h : ModGL TwistTag.D4.tag L))⁻¹ := hz₀eq
    have e1 : baseChangeGL (algebraMap K₃ L) ((δ₀ z' : ↥(graphFixedRootGroup TwistTag.D4 K₃
        Fr.toRingHom)) : ModGL TwistTag.D4.tag K₃) = Units.map (entrywiseHom FrL)
          ((h : ModGL TwistTag.D4.tag L) * (Units.map (entrywiseHom FrL)
            (h : ModGL TwistTag.D4.tag L))⁻¹) := by
      rw [hδcoe, ← hFι, hz]
    have e2 : baseChangeGL (algebraMap K₃ L) ((δ₀ (δ₀ z') : ↥(graphFixedRootGroup TwistTag.D4 K₃
        Fr.toRingHom)) : ModGL TwistTag.D4.tag K₃) = Units.map (entrywiseHom FrL)
          (Units.map (entrywiseHom FrL) ((h : ModGL TwistTag.D4.tag L) *
            (Units.map (entrywiseHom FrL) (h : ModGL TwistTag.D4.tag L))⁻¹)) := by
      rw [hδcoe, ← hFι, e1]
    rw [Subgroup.coe_mul, Subgroup.coe_mul, map_mul, map_mul, hz, e1, e2, Subgroup.coe_one,
      map_one]
    simp only [map_mul, map_inv, hF3h]
    group
  have hαhat3 : (MulAut.conj z' * δ₀) ^ 3 = 1 := by
    refine MulEquiv.ext fun y => ?_
    have h3 : ((MulAut.conj z' * δ₀) ^ 3) y =
        (z' * δ₀ z' * δ₀ (δ₀ z')) * y * (z' * δ₀ z' * δ₀ (δ₀ z'))⁻¹ := by
      simp only [pow_three, MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv, hδ3']
      group
    rw [h3, hN, one_mul, inv_one, mul_one]
    rfl
  have hout : (MulAut.conj z' * δ₀) ∉ CFSG.ComponentClassification.OuterAutomorphisms.inner ↥(graphFixedRootGroup TwistTag.D4 K₃ Fr.toRingHom) := by
    intro hin
    have hinn : δ₀ ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner ↥(graphFixedRootGroup TwistTag.D4 K₃ Fr.toRingHom) := by
      have h1 : (MulAut.conj z')⁻¹ * (MulAut.conj z' * δ₀) = δ₀ := inv_mul_cancel_left _ _
      rw [← h1]
      exact mul_mem (inv_mem ⟨z', rfl⟩) hin
    exact D4Three.fieldActor_not_inner hℓ hf hK₃ Fr hFr hinn
  have h27 := D4Three.twentySeven_dvd_fixedSubgroup_graphFixed hℓ hf hK₃ Fr hFr
    (MulAut.conj z' * δ₀) hαhat3 hout
  have hYle : graphFixedRootGroup TwistTag.D4 K₃ Fr.toRingHom ≤ adjointGroup TwistTag.D4.tag K₃ :=
    (graphFixedRootGroup_le TwistTag.D4 K₃ Fr.toRingHom).trans inf_le_left
  let incl : ↥(graphFixedRootGroup TwistTag.D4 K₃ Fr.toRingHom) →*
      ↥(adjointGroup TwistTag.D4.tag K₃) := Subgroup.inclusion hYle
  let Ψ : ↥(fixedSubgroup (MulAut.conj z' * δ₀)) →* ↥(adjointGroup TwistTag.D4.tag K₃) :=
    (ψ⁻¹).toMonoidHom.comp (incl.comp (Subgroup.subtype _))
  have hΨinj : Function.Injective Ψ := fun a b hab =>
    Subtype.ext (Subgroup.inclusion_injective hYle ((ψ⁻¹).injective hab))
  let ι₃G : ↥(adjointGroup TwistTag.D4.tag K) →* ↥(adjointGroup TwistTag.D4.tag K₃) :=
    ((baseChangeGL (algebraMap K K₃)).comp (adjointGroup TwistTag.D4.tag K).subtype).codRestrict
      (adjointGroup TwistTag.D4.tag K₃) fun u => baseChangeGL_mem_adjointGroup _ u.2
  have hι₃G : ∀ u, (ι₃G u : ModGL TwistTag.D4.tag K₃) =
      baseChangeGL (algebraMap K K₃) (u : ModGL TwistTag.D4.tag K) := fun _ => rfl
  have hι₃Ginj : Function.Injective ι₃G := fun a b hab =>
    Subtype.ext (baseChangeGL_injective (algebraMap K K₃) (by rw [← hι₃G, ← hι₃G, hab]))
  have hFK : ∀ w : ModGL TwistTag.D4.tag K, Units.map (entrywiseHom Fr.toRingHom)
      (baseChangeGL (algebraMap K K₃) w) = baseChangeGL (algebraMap K K₃) w := fun w => by
    rw [units_map_entrywiseHom_eq_baseChangeGL, baseChangeGL_baseChangeGL]
    have : Fr.toRingHom.comp (algebraMap K K₃) = algebraMap K K₃ :=
      RingHom.ext (graphType_frobenius_algebraMap hK Fr hFr)
    rw [this]
  have hcompat : ∀ u, β (ι₃G u) = ι₃G (α u) := fun u => by
    refine Subtype.ext (baseChangeGL_injective (algebraMap K₃ L) ?_)
    calc baseChangeGL (algebraMap K₃ L) ((β (ι₃G u) : ↥(adjointGroup TwistTag.D4.tag K₃)) :
          ModGL TwistTag.D4.tag K₃) =
        (x * diagramMap TwistTag.D4 L) * Units.map (entrywiseHom FrL)
          (baseChangeGL (algebraMap K₃ L) ((ι₃G u : ↥(adjointGroup TwistTag.D4.tag K₃)) :
            ModGL TwistTag.D4.tag K₃)) * (x * diagramMap TwistTag.D4 L)⁻¹ := hstep _
      _ = (x * diagramMap TwistTag.D4 L) * baseChangeGL ((algebraMap K₃ L).comp (algebraMap K K₃))
          (u : ModGL TwistTag.D4.tag K) * (x * diagramMap TwistTag.D4 L)⁻¹ := by
        rw [hι₃G, hFι, hFK, baseChangeGL_baseChangeGL]
      _ = baseChangeGL (algebraMap K₃ L) ((ι₃G (α u) : ↥(adjointGroup TwistTag.D4.tag K₃)) :
          ModGL TwistTag.D4.tag K₃) := by
        rw [hι₃G, baseChangeGL_baseChangeGL, hα]
        group
  have hrange : ∀ c : ↥(fixedSubgroup (MulAut.conj z' * δ₀)), ∃ u : ↥(fixedSubgroup α),
      ι₃G u = Ψ c := by
    rintro ⟨c, hc⟩
    have hcfix : (MulAut.conj z' * δ₀) c = c := hc
    have hcm : z₀ * Units.map (entrywiseHom Fr.toRingHom) (c : ModGL TwistTag.D4.tag K₃) * z₀⁻¹ =
        (c : ModGL TwistTag.D4.tag K₃) := by
      have := congrArg Subtype.val hcfix
      rw [MulAut.mul_apply, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_mul,
        Subgroup.coe_inv, hδcoe] at this
      exact this
    have hcL : ((h : ModGL TwistTag.D4.tag L) * (Units.map (entrywiseHom FrL)
        (h : ModGL TwistTag.D4.tag L))⁻¹) * Units.map (entrywiseHom FrL)
          (baseChangeGL (algebraMap K₃ L) (c : ModGL TwistTag.D4.tag K₃)) *
        ((h : ModGL TwistTag.D4.tag L) * (Units.map (entrywiseHom FrL)
          (h : ModGL TwistTag.D4.tag L))⁻¹)⁻¹ =
        baseChangeGL (algebraMap K₃ L) (c : ModGL TwistTag.D4.tag K₃) := by
      have := congrArg (baseChangeGL (algebraMap K₃ L)) hcm
      rw [map_mul, map_mul, map_inv, hz₀eq, ← hFι] at this
      exact this
    obtain ⟨u₃, hu₃⟩ : ∃ u₃ : ↥(adjointGroup TwistTag.D4.tag K₃), u₃ = ψ⁻¹ (incl c) := ⟨_, rfl⟩
    have hψu : ψ u₃ = incl c := by rw [hu₃, MulAut.apply_inv_self]
    have hα₀c : twistedEntrywiseAut TwistTag.D4 1 Fr (incl c) = incl c := by
      refine Subtype.ext ?_
      have hmem := (graphFixedRootGroup_le TwistTag.D4 K₃ Fr.toRingHom) c.2
      have htw := ((mem_twistedFixedGroup_iff_twistHom TwistTag.D4 K₃ Fr.toRingHom).1 hmem).2
      rw [coe_twistedEntrywiseAut, zpow_one]
      rw [twistHom_apply] at htw
      exact htw
    have hψc : baseChangeGL (algebraMap K₃ L) (c : ModGL TwistTag.D4.tag K₃) =
        (h : ModGL TwistTag.D4.tag L) * baseChangeGL (algebraMap K₃ L)
          (u₃ : ModGL TwistTag.D4.tag K₃) * (h : ModGL TwistTag.D4.tag L)⁻¹ := by
      have := hψι u₃
      rw [hψu] at this
      exact this
    have hFu : Units.map (entrywiseHom FrL) (baseChangeGL (algebraMap K₃ L)
        (u₃ : ModGL TwistTag.D4.tag K₃)) = baseChangeGL (algebraMap K₃ L)
          (u₃ : ModGL TwistTag.D4.tag K₃) := by
      have hu : baseChangeGL (algebraMap K₃ L) (u₃ : ModGL TwistTag.D4.tag K₃) =
          (h : ModGL TwistTag.D4.tag L)⁻¹ * baseChangeGL (algebraMap K₃ L)
            (c : ModGL TwistTag.D4.tag K₃) * (h : ModGL TwistTag.D4.tag L) := by
        rw [hψc]; group
      have hFc : Units.map (entrywiseHom FrL) (baseChangeGL (algebraMap K₃ L)
          (c : ModGL TwistTag.D4.tag K₃)) =
          (Units.map (entrywiseHom FrL) (h : ModGL TwistTag.D4.tag L) *
            (h : ModGL TwistTag.D4.tag L)⁻¹) * baseChangeGL (algebraMap K₃ L)
              (c : ModGL TwistTag.D4.tag K₃) * ((h : ModGL TwistTag.D4.tag L) *
                (Units.map (entrywiseHom FrL) (h : ModGL TwistTag.D4.tag L))⁻¹) := by
        calc _ = ((h : ModGL TwistTag.D4.tag L) * (Units.map (entrywiseHom FrL)
              (h : ModGL TwistTag.D4.tag L))⁻¹)⁻¹ * (((h : ModGL TwistTag.D4.tag L) *
                (Units.map (entrywiseHom FrL) (h : ModGL TwistTag.D4.tag L))⁻¹) *
                  Units.map (entrywiseHom FrL) (baseChangeGL (algebraMap K₃ L)
                    (c : ModGL TwistTag.D4.tag K₃)) * ((h : ModGL TwistTag.D4.tag L) *
                      (Units.map (entrywiseHom FrL) (h : ModGL TwistTag.D4.tag L))⁻¹)⁻¹) *
                ((h : ModGL TwistTag.D4.tag L) * (Units.map (entrywiseHom FrL)
                  (h : ModGL TwistTag.D4.tag L))⁻¹) := by group
          _ = _ := by rw [hcL]; group
      rw [hu, map_mul, map_mul, map_inv, hFc]
      group
    have hΦu : Units.map (entrywiseHom Fr.toRingHom) (u₃ : ModGL TwistTag.D4.tag K₃) = u₃ := by
      apply baseChangeGL_injective (algebraMap K₃ L)
      rw [← hFι]
      exact hFu
    have hmemfix : (u₃ : ModGL TwistTag.D4.tag K₃) ∈ entrywiseFixedGroup TwistTag.D4.tag Fr :=
      ⟨u₃.2, hΦu⟩
    rw [CFSG.GH74.GLS.Stage2.Bender.Thm1.entrywiseFixedGroup_D4_eq_fixedFieldImage_of_cube Fr
      hFr3] at hmemfix
    obtain ⟨v, hv, hvu⟩ := hmemfix
    let e := graphTypeFixedEquiv hf hK hK₃ Fr hFr
    have hecomp : (algebraMap K K₃).comp e.symm.toRingHom = (fixSubfield Fr).subtype :=
      RingHom.ext fun y => by
        have := graphTypeFixedEquiv_apply hf hK hK₃ Fr hFr (e.symm y)
        rw [RingEquiv.apply_symm_apply] at this
        exact this.symm
    have huKad : baseChangeGL e.symm.toRingHom v ∈ adjointGroup TwistTag.D4.tag K :=
      baseChangeGL_mem_adjointGroup _ hv
    set u : ↥(adjointGroup TwistTag.D4.tag K) := ⟨baseChangeGL e.symm.toRingHom v, huKad⟩ with hudef
    have hu : ι₃G u = u₃ := by
      refine Subtype.ext ?_
      rw [hι₃G]
      change baseChangeGL (algebraMap K K₃) (baseChangeGL e.symm.toRingHom v) = _
      rw [baseChangeGL_baseChangeGL, hecomp]
      exact hvu
    have hβu : β u₃ = u₃ := by
      have h1 := hcomm u₃
      rw [hψu, hα₀c] at h1
      refine ψ.injective ?_
      rw [← h1, hψu]
    have hαu : α u = u := by
      refine hι₃Ginj ?_
      calc ι₃G (α u) = β (ι₃G u) := (hcompat u).symm
        _ = β u₃ := by rw [hu]
        _ = u₃ := hβu
        _ = ι₃G u := hu.symm
    exact ⟨⟨u, hαu⟩, hu.trans hu₃⟩
  have hle : Ψ.range ≤ (fixedSubgroup α).map ι₃G := by
    rintro _ ⟨c, rfl⟩
    obtain ⟨u, hu⟩ := hrange c
    exact ⟨u, u.2, hu⟩
  have hcard : Nat.card ↥(fixedSubgroup (MulAut.conj z' * δ₀)) ∣ Nat.card ↥(fixedSubgroup α) := by
    calc Nat.card ↥(fixedSubgroup (MulAut.conj z' * δ₀)) = Nat.card Ψ.range :=
          Nat.card_congr (MonoidHom.ofInjective hΨinj).toEquiv
      _ ∣ Nat.card ↥((fixedSubgroup α).map ι₃G) := Subgroup.card_dvd_of_le hle
      _ = Nat.card ↥(fixedSubgroup α) := Subgroup.card_map_of_injective hι₃Ginj
  exact h27.trans hcard

end Core

end CFSG.HardMathSupport.Lang.E6Descent
