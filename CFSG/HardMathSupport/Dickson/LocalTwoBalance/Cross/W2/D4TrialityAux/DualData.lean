module

public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.D4Graph.Duality

public noncomputable section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Lang.D4Three CFSG.GroupTheory
open CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
  CFSG.HardMathSupport.Lang.E6Descent CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.D4Dual
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

section DualData


theorem graphFixedRootGroup_le_adjoint (K : Type) [Field K] (σ : K →+* K) :
    graphFixedRootGroup TwistTag.D4 K σ ≤ adjointGroup TwistTag.D4.tag K :=
  (graphFixedRootGroup_le TwistTag.D4 K σ).trans inf_le_left

@[expose] def graphFixedInclusion (K : Type) [Field K] (σ : K ≃+* K) :
    ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom) →* ↥(adjointGroup Tag.D4 K) :=
  Subgroup.inclusion (graphFixedRootGroup_le_adjoint K σ.toRingHom)

@[expose] def baseChangeAdj {K K₃ : Type} [Field K] [Field K₃] (ι : K →+* K₃) :
    ↥(adjointGroup Tag.D4 K) →* ↥(adjointGroup Tag.D4 K₃) :=
  ((baseChangeGL ι).comp (adjointGroup Tag.D4 K).subtype).codRestrict
    (adjointGroup Tag.D4 K₃) fun u => baseChangeGL_mem_adjointGroup _ u.2

theorem dual_data_ambient {ℓ f : ℕ} [Fact ℓ.Prime] (hf : 1 ≤ f)
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
    ∃ (ψ : MulAut ↥(adjointGroup TwistTag.D4.tag K₃))
      (φ : MulAut ↥(graphFixedRootGroup TwistTag.D4 K₃ Fr.toRingHom)),
      ψ * β * ψ⁻¹ = twistedEntrywiseAut TwistTag.D4 1 Fr ∧ φ ^ 3 = 1 ∧
      φ ∉ (MulAut.conj : ↥(graphFixedRootGroup TwistTag.D4 K₃ Fr.toRingHom) →*
        MulAut ↥(graphFixedRootGroup TwistTag.D4 K₃ Fr.toRingHom)).range ∧
      (∀ y : ↥(graphFixedRootGroup TwistTag.D4 K₃ Fr.toRingHom),
        ψ (entrywiseAdjointAut TwistTag.D4.tag Fr (ψ⁻¹ (graphFixedInclusion K₃ Fr y))) =
          graphFixedInclusion K₃ Fr (φ y)) ∧
      (∀ u : ↥(fixSubgroup α), ∃ y : ↥(graphFixedRootGroup TwistTag.D4 K₃ Fr.toRingHom),
        graphFixedInclusion K₃ Fr y = ψ (baseChangeAdj (algebraMap K K₃) u.1) ∧ φ y = y) ∧
      (∀ y : ↥(graphFixedRootGroup TwistTag.D4 K₃ Fr.toRingHom), φ y = y →
        ∃ u : ↥(fixSubgroup α),
          graphFixedInclusion K₃ Fr y = ψ (baseChangeAdj (algebraMap K K₃) u.1)) ∧
      (∀ y : ↥(graphFixedRootGroup TwistTag.D4 K₃ Fr.toRingHom),
        twistedEntrywiseAut TwistTag.D4 1 Fr (graphFixedInclusion K₃ Fr y) =
          graphFixedInclusion K₃ Fr y) ∧
      (∀ w : ↥(adjointGroup TwistTag.D4.tag K₃), twistedEntrywiseAut TwistTag.D4 1 Fr w = w →
        ∃ y : ↥(graphFixedRootGroup TwistTag.D4 K₃ Fr.toRingHom),
          graphFixedInclusion K₃ Fr y = w) := by
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
      baseChangeGL (algebraMap K₃ L)
          (twistedEntrywiseAut TwistTag.D4 1 Fr w : ModGL TwistTag.D4.tag K₃) =
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
  have hδ3 : δ₀ ^ 3 = 1 := fieldActor_cube (sigma_cube hK₃ Fr hFr)
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
  have hout : (MulAut.conj z' * δ₀) ∉ CFSG.ComponentClassification.OuterAutomorphisms.inner
      ↥(graphFixedRootGroup TwistTag.D4 K₃ Fr.toRingHom) := by
    intro hin
    have hinn : δ₀ ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner
        ↥(graphFixedRootGroup TwistTag.D4 K₃ Fr.toRingHom) := by
      have h1 : (MulAut.conj z')⁻¹ * (MulAut.conj z' * δ₀) = δ₀ := inv_mul_cancel_left _ _
      rw [← h1]
      exact mul_mem (inv_mem ⟨z', rfl⟩) hin
    exact fieldActor_not_inner hℓ hf hK₃ Fr hFr hinn
  have hYle : graphFixedRootGroup TwistTag.D4 K₃ Fr.toRingHom ≤ adjointGroup TwistTag.D4.tag K₃ :=
    (graphFixedRootGroup_le TwistTag.D4 K₃ Fr.toRingHom).trans inf_le_left
  let incl : ↥(graphFixedRootGroup TwistTag.D4 K₃ Fr.toRingHom) →*
      ↥(adjointGroup TwistTag.D4.tag K₃) := Subgroup.inclusion hYle
  let ι₃G : ↥(adjointGroup TwistTag.D4.tag K) →* ↥(adjointGroup TwistTag.D4.tag K₃) :=
    baseChangeAdj (algebraMap K K₃)
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
  have htw : twistedFixedGroup TwistTag.D4 K₃ Fr.toRingHom =
      graphFixedRootGroup TwistTag.D4 K₃ Fr.toRingHom :=
    (triality_both_field_orientations_simple_full_ambient_fixed_group (ℓ := ℓ) (d := f) hℓ hf K₃
      hK₃ L 1 (Or.inl rfl) Fr.toRingHom (fun c => by simpa using hFr c) FrL hFrL').2.2.1
  have hΘY : ∀ u : ↥(fixSubgroup α),
      ((ψ (ι₃G u.1) : ↥(adjointGroup TwistTag.D4.tag K₃)) : ModGL TwistTag.D4.tag K₃) ∈
        graphFixedRootGroup TwistTag.D4 K₃ Fr.toRingHom := by
    intro u
    have hu : α u.1 = u.1 := u.2
    have hβu : β (ι₃G u.1) = ι₃G u.1 := by rw [hcompat, hu]
    have h1 := hcomm (ι₃G u.1)
    rw [hβu] at h1
    rw [← htw, mem_twistedFixedGroup_iff_twistHom]
    refine ⟨(ψ (ι₃G u.1)).2, ?_⟩
    have h2 := congrArg Subtype.val h1
    rw [coe_twistedEntrywiseAut, zpow_one] at h2
    rw [twistHom_apply]
    exact h2
  have hrange : ∀ c : ↥(fixSubgroup (MulAut.conj z' * δ₀)), ∃ u : ↥(fixSubgroup α),
      ι₃G u = ψ⁻¹ (incl c.1) := by
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
  have hΘfix : ∀ u : ↥(fixSubgroup α),
      (MulAut.conj z' * δ₀) ⟨((ψ (ι₃G u.1) : ↥(adjointGroup TwistTag.D4.tag K₃)) :
        ModGL TwistTag.D4.tag K₃), hΘY u⟩ =
      ⟨((ψ (ι₃G u.1) : ↥(adjointGroup TwistTag.D4.tag K₃)) : ModGL TwistTag.D4.tag K₃),
        hΘY u⟩ := by
    intro u
    apply Subtype.ext
    apply baseChangeGL_injective (algebraMap K₃ L)
    have hwF : Units.map (entrywiseHom Fr.toRingHom)
        ((ι₃G u.1 : ↥(adjointGroup TwistTag.D4.tag K₃)) : ModGL TwistTag.D4.tag K₃) =
        ((ι₃G u.1 : ↥(adjointGroup TwistTag.D4.tag K₃)) : ModGL TwistTag.D4.tag K₃) := by
      rw [hι₃G, hFK]
    have hBwF : Units.map (entrywiseHom FrL) (baseChangeGL (algebraMap K₃ L)
        ((ι₃G u.1 : ↥(adjointGroup TwistTag.D4.tag K₃)) : ModGL TwistTag.D4.tag K₃)) =
        baseChangeGL (algebraMap K₃ L)
          ((ι₃G u.1 : ↥(adjointGroup TwistTag.D4.tag K₃)) : ModGL TwistTag.D4.tag K₃) := by
      rw [hFι, hwF]
    have hψc := hψι (ι₃G u.1)
    rw [MulAut.mul_apply, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_mul,
      Subgroup.coe_inv, hδcoe]
    change baseChangeGL (algebraMap K₃ L) (z₀ * Units.map (entrywiseHom Fr.toRingHom)
        ((ψ (ι₃G u.1) : ↥(adjointGroup TwistTag.D4.tag K₃)) : ModGL TwistTag.D4.tag K₃) * z₀⁻¹) =
      baseChangeGL (algebraMap K₃ L)
        ((ψ (ι₃G u.1) : ↥(adjointGroup TwistTag.D4.tag K₃)) : ModGL TwistTag.D4.tag K₃)
    rw [map_mul, map_mul, map_inv, hz₀eq, ← hFι, hψc]
    simp only [map_mul, map_inv, hBwF]
    group
  refine ⟨ψ, MulAut.conj z' * δ₀, hψβ, hαhat3, hout, ?_, ?_, ?_, ?_, ?_⟩
  ·
    intro y
    have hgoal : ψ (entrywiseAdjointAut TwistTag.D4.tag Fr (ψ⁻¹ (incl y))) =
        incl ((MulAut.conj z' * δ₀) y) := by
      refine Subtype.ext (baseChangeGL_injective (algebraMap K₃ L) ?_)
      have hw := hψι (ψ⁻¹ (incl y))
      rw [MulAut.apply_inv_self] at hw
      have hTw := hψι (entrywiseAdjointAut TwistTag.D4.tag Fr (ψ⁻¹ (incl y)))
      have hTc : baseChangeGL (algebraMap K₃ L)
          ((entrywiseAdjointAut TwistTag.D4.tag Fr (ψ⁻¹ (incl y)) :
            ↥(adjointGroup TwistTag.D4.tag K₃)) : ModGL TwistTag.D4.tag K₃) =
          Units.map (entrywiseHom FrL) (baseChangeGL (algebraMap K₃ L)
            ((ψ⁻¹ (incl y) : ↥(adjointGroup TwistTag.D4.tag K₃)) : ModGL TwistTag.D4.tag K₃)) := by
        rw [coe_entrywiseAdjointAut, hFι]
      have hbw : baseChangeGL (algebraMap K₃ L)
          ((ψ⁻¹ (incl y) : ↥(adjointGroup TwistTag.D4.tag K₃)) : ModGL TwistTag.D4.tag K₃) =
          (h : ModGL TwistTag.D4.tag L)⁻¹ * baseChangeGL (algebraMap K₃ L)
            ((incl y : ↥(adjointGroup TwistTag.D4.tag K₃)) : ModGL TwistTag.D4.tag K₃) *
              (h : ModGL TwistTag.D4.tag L) := by
        rw [hw]; group
      rw [hTw, hTc, hbw]
      change _ = baseChangeGL (algebraMap K₃ L) (z₀ * Units.map (entrywiseHom Fr.toRingHom)
        ((incl y : ↥(adjointGroup TwistTag.D4.tag K₃)) : ModGL TwistTag.D4.tag K₃) * z₀⁻¹)
      simp only [map_mul, map_inv]
      rw [hz₀eq, ← hFι]
      group
    exact hgoal
  · intro u
    exact ⟨⟨_, hΘY u⟩, rfl, hΘfix u⟩
  · intro y hy
    obtain ⟨u, hu⟩ := hrange ⟨y, hy⟩
    have hu' : baseChangeAdj (algebraMap K K₃) u.1 = ψ⁻¹ (incl y) := hu
    exact ⟨u, by rw [hu', MulAut.apply_inv_self]; rfl⟩
  · intro y
    have hmem := (graphFixedRootGroup_le TwistTag.D4 K₃ Fr.toRingHom) y.2
    have htw' := ((mem_twistedFixedGroup_iff_twistHom TwistTag.D4 K₃ Fr.toRingHom).1 hmem).2
    refine Subtype.ext ?_
    change ((twistedEntrywiseAut TwistTag.D4 1 Fr (incl y) : ↥(adjointGroup TwistTag.D4.tag K₃)) :
      ModGL TwistTag.D4.tag K₃) = _
    rw [coe_twistedEntrywiseAut, zpow_one]
    rw [twistHom_apply] at htw'
    exact htw'
  · intro w hw
    have hmem : (w : ModGL TwistTag.D4.tag K₃) ∈ graphFixedRootGroup TwistTag.D4 K₃ Fr.toRingHom := by
      rw [← htw, mem_twistedFixedGroup_iff_twistHom]
      refine ⟨w.2, ?_⟩
      have h2 := congrArg Subtype.val hw
      rw [coe_twistedEntrywiseAut, zpow_one] at h2
      rw [twistHom_apply]
      exact h2
    exact ⟨⟨_, hmem⟩, rfl⟩


theorem dual_data_one {ℓ f : ℕ} [Fact ℓ.Prime] (hf : 1 ≤ f)
    (K : Type) [Field K] [Finite K] (hK : Nat.card K = ℓ ^ f)
    (α : MulAut (adjointGroup Tag.D4 K)) (hα3 : α ^ 3 = 1) (g : adjointGroup Tag.D4 K)
    (a : Fin Tag.D4.rank → Kˣ)
    (hα : α = MulAut.conj g * (exactNormalAut Tag.D4 K a 1 0 * d4Graph K 1)) :
    ∃ (K₃ : Type) (_ : Field K₃) (_ : Finite K₃) (_ : Algebra K K₃) (Fr : K₃ ≃+* K₃),
      Nat.card K₃ = (ℓ ^ f) ^ 3 ∧ (∀ c, Fr c = c ^ (ℓ ^ f)) ∧
      ∃ (ψ : MulAut ↥(adjointGroup Tag.D4 K₃))
        (φ : MulAut ↥(graphFixedRootGroup TwistTag.D4 K₃ Fr.toRingHom)),
        ψ * (MulAut.conj (baseChangeAdj (algebraMap K K₃) g) *
          (exactNormalAut Tag.D4 K₃ (fun i => Units.map (algebraMap K K₃).toMonoidHom (a i)) Fr 0 *
            d4Graph K₃ 1)) * ψ⁻¹ = twistedEntrywiseAut TwistTag.D4 1 Fr ∧ φ ^ 3 = 1 ∧
        φ ∉ (MulAut.conj : ↥(graphFixedRootGroup TwistTag.D4 K₃ Fr.toRingHom) →*
          MulAut ↥(graphFixedRootGroup TwistTag.D4 K₃ Fr.toRingHom)).range ∧
        (∀ y : ↥(graphFixedRootGroup TwistTag.D4 K₃ Fr.toRingHom),
          ψ (entrywiseAdjointAut TwistTag.D4.tag Fr (ψ⁻¹ (graphFixedInclusion K₃ Fr y))) =
            graphFixedInclusion K₃ Fr (φ y)) ∧
        (∀ u : ↥(fixSubgroup α), ∃ y : ↥(graphFixedRootGroup TwistTag.D4 K₃ Fr.toRingHom),
          graphFixedInclusion K₃ Fr y = ψ (baseChangeAdj (algebraMap K K₃) u.1) ∧ φ y = y) ∧
        (∀ y : ↥(graphFixedRootGroup TwistTag.D4 K₃ Fr.toRingHom), φ y = y →
          ∃ u : ↥(fixSubgroup α),
            graphFixedInclusion K₃ Fr y = ψ (baseChangeAdj (algebraMap K K₃) u.1)) ∧
        (∀ y : ↥(graphFixedRootGroup TwistTag.D4 K₃ Fr.toRingHom),
          twistedEntrywiseAut TwistTag.D4 1 Fr (graphFixedInclusion K₃ Fr y) =
            graphFixedInclusion K₃ Fr y) ∧
        (∀ w : ↥(adjointGroup Tag.D4 K₃), twistedEntrywiseAut TwistTag.D4 1 Fr w = w →
          ∃ y : ↥(graphFixedRootGroup TwistTag.D4 K₃ Fr.toRingHom),
            graphFixedInclusion K₃ Fr y = w) := by
  classical
  have hℓ : ℓ.Prime := Fact.out
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨K₃, _, _, _, _, hK₃, Fr, hFr⟩ := graphType_exists_ext hf K hK
  set L := AlgebraicClosure K₃ with hL
  have : CharP L ℓ := charP_of_injective_algebraMap (algebraMap K₃ L).injective ℓ
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K₃
  set ιK : K →+* K₃ := algebraMap K K₃ with hιK
  set ιL : K₃ →+* L := algebraMap K₃ L with hιL
  set ιLK : K →+* L := ιL.comp ιK with hιLK
  set x : ModGL Tag.D4 L := baseChangeGL ιLK ((g : ModGL Tag.D4 K) * rootDiagUnit Tag.D4 a)
    with hxdef
  have hx : x ∈ adjointGroup Tag.D4 L := by
    rw [hxdef, map_mul, baseChangeGL_rootDiagUnit]
    exact mul_mem (CFSG.LieType.Chevalley.baseChangeGL_mem_adjointGroup _ g.2)
      (exceptional_Lang_adjoint_diagonal_lift Tag.D4 L _).1
  have hFrc : (iterateFrobenius L ℓ f).comp ιLK = ιLK := by
    ext c
    simp only [RingHom.comp_apply, iterateFrobenius_def, hιLK, ← map_pow]
    rw [← hK, Nat.card_eq_fintype_card, FiniteField.pow_card]
  have hxF : Units.map (entrywiseHom (iterateFrobenius L ℓ f)) x = x := by
    rw [hxdef, units_map_entrywiseHom_eq_baseChangeGL, baseChangeGL_baseChangeGL, hFrc]
  have hM : ∀ u : adjointGroup Tag.D4 K, baseChangeGL ιLK (α u : ModGL Tag.D4 K) =
      (x * d4P L ^ 1) * baseChangeGL ιLK (u : ModGL Tag.D4 K) * (x * d4P L ^ 1)⁻¹ := by
    intro u
    have h := graphType_baseChange_normalForm_one ιLK g a 1 u
    rw [← hα] at h
    exact h
  have hαx : ∀ u : adjointGroup Tag.D4 K, baseChangeGL ιLK (α u : ModGL Tag.D4 K) =
      x * (d4P L * baseChangeGL ιLK (u : ModGL Tag.D4 K) * (d4P L)⁻¹) * x⁻¹ := by
    intro u
    rw [hM u, pow_one]
    group
  have hxP : (x * d4P L) ^ 3 = 1 := by
    have := graphType_cube_eq_one ιLK α hα3 g a 1 hx hM
    rwa [pow_one] at this
  set g₃ : adjointGroup Tag.D4 K₃ := ⟨baseChangeGL ιK (g : ModGL Tag.D4 K),
    CFSG.LieType.Chevalley.baseChangeGL_mem_adjointGroup _ g.2⟩ with hg₃
  set a₃ : Fin Tag.D4.rank → K₃ˣ := fun i => Units.map ιK.toMonoidHom (a i) with ha₃
  have hx3' : (g₃ : ModGL Tag.D4 K₃) * rootDiagUnit Tag.D4 a₃ =
      baseChangeGL ιK ((g : ModGL Tag.D4 K) * rootDiagUnit Tag.D4 a) := by
    rw [map_mul, baseChangeGL_rootDiagUnit]
  have hx3 : baseChangeGL ιL ((g₃ : ModGL Tag.D4 K₃) * rootDiagUnit Tag.D4 a₃) = x := by
    rw [hx3', hxdef, baseChangeGL_baseChangeGL]
  obtain ⟨ψ, φ, hψβ, hφ⟩ := dual_data_ambient hf K hK K₃ hK₃ Fr hFr L x hx hxF hxP
      (MulAut.conj g₃ * (exactNormalAut Tag.D4 K₃ a₃ Fr 0 * d4Graph K₃ 1))
      (fun u => by
        have h := graphType_baseChange_normalForm L ιL g₃ a₃ Fr 1 u
        rw [hx3] at h
        exact h)
      α hαx
  exact ⟨K₃, inferInstance, inferInstance, inferInstance, Fr, hK₃, hFr, ψ, φ, hψβ, hφ⟩

end DualData

end CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross
