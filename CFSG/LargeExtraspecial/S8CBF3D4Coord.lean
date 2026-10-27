module

public import CFSG.LargeExtraspecial.S8CBF3D4Param

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S8

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Chevalley.TrialityFieldTwo CFSG.LieType.Chevalley.ExceptionalCover
open scoped commutatorElement

theorem mem_one_of_mem_middle
    {K : Type} [Field K] (σ : K ≃+* K) {g : ModGL TwistTag.D4.tag K}
    (hg : g ∈ graphFixedParabolicRadical TwistTag.D4 K σ.toRingHom
      {(⟨1, by decide⟩ : Fin TwistTag.D4.foldedTag.rank)}) :
    g ∈ heightSeries TwistTag.D4.tag K 1 := by
  rw [heightSeries_one]
  exact (graphFixedParabolicRadical_le TwistTag.D4 K σ.toRingHom _ hg).1

theorem x₁_add
    {K : Type} [Field K] (σ : K ≃+* K) (a a' : K) :
    (trialityX₁ K σ.toRingHom (a + a') : ModGL TwistTag.D4.tag K) =
      (trialityX₁ K σ.toRingHom a : ModGL TwistTag.D4.tag K) * trialityX₁ K σ.toRingHom a' := by
  rw [trialityX₁, trialityOrbitProd_add' (Or.inl rfl), Subgroup.coe_mul]
  rfl

theorem exists_middle_form {K : Type} [Field K] (μ : K) :
    ∃ β : (Fin 6 → K) →ₗ[K] (Fin 6 → K) →ₗ[K] K,
      ∀ v w, β v w = μ⁻¹ * (v 1 * w 5 + v 2 * w 4 + w 1 * v 5 + w 2 * v 4) :=
  ⟨LinearMap.mk₂ K (fun v w => μ⁻¹ * (v 1 * w 5 + v 2 * w 4 + w 1 * v 5 + w 2 * v 4))
    (fun _ _ _ => by simp only [Pi.add_apply]; ring)
    (fun _ _ _ => by simp only [Pi.smul_apply, smul_eq_mul]; ring)
    (fun _ _ _ => by simp only [Pi.add_apply]; ring)
    (fun _ _ _ => by simp only [Pi.smul_apply, smul_eq_mul]; ring), fun _ _ => rfl⟩

section Middle


variable {K : Type} [Field K] [Finite K] [CharP K 2] (σ : K ≃+* K) (hσ : σ ^ 3 = 1)
include hσ

theorem decomp_middle {g : ModGL TwistTag.D4.tag K}
    (hg : g ∈ graphFixedParabolicRadical TwistTag.D4 K σ.toRingHom
      {(⟨1, by decide⟩ : Fin TwistTag.D4.foldedTag.rank)}) :
    (trialityX₁ K σ.toRingHom (rootCoord (trialityRoot_pos 0) g) : ModGL TwistTag.D4.tag K)⁻¹ *
        g ∈ heightSeries TwistTag.D4.tag K 2 ∧
      (trialityX₃ K σ.toRingHom (rootCoord (trialityRoot_pos 2)
        ((trialityX₁ K σ.toRingHom (rootCoord (trialityRoot_pos 0) g) :
          ModGL TwistTag.D4.tag K)⁻¹ * g)) : ModGL TwistTag.D4.tag K)⁻¹ *
        ((trialityX₁ K σ.toRingHom (rootCoord (trialityRoot_pos 0) g) :
          ModGL TwistTag.D4.tag K)⁻¹ * g) ∈
        heightSeries TwistTag.D4.tag K 3 ⊓ twistedFixedGroup TwistTag.D4 K σ.toRingHom := by
  obtain ⟨a, c, d, e, f, rfl⟩ := exists_param_of_mem_middle σ hσ hg
  rw [(rootCoord_paramProd σ.toRingHom a 0 c d e f).1]
  have e1 : (trialityX₁ K σ.toRingHom a : ModGL TwistTag.D4.tag K)⁻¹ *
      paramProd σ.toRingHom a 0 c d e f =
      (trialityX₃ K σ.toRingHom c : ModGL TwistTag.D4.tag K) *
        (trialityX₄ K σ.toRingHom d : ModGL TwistTag.D4.tag K) *
          (trialityX₅ K σ.toRingHom e : ModGL TwistTag.D4.tag K) *
            (trialityX₆ K σ.toRingHom f : ModGL TwistTag.D4.tag K) := by
    rw [paramProd, x₂_zero, mul_one, inv_mul_cancel_left]
  rw [e1, rootCoord_tail_three]
  refine ⟨tail_mem σ.toRingHom c d e f, ?_⟩
  have e2 : (trialityX₃ K σ.toRingHom c : ModGL TwistTag.D4.tag K)⁻¹ *
      ((trialityX₃ K σ.toRingHom c : ModGL TwistTag.D4.tag K) *
        (trialityX₄ K σ.toRingHom d : ModGL TwistTag.D4.tag K) *
          (trialityX₅ K σ.toRingHom e : ModGL TwistTag.D4.tag K) *
            (trialityX₆ K σ.toRingHom f : ModGL TwistTag.D4.tag K)) =
      (trialityX₄ K σ.toRingHom d : ModGL TwistTag.D4.tag K) *
        (trialityX₅ K σ.toRingHom e : ModGL TwistTag.D4.tag K) *
          (trialityX₆ K σ.toRingHom f : ModGL TwistTag.D4.tag K) := by group
  rw [e2]
  refine mem_inf.2 ⟨mul_mem (mul_mem (x₄_mem _ d)
    (heightSeries_le_of_le (show (3 : ℤ) ≤ 4 by norm_num) (x₅_mem _ e)))
    (heightSeries_le_of_le (show (3 : ℤ) ≤ 5 by norm_num) (x₆_mem _ f)), ?_⟩
  obtain ⟨-, -, -, h4, h5, h6⟩ := xs_mem_graphFixedPosUnipotent σ hσ
  exact mul_mem (mul_mem (graphFixedPosUnipotent_le _ _ _ (h4 d))
    (graphFixedPosUnipotent_le _ _ _ (h5 e))) (graphFixedPosUnipotent_le _ _ _ (h6 f))

theorem coordC_mul {g g' : ModGL TwistTag.D4.tag K}
    (hg : g ∈ graphFixedParabolicRadical TwistTag.D4 K σ.toRingHom
      {(⟨1, by decide⟩ : Fin TwistTag.D4.foldedTag.rank)})
    (hg' : g' ∈ graphFixedParabolicRadical TwistTag.D4 K σ.toRingHom
      {(⟨1, by decide⟩ : Fin TwistTag.D4.foldedTag.rank)}) :
    rootCoord (trialityRoot_pos 2) ((trialityX₁ K σ.toRingHom
        (rootCoord (trialityRoot_pos 0) (g * g')) : ModGL TwistTag.D4.tag K)⁻¹ * (g * g')) =
      rootCoord (trialityRoot_pos 2) ((trialityX₁ K σ.toRingHom
        (rootCoord (trialityRoot_pos 0) g) : ModGL TwistTag.D4.tag K)⁻¹ * g) +
      rootCoord (trialityRoot_pos 2) ((trialityX₁ K σ.toRingHom
        (rootCoord (trialityRoot_pos 0) g') : ModGL TwistTag.D4.tag K)⁻¹ * g') := by
  have h0 : height (trialityRoot 0) = 1 := by decide
  have h2 : height (trialityRoot 2) = 2 := by decide
  have m1 := mem_one_of_mem_middle σ hg
  have m1' := mem_one_of_mem_middle σ hg'
  rw [← h0] at m1 m1'
  rw [rootCoord_mul _ m1 m1']
  set a := rootCoord (trialityRoot_pos 0) g
  set a' := rootCoord (trialityRoot_pos 0) g'
  set u := (trialityX₁ K σ.toRingHom a : ModGL TwistTag.D4.tag K) with hu
  set u' := (trialityX₁ K σ.toRingHom a' : ModGL TwistTag.D4.tag K) with hu'
  have ht := (decomp_middle σ hσ hg).1
  have ht' := (decomp_middle σ hσ hg').1
  rw [← h2] at ht ht'
  have e : (trialityX₁ K σ.toRingHom (a + a') : ModGL TwistTag.D4.tag K)⁻¹ * (g * g') =
      u'⁻¹ * (u⁻¹ * g) * u'⁻¹⁻¹ * (u'⁻¹ * g') := by
    rw [x₁_add σ, ← hu, ← hu']
    group
  have hu' : u'⁻¹ ∈ posUnipotent TwistTag.D4.tag K := by
    rw [← heightSeries_one]
    exact inv_mem (x₁_mem _ a')
  have hc : u'⁻¹ * (u⁻¹ * g) * u'⁻¹⁻¹ ∈ heightSeries TwistTag.D4.tag K (height (trialityRoot 2)) :=
    (mem_normalizer_iff.1 (heightSeries_le_normalizer K _ hu') _).1 ht
  rw [e, rootCoord_mul _ hc ht', rootCoord_conj _ hu' ht]

omit [Finite K] [CharP K 2] hσ in
theorem commutator_mem_heightSeries {h k : ℤ} {x y : ModGL TwistTag.D4.tag K}
    (hx : x ∈ heightSeries TwistTag.D4.tag K h) (hy : y ∈ heightSeries TwistTag.D4.tag K k) :
    ⁅x, y⁆ ∈ heightSeries TwistTag.D4.tag K (h + k) :=
  commutator_heightSeries_le K h k (commutator_mem_commutator hx hy)

omit hσ in
theorem rootCoord_three_facts :
    (∀ {h : ℤ}, 4 ≤ h → ∀ {y : ModGL TwistTag.D4.tag K}, y ∈ heightSeries TwistTag.D4.tag K h →
      rootCoord (trialityRoot_pos 3) y = 0) ∧
    (∀ {y : ModGL TwistTag.D4.tag K}, y ∈ heightSeries TwistTag.D4.tag K 3 →
      rootCoord (trialityRoot_pos 3) y⁻¹ = rootCoord (trialityRoot_pos 3) y) := by
  have h3 : height (trialityRoot 3) = 3 := by decide
  refine ⟨fun {h} hh {y} hy => rootCoord_of_mem_succ _
    (heightSeries_le_of_le (by rw [h3]; omega) hy), fun {y} hy => ?_⟩
  have hy' : y ∈ heightSeries TwistTag.D4.tag K (height (trialityRoot 3)) := by rw [h3]; exact hy
  have e := rootCoord_mul (trialityRoot_pos 3) hy' (inv_mem hy')
  rw [mul_inv_cancel, rootCoord_one] at e
  have e' : rootCoord (trialityRoot_pos 3) y⁻¹ = -rootCoord (trialityRoot_pos 3) y := by
    linear_combination -e
  rw [e', CharTwo.neg_eq]

theorem rootCoord_commutator_middle
    {g g' : ModGL TwistTag.D4.tag K}
    (hg : g ∈ graphFixedParabolicRadical TwistTag.D4 K σ.toRingHom
      {(⟨1, by decide⟩ : Fin TwistTag.D4.foldedTag.rank)})
    (hg' : g' ∈ graphFixedParabolicRadical TwistTag.D4 K σ.toRingHom
      {(⟨1, by decide⟩ : Fin TwistTag.D4.foldedTag.rank)}) :
    ⁅g, g'⁆ ∈ heightSeries TwistTag.D4.tag K 3 ∧
      rootCoord (trialityRoot_pos 3) ⁅g, g'⁆ =
        (σ (rootCoord (trialityRoot_pos 0) g) * σ (σ (rootCoord (trialityRoot_pos 2)
          ((trialityX₁ K σ.toRingHom (rootCoord (trialityRoot_pos 0) g') :
            ModGL TwistTag.D4.tag K)⁻¹ * g'))) +
          σ (σ (rootCoord (trialityRoot_pos 0) g)) * σ (rootCoord (trialityRoot_pos 2)
            ((trialityX₁ K σ.toRingHom (rootCoord (trialityRoot_pos 0) g') :
              ModGL TwistTag.D4.tag K)⁻¹ * g'))) +
        (σ (rootCoord (trialityRoot_pos 0) g') * σ (σ (rootCoord (trialityRoot_pos 2)
          ((trialityX₁ K σ.toRingHom (rootCoord (trialityRoot_pos 0) g) :
            ModGL TwistTag.D4.tag K)⁻¹ * g))) +
          σ (σ (rootCoord (trialityRoot_pos 0) g')) * σ (rootCoord (trialityRoot_pos 2)
            ((trialityX₁ K σ.toRingHom (rootCoord (trialityRoot_pos 0) g) :
              ModGL TwistTag.D4.tag K)⁻¹ * g))) := by
  have hσ' := TrialityCover.toRingHom_pow_three σ hσ
  have h3 : height (trialityRoot 3) = 3 := by decide
  set a := rootCoord (trialityRoot_pos 0) g with ha
  set a' := rootCoord (trialityRoot_pos 0) g' with ha'
  set c := rootCoord (trialityRoot_pos 2)
    ((trialityX₁ K σ.toRingHom a : ModGL TwistTag.D4.tag K)⁻¹ * g) with hc
  set c' := rootCoord (trialityRoot_pos 2)
    ((trialityX₁ K σ.toRingHom a' : ModGL TwistTag.D4.tag K)⁻¹ * g') with hc'
  set X₁ := (trialityX₁ K σ.toRingHom a : ModGL TwistTag.D4.tag K) with hX₁
  set X₁' := (trialityX₁ K σ.toRingHom a' : ModGL TwistTag.D4.tag K) with hX₁'
  set X₃ := (trialityX₃ K σ.toRingHom c : ModGL TwistTag.D4.tag K) with hX₃
  set X₃' := (trialityX₃ K σ.toRingHom c' : ModGL TwistTag.D4.tag K) with hX₃'
  set v := X₃⁻¹ * (X₁⁻¹ * g) with hv
  set v' := X₃'⁻¹ * (X₁'⁻¹ * g') with hv'
  have hvm : v ∈ heightSeries TwistTag.D4.tag K 3 := (mem_inf.1 (decomp_middle σ hσ hg).2).1
  have hvm' : v' ∈ heightSeries TwistTag.D4.tag K 3 := (mem_inf.1 (decomp_middle σ hσ hg').2).1
  have hgd : g = [X₁, X₃, v].prod := by
    simp only [List.prod_cons, List.prod_nil, mul_one, hv]
    group
  have hgd' : g' = [X₁', X₃', v'].prod := by
    simp only [List.prod_cons, List.prod_nil, mul_one, hv']
    group
  have m1 := x₁_mem σ.toRingHom a
  have m1' := x₁_mem σ.toRingHom a'
  have m3 := x₃_mem σ.toRingHom c
  have m3' := x₃_mem σ.toRingHom c'
  have hU : ∀ z ∈ [X₁, X₃, v], z ∈ heightSeries TwistTag.D4.tag K 1 := by
    intro z hz
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with rfl | rfl | rfl
    · exact m1
    · exact heightSeries_le_of_le (show (1 : ℤ) ≤ 2 by norm_num) m3
    · exact heightSeries_le_of_le (show (1 : ℤ) ≤ 3 by norm_num) hvm
  have hU' : ∀ z ∈ [X₁', X₃', v'], z ∈ heightSeries TwistTag.D4.tag K 1 := by
    intro z hz
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with rfl | rfl | rfl
    · exact m1'
    · exact heightSeries_le_of_le (show (1 : ℤ) ≤ 2 by norm_num) m3'
    · exact heightSeries_le_of_le (show (1 : ℤ) ≤ 3 by norm_num) hvm'
  have c11 : ⁅X₁, X₁'⁆ = 1 := by
    rw [commutatorElement_eq_one_iff_mul_comm, hX₁, hX₁', ← x₁_add σ, ← x₁_add σ, add_comm]
  set Y := (trialityOrbitProd K σ.toRingHom (trialityRoot 3)
    (σ a * σ (σ c') + σ (σ a) * σ c') : ModGL TwistTag.D4.tag K) with hY
  set Y' := (trialityOrbitProd K σ.toRingHom (trialityRoot 3)
    (σ a' * σ (σ c) + σ (σ a') * σ c) : ModGL TwistTag.D4.tag K) with hY'
  have k12 : Y⁻¹ * ⁅X₁, X₃'⁆ ∈ heightSeries TwistTag.D4.tag K 4 :=
    orbitProd_commutator_mem_four (σ := σ.toRingHom) hσ' a c'
  have k21 : Y'⁻¹ * ⁅X₁', X₃⁆ ∈ heightSeries TwistTag.D4.tag K 4 :=
    orbitProd_commutator_mem_four (σ := σ.toRingHom) hσ' a' c
  have hY3 : Y ∈ heightSeries TwistTag.D4.tag K 3 := x₄_mem σ.toRingHom _
  have hY'3 : Y' ∈ heightSeries TwistTag.D4.tag K 3 := x₄_mem σ.toRingHom _
  have e12 : ⁅X₁, X₃'⁆ = Y * (Y⁻¹ * ⁅X₁, X₃'⁆) := by group
  have e21 : ⁅X₁', X₃⁆ = Y' * (Y'⁻¹ * ⁅X₁', X₃⁆) := by group
  obtain ⟨hz4, hinv⟩ := rootCoord_three_facts (K := K)
  have hY3' : Y ∈ heightSeries TwistTag.D4.tag K (height (trialityRoot 3)) := by
    rw [h3]; exact hY3
  have hY'3' : Y' ∈ heightSeries TwistTag.D4.tag K (height (trialityRoot 3)) := by
    rw [h3]; exact hY'3
  have h4 : ∀ {y : ModGL TwistTag.D4.tag K}, y ∈ heightSeries TwistTag.D4.tag K 4 →
      y ∈ heightSeries TwistTag.D4.tag K (height (trialityRoot 3)) := fun hy => by
    rw [h3]; exact heightSeries_le_of_le (show (3 : ℤ) ≤ 4 by norm_num) hy
  have π12 : rootCoord (trialityRoot_pos 3) ⁅X₁, X₃'⁆ = σ a * σ (σ c') + σ (σ a) * σ c' := by
    rw [e12, rootCoord_mul _ hY3' (h4 k12), hz4 le_rfl k12, add_zero, hY,
      rootCoord_orbitProd σ.toRingHom _ le_rfl, ite_eq_left rfl,
      ite_eq_right (by decide +kernel), ite_eq_right (by decide +kernel), add_zero, add_zero]
  have π21 : rootCoord (trialityRoot_pos 3) ⁅X₃, X₁'⁆ = σ a' * σ (σ c) + σ (σ a') * σ c := by
    rw [← commutatorElement_inv, hinv (by
      have := commutator_mem_heightSeries m1' m3
      norm_num at this
      exact this), e21, rootCoord_mul _ hY'3' (h4 k21), hz4 le_rfl k21, add_zero, hY',
      rootCoord_orbitProd σ.toRingHom _ le_rfl, ite_eq_left rfl,
      ite_eq_right (by decide +kernel), ite_eq_right (by decide +kernel), add_zero, add_zero]
  have hc3 : ∀ {h k : ℤ} {x y : ModGL TwistTag.D4.tag K}, x ∈ heightSeries TwistTag.D4.tag K h →
      y ∈ heightSeries TwistTag.D4.tag K k → 3 ≤ h + k →
        ⁅x, y⁆ ∈ heightSeries TwistTag.D4.tag K 3 :=
    fun hx hy hhk => heightSeries_le_of_le hhk (commutator_mem_heightSeries hx hy)
  have hc4 : ∀ {h k : ℤ} {x y : ModGL TwistTag.D4.tag K}, x ∈ heightSeries TwistTag.D4.tag K h →
      y ∈ heightSeries TwistTag.D4.tag K k → 4 ≤ h + k →
        rootCoord (trialityRoot_pos 3) ⁅x, y⁆ = 0 :=
    fun hx hy hhk => hz4 hhk (commutator_mem_heightSeries hx hy)
  have hmul : ∀ x ∈ heightSeries TwistTag.D4.tag K 3, ∀ y ∈ heightSeries TwistTag.D4.tag K 3,
      rootCoord (trialityRoot_pos 3) (x * y) =
        rootCoord (trialityRoot_pos 3) x + rootCoord (trialityRoot_pos 3) y :=
    fun x hx y hy => rootCoord_mul _ (by rw [h3]; exact hx) (by rw [h3]; exact hy)
  have hconj : ∀ u ∈ posUnipotent TwistTag.D4.tag K, ∀ x ∈ heightSeries TwistTag.D4.tag K 3,
      rootCoord (trialityRoot_pos 3) (u * x * u⁻¹) = rootCoord (trialityRoot_pos 3) x :=
    fun u hu x hx => rootCoord_conj _ hu (by rw [h3]; exact hx)
  have hzw : ∀ z ∈ [X₁, X₃, v], ∀ w ∈ [X₁', X₃', v'],
      ⁅z, w⁆ ∈ heightSeries TwistTag.D4.tag K 3 := by
    intro z hz w hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hz hw
    rcases hz with rfl | rfl | rfl <;> rcases hw with rfl | rfl | rfl
    · rw [c11]
      exact one_mem _
    · exact hc3 m1 m3' (by norm_num)
    · exact hc3 m1 hvm' (by norm_num)
    · exact hc3 m3 m1' (by norm_num)
    · exact hc3 m3 m3' (by norm_num)
    · exact hc3 m3 hvm' (by norm_num)
    · exact hc3 hvm m1' (by norm_num)
    · exact hc3 hvm m3' (by norm_num)
    · exact hc3 hvm hvm' (by norm_num)
  obtain ⟨hmem, hπ⟩ := commutator_prod_mem_and_coord (heightSeries_le_normalizer K 3)
    (rootCoord (trialityRoot_pos 3)) hmul hconj [X₁, X₃, v] [X₁', X₃', v']
    (fun z hz => heightSeries_one (τ := TwistTag.D4.tag) (R := K) ▸ hU z hz)
    (fun z hz => heightSeries_one (τ := TwistTag.D4.tag) (R := K) ▸ hU' z hz) hzw
  rw [← hgd, ← hgd'] at hmem hπ
  refine ⟨hmem, ?_⟩
  rw [hπ]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  rw [c11, rootCoord_one, π12, π21, hc4 m1 hvm' (by norm_num), hc4 m3 m3' (by norm_num),
    hc4 m3 hvm' (by norm_num), hc4 hvm m1' (by norm_num), hc4 hvm m3' (by norm_num),
    hc4 hvm hvm' (by norm_num)]
  ring

theorem card_le_of_middle {s : ModGL TwistTag.D4.tag K}
    (hs3 : s ∈ heightSeries TwistTag.D4.tag K 3) (hs4 : s ∉ heightSeries TwistTag.D4.tag K 4)
    {N : Subgroup (ModGL TwistTag.D4.tag K)}
    (hNQ : N ≤ graphFixedParabolicRadical TwistTag.D4 K σ.toRingHom
      {(⟨1, by decide⟩ : Fin TwistTag.D4.foldedTag.rank)}) (hsN : s ∈ N)
    (hZ : ∀ x ∈ N, (∀ y ∈ N, x * y = y * x) → x = 1 ∨ x = s)
    (hcomm : ∀ x ∈ N, ∀ y ∈ N, ⁅x, y⁆ = 1 ∨ ⁅x, y⁆ = s) : Nat.card N ≤ 2 ^ 7 := by
  classical
  have h0 : height (trialityRoot 0) = 1 := by decide
  have h2 : height (trialityRoot 2) = 2 := by decide
  set A : ModGL TwistTag.D4.tag K → K := fun g => rootCoord (trialityRoot_pos 0) g with hA
  set C : ModGL TwistTag.D4.tag K → K := fun g => rootCoord (trialityRoot_pos 2)
    ((trialityX₁ K σ.toRingHom (A g) : ModGL TwistTag.D4.tag K)⁻¹ * g) with hC
  have hsQ := hNQ hsN
  have hsΓ : s ∈ twistedFixedGroup TwistTag.D4 K σ.toRingHom := (mem_inf.1 hsQ).2
  set μ := rootCoord (trialityRoot_pos 3) s with hμ
  have hμ0 : μ ≠ 0 := by
    intro hμ0
    obtain ⟨d, e, f, hsdef⟩ := exists_param_of_mem_three σ hσ hs3 hsΓ
    have hd := rootCoord_tail_four σ.toRingHom d e f
    rw [← hsdef, ← hμ, hμ0] at hd
    apply hs4
    rw [hsdef, ← hd, trialityX₄, orbitProd_zero, one_mul]
    exact mul_mem (x₅_mem _ e) (heightSeries_le_of_le (show (4 : ℤ) ≤ 5 by norm_num) (x₆_mem _ f))
  have hAC3 : ∀ {g : ModGL TwistTag.D4.tag K}, g ∈ heightSeries TwistTag.D4.tag K 3 →
      A g = 0 ∧ C g = 0 := by
    intro g hg
    have hA0 : A g = 0 := rootCoord_of_mem_succ _
      (heightSeries_le_of_le (show height (trialityRoot 0) + 1 ≤ 3 by rw [h0]; norm_num) hg)
    refine ⟨hA0, ?_⟩
    change rootCoord (trialityRoot_pos 2)
      ((trialityX₁ K σ.toRingHom (A g) : ModGL TwistTag.D4.tag K)⁻¹ * g) = 0
    rw [hA0, trialityX₁, orbitProd_zero, inv_one, one_mul]
    exact rootCoord_of_mem_succ _
      (heightSeries_le_of_le (show height (trialityRoot 2) + 1 ≤ 3 by rw [h2]; norm_num) hg)
  obtain ⟨hAs, hCs⟩ := hAC3 hs3
  have hAmul : ∀ g ∈ N, ∀ h ∈ N, A (g * h) = A g + A h := fun g hg h hh =>
    rootCoord_mul _ (by rw [h0]; exact mem_one_of_mem_middle σ (hNQ hg))
      (by rw [h0]; exact mem_one_of_mem_middle σ (hNQ hh))
  have hCmul : ∀ g ∈ N, ∀ h ∈ N, C (g * h) = C g + C h := fun g hg h hh =>
    coordC_mul σ hσ (hNQ hg) (hNQ hh)
  have hA1 : A 1 = 0 := rootCoord_one _
  have hC1 : C 1 = 0 := by
    change rootCoord (trialityRoot_pos 2)
      ((trialityX₁ K σ.toRingHom (A 1) : ModGL TwistTag.D4.tag K)⁻¹ * 1) = 0
    rw [hA1, trialityX₁, orbitProd_zero, inv_one, one_mul]
    exact rootCoord_one _
  let vec : ModGL TwistTag.D4.tag K → Fin 6 → K := fun g =>
    ![A g, σ (A g), σ (σ (A g)), C g, σ (C g), σ (σ (C g))]
  let Φ : N →* Multiplicative (Fin 6 → K) :=
    { toFun := fun g => Multiplicative.ofAdd (vec g)
      map_one' := by
        change Multiplicative.ofAdd (vec 1) = 1
        rw [← ofAdd_zero]
        congr 1
        funext i
        fin_cases i <;> simp [vec, hA1, hC1]
      map_mul' := fun g h => by
        change Multiplicative.ofAdd (vec ((g : ModGL TwistTag.D4.tag K) * h)) =
          Multiplicative.ofAdd (vec g) * Multiplicative.ofAdd (vec h)
        rw [← ofAdd_add]
        congr 1
        funext i
        have ha := hAmul g g.2 h h.2
        have hc := hCmul g g.2 h h.2
        fin_cases i <;> simp [vec, ha, hc, map_add] }
  have hΦ : ∀ g : N, (Φ g).toAdd = vec g := fun _ => rfl
  have hker : ∀ g : N, Φ g = 1 → (g : ModGL TwistTag.D4.tag K) = 1 ∨
      (g : ModGL TwistTag.D4.tag K) = s := by
    intro g hg
    have hv : vec g = 0 := by
      have := congrArg Multiplicative.toAdd hg
      rwa [hΦ, toAdd_one] at this
    have hAg : A g = 0 := by simpa [vec] using congrFun hv 0
    have hCg : C g = 0 := by simpa [vec] using congrFun hv 3
    have hg3 : (g : ModGL TwistTag.D4.tag K) ∈ heightSeries TwistTag.D4.tag K 3 := by
      have h := (mem_inf.1 (decomp_middle σ hσ (hNQ g.2)).2).1
      have e1 : rootCoord (trialityRoot_pos 2) ((trialityX₁ K σ.toRingHom
          (rootCoord (trialityRoot_pos 0) (g : ModGL TwistTag.D4.tag K)) :
            ModGL TwistTag.D4.tag K)⁻¹ * (g : ModGL TwistTag.D4.tag K)) = 0 := hCg
      have e0 : rootCoord (trialityRoot_pos 0) (g : ModGL TwistTag.D4.tag K) = 0 := hAg
      rw [e1, e0, trialityX₃, orbitProd_zero, trialityX₁, orbitProd_zero, inv_one, one_mul,
        one_mul] at h
      exact h
    refine hZ g g.2 fun y hy => ?_
    have hgy := commutator_mem_heightSeries hg3
      (mem_one_of_mem_middle σ (hNQ hy) : y ∈ heightSeries TwistTag.D4.tag K 1)
    rcases hcomm g g.2 y hy with h1 | h1
    · exact commutatorElement_eq_one_iff_mul_comm.1 h1
    · exfalso
      rw [h1] at hgy
      exact hs4 (by simpa using hgy)
  have hcardker : Nat.card Φ.ker ≤ 2 := by
    let b : Φ.ker → Bool := fun x => decide (((x : N) : ModGL TwistTag.D4.tag K) = 1)
    have hb : Function.Injective b := by
      intro x y hxy
      apply Subtype.ext
      apply Subtype.ext
      rcases hker x (MonoidHom.mem_ker.1 x.2) with hx | hx <;>
        rcases hker y (MonoidHom.mem_ker.1 y.2) with hy | hy
      · rw [hx, hy]
      · exfalso
        have hs1 : s ≠ 1 := fun h => hs4 (by rw [h]; exact one_mem _)
        simp only [b, hx, hy, decide_true, hs1, decide_false] at hxy
        exact Bool.noConfusion hxy
      · exfalso
        have hs1 : s ≠ 1 := fun h => hs4 (by rw [h]; exact one_mem _)
        simp only [b, hx, hy, decide_true, hs1, decide_false] at hxy
        exact Bool.noConfusion hxy
      · rw [hx, hy]
    calc Nat.card Φ.ker ≤ Nat.card Bool := Nat.card_le_card_of_injective b hb
      _ = 2 := by simp
  obtain ⟨β, hβ⟩ := exists_middle_form μ
  have hβΦ : ∀ g h : N, β (Φ g).toAdd (Φ h).toAdd =
      μ⁻¹ * rootCoord (trialityRoot_pos 3) ⁅(g : ModGL TwistTag.D4.tag K), (h : ModGL _ K)⁆ := by
    intro g h
    have v1 : ∀ x, vec x 1 = σ (A x) := fun _ => rfl
    have v2 : ∀ x, vec x 2 = σ (σ (A x)) := fun _ => rfl
    have v4 : ∀ x, vec x 4 = σ (C x) := fun _ => rfl
    have v5 : ∀ x, vec x 5 = σ (σ (C x)) := fun _ => rfl
    rw [hβ, hΦ, hΦ, (rootCoord_commutator_middle σ hσ (hNQ g.2) (hNQ h.2)).2]
    simp only [v1, v2, v4, v5, hA, hC]
    ring
  have h01 : ∀ w ∈ Φ.range, ∀ w' ∈ Φ.range,
      β w.toAdd w'.toAdd = 0 ∨ β w.toAdd w'.toAdd = 1 := by
    rintro _ ⟨g, rfl⟩ _ ⟨h, rfl⟩
    rw [hβΦ]
    rcases hcomm g g.2 h h.2 with h1 | h1
    · left
      rw [h1, rootCoord_one, mul_zero]
    · right
      rw [h1, ← hμ, inv_mul_cancel₀ hμ0]
  have hnd : ∀ w ∈ Φ.range, (∀ w' ∈ Φ.range, β w.toAdd w'.toAdd = 0) → w = 1 := by
    rintro _ ⟨g, rfl⟩ hw
    have hcen : ∀ y ∈ N, (g : ModGL TwistTag.D4.tag K) * y = y * g := by
      intro y hy
      have h0 := hw (Φ ⟨y, hy⟩) ⟨⟨y, hy⟩, rfl⟩
      rw [hβΦ] at h0
      rcases hcomm g g.2 y hy with h1 | h1
      · exact commutatorElement_eq_one_iff_mul_comm.1 h1
      · exfalso
        rw [h1, ← hμ, inv_mul_cancel₀ hμ0] at h0
        exact one_ne_zero h0
    rcases hZ g g.2 hcen with h1 | h1
    · have hg1 : g = 1 := Subtype.ext h1
      rw [hg1, map_one]
    · have hgs : g = ⟨s, hsN⟩ := Subtype.ext h1
      rw [hgs]
      apply Multiplicative.toAdd.injective
      rw [hΦ, toAdd_one]
      funext i
      fin_cases i <;> simp [vec, hAs, hCs]
  have hW := card_le_of_bilinear Φ.range β h01 hnd
  have hsplit : Nat.card N = Nat.card Φ.range * Nat.card Φ.ker := by
    rw [card_eq_card_quotient_mul_card_subgroup Φ.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivRange Φ).toEquiv]
  rw [hsplit]
  calc Nat.card Φ.range * Nat.card Φ.ker ≤ 2 ^ 6 * 2 := Nat.mul_le_mul hW hcardker
    _ = 2 ^ 7 := by norm_num

end Middle

end CFSG.LargeExtraspecial.S8
