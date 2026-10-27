module

public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8D4Res

public noncomputable section

namespace CFSG.ComponentClassification.RankTwoExceptional.D4

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open scoped commutatorElement Matrix

section Conj

variable {K : Type} [Field K] (σ : K ≃+* K)

@[expose] def d4Conj
    (u v : ModGL TwistTag.D4.tag K) : Prop :=
  ∃ g ∈ d4C K σ, g * u * g⁻¹ = v

theorem d4Conj_trans
    {u v w : ModGL TwistTag.D4.tag K} (h₁ : d4Conj σ u v)
    (h₂ : d4Conj σ v w) : d4Conj σ u w := by
  obtain ⟨g, hg, rfl⟩ := h₁
  obtain ⟨g', hg', rfl⟩ := h₂
  exact ⟨g' * g, mul_mem hg' hg, by group⟩

theorem d4Conj_symm
    {u v : ModGL TwistTag.D4.tag K} (h : d4Conj σ u v) :
    d4Conj σ v u := by
  obtain ⟨g, hg, rfl⟩ := h
  exact ⟨g⁻¹, inv_mem hg, by group⟩

theorem mem_of_d4Conj
    {u v : ModGL TwistTag.D4.tag K} (h : d4Conj σ u v)
    (hu : u ∈ d4C K σ) : v ∈ d4C K σ := by
  obtain ⟨g, hg, rfl⟩ := h
  exact mul_mem (mul_mem hg hu) (inv_mem hg)

theorem sq_of_d4Conj
    {u v : ModGL TwistTag.D4.tag K} (h : d4Conj σ u v)
    (hu : u * u = 1) : v * v = 1 := by
  obtain ⟨g, -, rfl⟩ := h
  calc g * u * g⁻¹ * (g * u * g⁻¹) = g * (u * u) * g⁻¹ := by group
    _ = 1 := by rw [hu, mul_one, mul_inv_cancel]

end Conj

section NF

variable {K : Type} [Field K] [Finite K] [CharP K 2] (σ : K ≃+* K) (hσ : ∀ c, σ (σ (σ c)) = c)

omit [Finite K] in
include hσ in
theorem trialityMiddleTorus_mem_d4C
    [Finite K] (β : (trialityFixedField K σ.toRingHom)ˣ) :
    trialityMiddleTorus K σ β ∈ d4C K σ := by
  obtain ⟨-, ⟨e, he⟩, -⟩ :=
    even_triality_faithful_torus_coordinates K σ (ringEquiv_cube_d4 σ hσ)
  have h1 := (e (1, β)).2
  have h0 : trialityOuterTorus K σ 1 = 1 := by
    simp only [trialityOuterTorus, map_one, torusElt_one, List.map_const', List.prod_replicate,
      one_pow]
  rw [he, h0, one_mul] at h1
  exact (mem_inf.1 h1).2

omit [CharP K 2] in
theorem exists_mul_self_eq_d4 [CharP K 2] (a : K) : ∃ b : K, b * b = a := by
  have := Fintype.ofFinite K
  obtain ⟨r, hr⟩ := FiniteField.isSquare_of_char_two (ringChar.eq K 2) a
  exact ⟨r, hr.symm⟩

omit hσ in
theorem exists_mul_self_eq_fixed_d4 {a : K} (ha : σ a = a) : ∃ b : K, σ b = b ∧ b * b = a := by
  obtain ⟨b, rfl⟩ := exists_mul_self_eq_d4 a
  refine ⟨b, ?_, rfl⟩
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have h : (σ b + b) * (σ b + b) = 0 := by
    rw [map_mul] at ha
    linear_combination ha + (σ b * b + b * b) * h2
  linear_combination mul_self_eq_zero.1 h - b * h2

include hσ in
theorem d4Conj_d4x₆
    {f : K} (hf : σ f = f) (hf0 : f ≠ 0) :
    d4Conj σ (d4x₆ K f) (d4z K) := by
  set β : (trialityFixedField K σ.toRingHom)ˣ :=
    Units.mk0 ⟨f⁻¹, by rw [mem_trialityFixedField]; simp [hf]⟩
      (by intro h; exact inv_ne_zero hf0 (congrArg Subtype.val h))
  refine ⟨_, trialityMiddleTorus_mem_d4C σ hσ β, ?_⟩
  rw [hm_conj_d4x₆, d4z]
  congr 1
  exact inv_mul_cancel₀ hf0

include hσ in
theorem d4Conj_d4x₂
    {b : K} (hb : σ b = b) (hb0 : b ≠ 0) :
    d4Conj σ (d4x₂ K b) (d4z K) := by
  obtain ⟨β, hβσ, hβ⟩ := exists_mul_self_eq_fixed_d4 σ (a := b⁻¹) (by rw [map_inv₀, hb])
  have hβ0 : β ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hβ
    exact inv_ne_zero hb0 hβ.symm
  set B : (trialityFixedField K σ.toRingHom)ˣ :=
    Units.mk0 ⟨β, by rw [mem_trialityFixedField]; exact hβσ⟩
      (by intro h; exact hβ0 (congrArg Subtype.val h))
  have h1 : d4Conj σ (d4x₂ K b) (d4x₂ K 1) := by
    refine ⟨_, trialityMiddleTorus_mem_d4C σ hσ B, ?_⟩
    rw [hm_conj_d4x₂]
    congr 1
    change β ^ 2 * b = 1
    rw [sq, hβ, inv_mul_cancel₀ hb0]
  have h2 : d4Conj σ (d4x₂ K 1) (d4x₅ K 1) :=
    ⟨_, (trialityRep_mem σ).1, trialityOuterRep_conj_d4x₂ 1⟩
  have h3 : d4Conj σ (d4x₅ K 1) (d4z K) :=
    ⟨_, (trialityRep_mem σ).2, trialityMiddleRep_conj_d4x₅ 1⟩
  exact d4Conj_trans σ (d4Conj_trans σ h1 h2) h3

include hσ in
theorem d4Conj_d4x₁_d4x₄
    {d : K} (hd0 : d ≠ 0) :
    d4Conj σ (d4x₁ K σ 1) (d4x₄ K σ d) := by
  obtain ⟨a, ha⟩ := exists_mul_self_eq_d4 d
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [mul_zero] at ha
    exact hd0 ha.symm
  have h1 : d4Conj σ (d4x₁ K σ 1) (d4x₁ K σ d) := by
    refine ⟨_, trialityOuterTorus_mem_d4C σ hσ (Units.mk0 a ha0), ?_⟩
    rw [ho_conj_d4x₁, Units.val_mk0, mul_one, sq, ha]
  have h2 : d4Conj σ (d4x₁ K σ d) (d4x₃ K σ d) :=
    ⟨_, (trialityRep_mem σ).2, trialityMiddleRep_conj_d4x₁ σ d⟩
  have h3 : d4Conj σ (d4x₃ K σ d) (d4x₄ K σ d) :=
    ⟨_, (trialityRep_mem σ).1, trialityOuterRep_conj_d4x₃ σ d⟩
  exact d4Conj_trans σ (d4Conj_trans σ h1 h2) h3

include hσ in
theorem d4Conj_d4x₄
    {d : K} (hd0 : d ≠ 0) : d4Conj σ (d4x₄ K σ d) (d4t K σ) :=
  d4Conj_trans σ (d4Conj_symm σ (d4Conj_d4x₁_d4x₄ σ hσ hd0))
    (d4Conj_d4x₁_d4x₄ σ hσ one_ne_zero)

include hσ in
theorem fixed_coords_of_mem_d4C
    {b c d e f : K} (h : d4v K σ b c d e f ∈ d4C K σ) :
    σ b = b ∧ σ e = e ∧ σ f = f := by
  have hσ3 := toRingHom_pow_three_d4 σ hσ
  have hS : d4v K σ b c d e f ∈ rootSpan TwistTag.D4.tag K
      (simpleComplementRoots TwistTag.D4 ⟨0, by decide⟩) := by
    have hm : ∀ j : Fin 6, j ≠ 0 → d4factors σ 0 b c d e f j ∈ rootSpan TwistTag.D4.tag K
        (simpleComplementRoots TwistTag.D4 ⟨0, by decide⟩) := fun j hj =>
      rootSpan_mono (trialityOrbit_subset_simpleComplementRoots j hj)
        (d4factors_mem σ 0 b c d e f j)
    exact mul_mem (mul_mem (mul_mem (mul_mem (hm 1 (by decide)) (hm 2 (by decide)))
      (hm 3 (by decide))) (hm 4 (by decide))) (hm 5 (by decide))
  obtain ⟨b', c', d', e', f', hb', he', hf', h'⟩ :=
    exists_d4v σ hσ3 (mem_inf.2 ⟨hS, graphFixedRootGroup_le _ _ _ h⟩)
  obtain ⟨rfl, -, -, rfl, rfl⟩ := d4v_injective σ h'
  exact ⟨hb', he', hf'⟩

end NF

section Moves

variable {K : Type} [Field K] [CharP K 2] (σ : K ≃+* K) (hσ : ∀ c, σ (σ (σ c)) = c)

include hσ in
theorem d4v_mul_self_eq_one_iff
    {b c d e f : K} :
    d4v K σ b c d e f * d4v K σ b c d e f = 1 ↔
      b * e + (c * d + σ (c * d) + σ (σ (c * d))) = 0 := by
  rw [d4v_mul_self σ hσ]
  constructor
  · intro h
    exact pinnedX_injective _ _ _ (h.trans (pinnedX_zero _ _ _).symm)
  · intro h
    rw [h]
    exact d4x₆_zero K

include hσ in
theorem d4Conj_x₁
    {b c d e f : K} (s : K) (hb : σ b = b) : ∃ F : K,
    d4Conj σ (d4v K σ b c d e f) (d4v K σ b (c + b * s)
      (d + b * (σ s * σ (σ s)) + (σ s * σ (σ c) + σ (σ s) * σ c))
      (e + b * (s * σ s * σ (σ s)) + (σ s * σ (σ s) * c + σ (σ s * σ (σ s) * c) +
        σ (σ (σ s * σ (σ s) * c))) + (s * d + σ (s * d) + σ (σ (s * d)))) F) := by
  obtain ⟨F, hF⟩ := d4x₁_conj_d4v σ hσ s b c d e f hb
  exact ⟨F, _, (d4x_short_mem σ (toRingHom_pow_three_d4 σ hσ) s).1, hF⟩

include hσ in
theorem d4Conj_nr
    (b c d e f : K) :
    d4Conj σ (d4v K σ b c d e f)
      (d4v K σ e d c b (b * e + (c * d + σ (c * d) + σ (σ (c * d))) + f)) :=
  ⟨_, (trialityRep_mem σ).1, trialityOuterRep_conj_d4v σ hσ b c d e f⟩

include hσ in
theorem d4Conj_x₃
    (γ b c d e f : K) :
    d4Conj σ (d4v K σ b c d e f) (d4v K σ b c d e (d * γ + σ (d * γ) + σ (σ (d * γ)) + f)) :=
  ⟨_, (d4x_short_mem σ (toRingHom_pow_three_d4 σ hσ) γ).2.1, d4x₃_conj_d4v σ hσ γ b c d e f⟩

include hσ in
theorem d4Conj_x₅
    {γ : K} (hγ : σ γ = γ) (b c d e f : K) :
    d4Conj σ (d4v K σ b c d e f) (d4v K σ b c d e (γ * b + f)) := by
  refine ⟨_, (d4x_long_mem σ hγ).2.1, ?_⟩
  have h := comm_d4v_d4v σ hσ 0 0 0 γ 0 b c d e f
  rw [← d4x₅_eq_d4v σ] at h
  calc d4x₅ K γ * d4v K σ b c d e f * (d4x₅ K γ)⁻¹ =
      ⁅d4x₅ K γ, d4v K σ b c d e f⁆ * d4v K σ b c d e f := by
        simp only [commutatorElement_def]; group
    _ = _ := by
      rw [h, d4x₆_eq_d4v σ, d4v_mul σ hσ]
      refine d4v_congr σ (by ring) (by ring) (by ring) (by ring) ?_
      simp only [mul_zero, zero_mul, map_zero, add_zero, zero_add]

end Moves

section TraceObs

variable {K : Type} [Field K] [CharP K 2] (σ : K ≃+* K) (hσ : ∀ c, σ (σ (σ c)) = c)

include hσ in
theorem exists_trace_ne_zero_d4 {c d : K} (hcd : c ≠ 0 ∨ d ≠ 0)
    (hT : c * d + σ (c * d) + σ (σ (c * d)) = 0) :
    ∃ s : K, (σ s * σ (σ s) * c + σ (σ s * σ (σ s) * c) + σ (σ (σ s * σ (σ s) * c))) +
        (s * d + σ (s * d) + σ (σ (s * d))) ≠ 0 ∨
      (σ s * σ (σ s) * d + σ (σ s * σ (σ s) * d) + σ (σ (σ s * σ (σ s) * d))) +
        (s * c + σ (s * c) + σ (σ (s * c))) ≠ 0 := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  by_contra hcon
  push Not at hcon
  have key : ∀ x y : K, (∀ s : K, (σ s * σ (σ s) * x + σ (σ s * σ (σ s) * x) +
      σ (σ (σ s * σ (σ s) * x))) + (s * y + σ (s * y) + σ (σ (s * y))) = 0) →
      σ x = x := by
    intro x y hA
    have hz : ∀ s : K, (σ x + σ (σ x)) * s + σ ((σ x + σ (σ x)) * s) +
        σ (σ ((σ x + σ (σ x)) * s)) = 0 := fun s => by
      have h1 := hA (s + 1)
      have h3 := hA s
      have h4 := hA 1
      simp only [map_add, map_mul, map_one, hσ] at h1 h3 h4 ⊢
      linear_combination h1 - h3 - h4
    have h5 : σ x + σ (σ x) = 0 := eq_zero_of_trace_d4 σ hz
    have h6 : σ x = σ (σ x) := by linear_combination h5 - σ (σ x) * h2
    exact (σ.injective h6).symm
  have hc := key c d fun s => (hcon s).1
  have hd := key d c fun s => (hcon s).2
  have h1 := (hcon 1).1
  simp only [map_one, one_mul, mul_one, hc, hd] at h1
  have hcd' : c = d := by linear_combination h1 - (c + 2 * d) * h2
  subst hcd'
  simp only [map_mul, hc] at hT
  have hc0 : c * c = 0 := by linear_combination hT - (c * c) * h2
  rcases hcd with h | h <;> exact h (mul_self_eq_zero.1 hc0)

end TraceObs

section Vr

variable {K : Type} [Field K] [Finite K] [CharP K 2] (σ : K ≃+* K) (hσ : ∀ c, σ (σ (σ c)) = c)

include hσ in
theorem d4Conj_of_fst_ne_zero
    {b c d e f : K} (hb0 : b ≠ 0)
    (hv : d4v K σ b c d e f ∈ d4C K σ) (hv2 : d4v K σ b c d e f * d4v K σ b c d e f = 1) :
    d4Conj σ (d4v K σ b c d e f) (d4z K) ∨ d4Conj σ (d4v K σ b c d e f) (d4t K σ) := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  obtain ⟨hbσ, -, -⟩ := fixed_coords_of_mem_d4C σ hσ hv
  obtain ⟨F₁, h₁⟩ := d4Conj_x₁ σ hσ (b := b) (c := c) (d := d) (e := e) (f := f) (c * b⁻¹) hbσ
  have hc : c + b * (c * b⁻¹) = 0 := by
    rw [mul_comm c, ← mul_assoc, mul_inv_cancel₀ hb0, one_mul]
    linear_combination c * h2
  rw [hc] at h₁
  generalize hD₁ : d + b * (σ (c * b⁻¹) * σ (σ (c * b⁻¹))) +
    (σ (c * b⁻¹) * σ (σ c) + σ (σ (c * b⁻¹)) * σ c) = D₁ at h₁
  generalize hE₁ : e + b * (c * b⁻¹ * σ (c * b⁻¹) * σ (σ (c * b⁻¹))) +
    (σ (c * b⁻¹) * σ (σ (c * b⁻¹)) * c + σ (σ (c * b⁻¹) * σ (σ (c * b⁻¹)) * c) +
      σ (σ (σ (c * b⁻¹) * σ (σ (c * b⁻¹)) * c))) +
    (c * b⁻¹ * d + σ (c * b⁻¹ * d) + σ (σ (c * b⁻¹ * d))) = E₁ at h₁
  have hv₁ := mem_of_d4Conj σ h₁ hv
  have hv₁2 := sq_of_d4Conj σ h₁ hv2
  rw [d4v_mul_self_eq_one_iff σ hσ] at hv₁2
  simp only [zero_mul, map_zero, add_zero] at hv₁2
  have hE₀ : E₁ = 0 := (mul_eq_zero.1 hv₁2).resolve_left hb0
  rw [hE₀] at h₁ hv₁
  obtain ⟨-, -, hF₁⟩ := fixed_coords_of_mem_d4C σ hσ hv₁
  by_cases hD₀ : D₁ = 0
  ·
    left
    rw [hD₀] at h₁
    have hγ : σ (F₁ * b⁻¹) = F₁ * b⁻¹ := by rw [map_mul, map_inv₀, hF₁, hbσ]
    have h₂ := d4Conj_x₅ σ hσ hγ b 0 0 0 F₁
    have hf : F₁ * b⁻¹ * b + F₁ = 0 := by
      rw [mul_assoc, inv_mul_cancel₀ hb0, mul_one]
      linear_combination F₁ * h2
    rw [hf, ← d4x₂_eq_d4v σ] at h₂
    exact d4Conj_trans σ (d4Conj_trans σ h₁ h₂) (d4Conj_d4x₂ σ hσ hbσ hb0)
  ·
    right
    have h₂ := d4Conj_nr σ hσ b 0 D₁ 0 F₁
    simp only [mul_zero, zero_mul, map_zero, add_zero, zero_add] at h₂
    have hσD : σ D₁ ≠ 0 := (map_ne_zero σ).2 hD₀
    have hσσD : σ (σ D₁) ≠ 0 := (map_ne_zero σ).2 hσD
    have hN0 : D₁ * σ D₁ * σ (σ D₁) ≠ 0 := mul_ne_zero (mul_ne_zero hD₀ hσD) hσσD
    have hNσ : σ (D₁ * σ D₁ * σ (σ D₁)) = D₁ * σ D₁ * σ (σ D₁) := by
      rw [map_mul, map_mul, hσ]
      ring
    obtain ⟨l, hlσ, hl⟩ := exists_mul_self_eq_fixed_d4 σ (a := b * (D₁ * σ D₁ * σ (σ D₁))⁻¹)
      (by rw [map_mul, map_inv₀, hbσ, hNσ])
    obtain ⟨F₃, h₃⟩ := d4Conj_x₁ σ hσ (b := 0) (c := D₁) (d := 0) (e := b) (f := F₁)
      (l * D₁) (map_zero σ)
    have hd₃ : 0 + 0 * (σ (l * D₁) * σ (σ (l * D₁))) +
        (σ (l * D₁) * σ (σ D₁) + σ (σ (l * D₁)) * σ D₁) = 0 := by
      simp only [map_mul, hlσ]
      linear_combination (l * σ D₁ * σ (σ D₁)) * h2
    have he₃ : b + 0 * (l * D₁ * σ (l * D₁) * σ (σ (l * D₁))) +
        (σ (l * D₁) * σ (σ (l * D₁)) * D₁ + σ (σ (l * D₁) * σ (σ (l * D₁)) * D₁) +
          σ (σ (σ (l * D₁) * σ (σ (l * D₁)) * D₁))) +
        (l * D₁ * 0 + σ (l * D₁ * 0) + σ (σ (l * D₁ * 0))) = 0 := by
      have hl' : l * l * (D₁ * σ D₁ * σ (σ D₁)) = b := by
        rw [hl, mul_assoc, inv_mul_cancel₀ hN0, mul_one]
      simp only [map_mul, hlσ, hσ, mul_zero, map_zero, add_zero, zero_mul]
      linear_combination 3 * hl' + (2 * b) * h2
    rw [hd₃, he₃, zero_mul, add_zero] at h₃
    have hv₃ := mem_of_d4Conj σ (d4Conj_trans σ h₂ h₃)
      (mem_of_d4Conj σ h₁ hv)
    obtain ⟨-, -, hF₃⟩ := fixed_coords_of_mem_d4C σ hσ hv₃
    have h₄ := d4Conj_nr σ hσ 0 D₁ 0 0 F₃
    simp only [mul_zero, map_zero, add_zero, zero_add] at h₄
    have h₅ := d4Conj_x₃ σ hσ (F₃ * D₁⁻¹) 0 0 D₁ 0 F₃
    have hf : D₁ * (F₃ * D₁⁻¹) + σ (D₁ * (F₃ * D₁⁻¹)) + σ (σ (D₁ * (F₃ * D₁⁻¹))) + F₃ = 0 := by
      rw [mul_comm F₃, ← mul_assoc, mul_inv_cancel₀ hD₀, one_mul, hF₃, hF₃]
      linear_combination (2 * F₃) * h2
    rw [hf, ← d4x₄_eq_d4v σ] at h₅
    exact d4Conj_trans σ (d4Conj_trans σ (d4Conj_trans σ (d4Conj_trans σ (d4Conj_trans σ h₁ h₂)
      h₃) h₄) h₅) (d4Conj_d4x₄ σ hσ hD₀)

include hσ in
theorem d4Conj_of_fourth_ne_zero
    {c d e f : K} (he0 : e ≠ 0)
    (hv : d4v K σ 0 c d e f ∈ d4C K σ) (hv2 : d4v K σ 0 c d e f * d4v K σ 0 c d e f = 1) :
    d4Conj σ (d4v K σ 0 c d e f) (d4z K) ∨ d4Conj σ (d4v K σ 0 c d e f) (d4t K σ) := by
  have h₁ := d4Conj_nr σ hσ 0 c d e f
  rcases d4Conj_of_fst_ne_zero σ hσ he0 (mem_of_d4Conj σ h₁ hv) (sq_of_d4Conj σ h₁ hv2)
    with h | h
  · exact Or.inl (d4Conj_trans σ h₁ h)
  · exact Or.inr (d4Conj_trans σ h₁ h)

include hσ in
theorem d4Conj_of_mid_ne_zero
    {c d f : K} (hcd : c ≠ 0 ∨ d ≠ 0)
    (hv : d4v K σ 0 c d 0 f ∈ d4C K σ) (hv2 : d4v K σ 0 c d 0 f * d4v K σ 0 c d 0 f = 1) :
    d4Conj σ (d4v K σ 0 c d 0 f) (d4z K) ∨ d4Conj σ (d4v K σ 0 c d 0 f) (d4t K σ) := by
  have hT : c * d + σ (c * d) + σ (σ (c * d)) = 0 := by
    have h := (d4v_mul_self_eq_one_iff σ hσ).1 hv2
    rwa [zero_mul, zero_add] at h
  obtain ⟨s, hs | hs⟩ := exists_trace_ne_zero_d4 σ hσ hcd hT
  · obtain ⟨F, h₁⟩ := d4Conj_x₁ σ hσ (b := 0) (c := c) (d := d) (e := 0) (f := f) s (map_zero σ)
    simp only [zero_mul, add_zero, zero_add] at h₁
    rcases d4Conj_of_fourth_ne_zero σ hσ hs (mem_of_d4Conj σ h₁ hv) (sq_of_d4Conj σ h₁ hv2)
      with h | h
    · exact Or.inl (d4Conj_trans σ h₁ h)
    · exact Or.inr (d4Conj_trans σ h₁ h)
  · have h₀ := d4Conj_nr σ hσ 0 c d 0 f
    simp only [zero_mul, zero_add] at h₀
    obtain ⟨F, h₁⟩ := d4Conj_x₁ σ hσ (b := 0) (c := d) (d := c) (e := 0)
      (f := c * d + σ (c * d) + σ (σ (c * d)) + f) s (map_zero σ)
    simp only [zero_mul, add_zero, zero_add] at h₁
    have h₂ := d4Conj_trans σ h₀ h₁
    rcases d4Conj_of_fourth_ne_zero σ hσ hs (mem_of_d4Conj σ h₂ hv) (sq_of_d4Conj σ h₂ hv2)
      with h | h
    · exact Or.inl (d4Conj_trans σ h₂ h)
    · exact Or.inr (d4Conj_trans σ h₂ h)

include hσ in
theorem d4Conj_of_mem_Vr
    {b c d e f : K} (hv : d4v K σ b c d e f ∈ d4C K σ)
    (hv2 : d4v K σ b c d e f * d4v K σ b c d e f = 1) (hv1 : d4v K σ b c d e f ≠ 1) :
    d4Conj σ (d4v K σ b c d e f) (d4z K) ∨ d4Conj σ (d4v K σ b c d e f) (d4t K σ) := by
  by_cases hb : b = 0
  · subst hb
    by_cases he : e = 0
    · subst he
      by_cases hcd : c ≠ 0 ∨ d ≠ 0
      · exact d4Conj_of_mid_ne_zero σ hσ hcd hv hv2
      · push Not at hcd
        obtain ⟨rfl, rfl⟩ := hcd
        left
        have hf0 : f ≠ 0 := by
          rintro rfl
          exact hv1 (d4v_zero σ)
        rw [← d4x₆_eq_d4v σ] at hv ⊢
        obtain ⟨-, -, hfσ⟩ := fixed_coords_of_mem_d4C σ hσ (by rwa [← d4x₆_eq_d4v σ])
        exact d4Conj_d4x₆ σ hσ hfσ hf0
    · exact d4Conj_of_fourth_ne_zero σ hσ he hv hv2
  · exact d4Conj_of_fst_ne_zero σ hσ hb hv hv2

end Vr

section U

variable {K : Type} [Field K] [Finite K] [CharP K 2] (σ : K ≃+* K) (hσ : ∀ c, σ (σ (σ c)) = c)

omit [Finite K] in
include hσ in
theorem comm_d4x₁_d4x₂_eq_d4v
    (a : K) {l : K} (hl : σ l = l) : ∃ F : K,
    ⁅d4x₁ K σ a, d4x₂ K l⁆ =
      d4v K σ 0 (l * a) (l * (σ a * σ (σ a))) (l * (a * σ a * σ (σ a))) F := by
  rw [comm_d4x₁_d4x₂ σ hσ a l hl, d4x₅_eq_d4v σ, d4x₄_eq_d4v σ, d4x₆_eq_d4v σ, d4x₃_eq_d4v σ,
    d4v_mul σ hσ, d4v_mul σ hσ, d4v_mul σ hσ]
  exact ⟨_, d4v_congr σ (by ring) (by ring) (by ring) (by ring) rfl⟩

omit [Finite K] in
include hσ in
theorem d4Conj_Vr_of_d4x₁
    {a b c d e f : K} (ha0 : a ≠ 0) (hb : σ b = b)
    (hu2 : d4x₁ K σ a * d4v K σ b c d e f * (d4x₁ K σ a * d4v K σ b c d e f) = 1) :
    ∃ D E F : K, d4Conj σ (d4x₁ K σ a * d4v K σ b c d e f) (d4v K σ 0 a D E F) := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hsq : d4x₁ K σ a * d4v K σ b c d e f * (d4x₁ K σ a * d4v K σ b c d e f) =
      d4x₁ K σ a * d4v K σ b c d e f * (d4x₁ K σ a)⁻¹ * d4v K σ b c d e f := by
    rw [d4x₁_inv]
    group
  obtain ⟨F₀, hF₀⟩ := d4x₁_conj_d4v σ hσ a b c d e f hb
  rw [hsq, hF₀, d4v_mul σ hσ, ← d4v_zero σ] at hu2
  obtain ⟨-, hc', hd', -, -⟩ := d4v_injective σ hu2
  have hb0 : b = 0 := by
    have h : b * a = 0 := by linear_combination hc' - c * h2
    exact (mul_eq_zero.1 h).resolve_right ha0
  subst hb0
  have hac : σ a * σ (σ c) + σ (σ a) * σ c = 0 := by
    simp only [zero_mul, add_zero] at hd'
    linear_combination hd' - d * h2
  obtain ⟨l, hl⟩ : ∃ l : K, l = c * a⁻¹ := ⟨_, rfl⟩
  have hca : c = l * a := by rw [hl, mul_assoc, inv_mul_cancel₀ ha0, mul_one]
  have hσa : σ a ≠ 0 := (map_ne_zero σ).2 ha0
  have hσσa : σ (σ a) ≠ 0 := (map_ne_zero σ).2 hσa
  have hlσ : σ l = l := by
    rw [hca] at hac
    simp only [map_mul] at hac
    have h3 : σ a * σ (σ a) * (σ (σ l) + σ l) = 0 := by linear_combination hac
    have h4 : σ (σ l) + σ l = 0 := (mul_eq_zero.1 h3).resolve_left (mul_ne_zero hσa hσσa)
    have h5 : σ (σ l) = σ l := by linear_combination h4 - σ l * h2
    exact σ.injective h5
  obtain ⟨F₁, hF₁⟩ := comm_d4x₁_d4x₂_eq_d4v σ hσ a hlσ
  have hx₂ : d4x₂ K l * (d4x₁ K σ a * d4v K σ 0 c d e f) * (d4x₂ K l)⁻¹ =
      d4x₁ K σ a * (⁅d4x₁ K σ a, d4x₂ K l⁆ *
        (d4x₂ K l * d4v K σ 0 c d e f * (d4x₂ K l)⁻¹)) := by
    have h1 : d4x₁ K σ a * d4x₁ K σ a = 1 := d4x₁_mul_self σ a
    simp only [commutatorElement_def]
    rw [d4x₁_inv]
    calc d4x₂ K l * (d4x₁ K σ a * d4v K σ 0 c d e f) * (d4x₂ K l)⁻¹ =
        (d4x₁ K σ a * d4x₁ K σ a) * d4x₂ K l * d4x₁ K σ a * (d4x₂ K l)⁻¹ *
          (d4x₂ K l * d4v K σ 0 c d e f * (d4x₂ K l)⁻¹) := by rw [h1]; group
      _ = _ := by group
  rw [hF₁, d4x₂_conj_d4v σ hσ l 0 c d e f, d4v_mul σ hσ] at hx₂
  have hc0 : 0 + 0 = (0 : K) ∧ l * a + c = 0 := by
    refine ⟨add_zero 0, ?_⟩
    rw [hca]
    linear_combination (l * a) * h2
  rw [hc0.1, hc0.2] at hx₂
  have hna : ∀ D' E' G : K, trialityMiddleRep K * (d4x₁ K σ a * d4v K σ 0 0 D' E' G) *
      (trialityMiddleRep K)⁻¹ = d4v K σ 0 a D' G E' := by
    intro D' E' G
    rw [← MulAut.conj_apply, map_mul, MulAut.conj_apply, MulAut.conj_apply,
      trialityMiddleRep_conj_d4x₁, trialityMiddleRep_conj_d4v σ hσ, d4x₃_eq_d4v σ, d4v_mul σ hσ]
    refine d4v_congr σ (by ring) (by ring) (by ring) (by ring) ?_
    simp only [mul_zero, map_zero, add_zero, zero_add]
  exact ⟨_, _, _, d4Conj_trans σ ⟨_, (d4x_long_mem σ hlσ).1, hx₂⟩
    ⟨_, (trialityRep_mem σ).2, hna _ _ _⟩⟩

include hσ in
theorem d4Conj_of_mem_U
    {u : ModGL TwistTag.D4.tag K}
    (hu : u ∈ graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom) (hu2 : u * u = 1) (hu1 : u ≠ 1) :
    d4Conj σ u (d4z K) ∨ d4Conj σ u (d4t K σ) := by
  have hσ3 := toRingHom_pow_three_d4 σ hσ
  have huC := graphFixedPosUnipotent_le_graphFixedRootGroup _ _ _ hu
  obtain ⟨a, b, c, d, e, f, hb, -, -, rfl⟩ := exists_d4coord σ hσ3 hu
  by_cases ha : a = 0
  · subst ha
    rw [d4x₁_zero, one_mul] at huC hu2 hu1 ⊢
    exact d4Conj_of_mem_Vr σ hσ huC hu2 hu1
  · obtain ⟨D, E, F, h⟩ := d4Conj_Vr_of_d4x₁ σ hσ ha hb hu2
    have hv1 : d4v K σ 0 a D E F ≠ 1 := by
      intro h1
      rw [← d4v_zero σ] at h1
      exact ha (d4v_injective σ h1).2.1
    rcases d4Conj_of_mem_Vr σ hσ (mem_of_d4Conj σ h huC) (sq_of_d4Conj σ h hu2) hv1 with h' | h'
    · exact Or.inl (d4Conj_trans σ h h')
    · exact Or.inr (d4Conj_trans σ h h')

end U

section Classes

variable {K : Type} [Field K] [Finite K] [CharP K 2] (σ : K ≃+* K) (hσ : ∀ c, σ (σ (σ c)) = c)

theorem exists_conj_mem_U_d4
    {x : ↥(d4C K σ)} (hx2 : x * x = 1) :
    ∃ c : ↥(d4C K σ), ((c * x * c⁻¹ : ↥(d4C K σ)) : ModGL TwistTag.D4.tag K) ∈
      graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (ModGL TwistTag.D4.tag K) := finite_modGL
  set P : Sylow 2 ↥(d4C K σ) := (isPGroup_graphFixedPosUnipotent_subgroupOf 2).toSylow
    (not_dvd_index_graphFixedPosUnipotent 2 σ.surjective)
  have hQ : IsPGroup 2 (zpowers x) := by
    intro g
    obtain ⟨n, hn⟩ := mem_zpowers_iff.1 g.2
    refine ⟨1, Subtype.ext ?_⟩
    rw [Subgroup.coe_pow, ← hn, pow_one, sq, ← (Commute.refl x).mul_zpow, hx2, one_zpow]
    rfl
  obtain ⟨Q, hQ⟩ := hQ.exists_le_sylow
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq ↥(d4C K σ) Q P
  refine ⟨c, ?_⟩
  have h := Subgroup.smul_mem_pointwise_smul _ (MulAut.conj c) _ (hQ (mem_zpowers x))
  rw [MulAut.smul_def, MulAut.conj_apply, ← Sylow.coe_subgroup_smul, hc] at h
  exact mem_subgroupOf.1 h

include hσ in
theorem d4_classesCover
    {z t : ↥(d4C K σ)} (hz : (z : ModGL TwistTag.D4.tag K) = d4z K)
    (ht : (t : ModGL TwistTag.D4.tag K) = d4t K σ) : Exc.ClassesCover [z, t] := by
  intro x hx2 hx1
  obtain ⟨c, hc⟩ := exists_conj_mem_U_d4 σ hx2
  have hu2 : ((c * x * c⁻¹ : ↥(d4C K σ)) : ModGL TwistTag.D4.tag K) *
      ((c * x * c⁻¹ : ↥(d4C K σ)) : ModGL TwistTag.D4.tag K) = 1 := by
    rw [← Subgroup.coe_mul]
    have : c * x * c⁻¹ * (c * x * c⁻¹) = 1 := by
      calc c * x * c⁻¹ * (c * x * c⁻¹) = c * (x * x) * c⁻¹ := by group
        _ = 1 := by rw [hx2, mul_one, mul_inv_cancel]
    rw [this, Subgroup.coe_one]
  have hu1 : ((c * x * c⁻¹ : ↥(d4C K σ)) : ModGL TwistTag.D4.tag K) ≠ 1 := by
    intro h
    apply hx1
    have h' : c * x * c⁻¹ = 1 := Subtype.ext h
    calc x = c⁻¹ * (c * x * c⁻¹) * c := by group
      _ = 1 := by rw [h', mul_one, inv_mul_cancel]
  have key : ∀ y : ↥(d4C K σ), d4Conj σ ((c * x * c⁻¹ : ↥(d4C K σ)) : ModGL TwistTag.D4.tag K)
      (y : ModGL TwistTag.D4.tag K) → IsConj y x := by
    rintro y ⟨g, hg, hgy⟩
    refine (isConj_iff.2 ⟨(⟨g, hg⟩ : ↥(d4C K σ)) * c, Subtype.ext ?_⟩).symm
    rw [← hgy]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    group
  rcases d4Conj_of_mem_U σ hσ hc hu2 hu1 with h | h
  · exact ⟨z, List.mem_cons_self, key z (hz ▸ h)⟩
  · exact ⟨t, List.mem_cons_of_mem _ List.mem_cons_self, key t (ht ▸ h)⟩

end Classes

theorem d4ClassFacts :
    D4ClassFacts := by
  intro m hm K _ _ hK σ hσq z t hz ht
  have := charP_two_of_card_d4 hK
  have hσ := sigma_cube_of_card_d4 σ hK hσq
  exact ⟨d4_classesCover σ hσ hz ht, ⟨_, d4_classData_z m hm K hK σ hσq z hz⟩,
    ⟨_, d4_classData_t m hm K hK σ hσq t ht⟩⟩

end CFSG.ComponentClassification.RankTwoExceptional.D4
