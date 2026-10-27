module

public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8D4Cell
public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8ExcSub

public noncomputable section

namespace CFSG.ComponentClassification.RankTwoExceptional.D4

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open scoped commutatorElement Matrix

section CentT3

variable {K : Type} [Field K] [CharP K 2] (σ : K ≃+* K) (hσ : ∀ c, σ (σ (σ c)) = c)

include hσ in
theorem borel_conj_d4vA_lin
    [Finite K] {b : ModGL TwistTag.D4.tag K}
    (hb : b ∈ graphFixedRootBorel TwistTag.D4 K σ.toRingHom) {D E F : K} (hE : σ E = E)
    (hF : σ F = F) :
    ∃ D' E' F' : K, σ E' = E' ∧ σ F' = F' ∧ b * d4v K σ 0 0 D E F * b⁻¹ = d4v K σ 0 0 D' E' F' ∧
      ∀ c : K, σ c = c → b * d4v K σ 0 0 (c * D) (c * E) (c * F) * b⁻¹ =
        d4v K σ 0 0 (c * D') (c * E') (c * F') := by
  obtain ⟨a, β, a₁, b₁, c₁, d₁, e₁, f₁, hb₁, -, -, -, -, rfl⟩ := exists_borel_coords σ hσ hb
  have hβ : σ ((trialityFixedUnit K σ β : Kˣ) : K) = (trialityFixedUnit K σ β : Kˣ) :=
    sigma_trialityFixedUnit β
  refine ⟨_, _, _, ?_, ?_, borel_conj_d4vA σ hσ a β a₁ b₁ c₁ d₁ e₁ f₁ D E F, fun c hc => ?_⟩
  · simp only [map_mul, map_inv₀, map_add, hβ, hσ, hE]
    ring
  · simp only [map_mul, map_add, hβ, hσ, hb₁, hE, hF]
    ring
  · rw [borel_conj_d4vA σ hσ]
    refine d4v_congr σ rfl rfl (by ring) ?_ ?_
    · simp only [map_mul, hc]
      ring
    · simp only [map_mul, hc]
      ring

include hσ in
theorem conj_d4x₄_of_commute
    [Finite K] {g : ModGL TwistTag.D4.tag K} (hg : g ∈ d4C K σ)
    (ht : g * d4t K σ * g⁻¹ = d4t K σ) {c : K} (hc : σ c = c) :
    g * d4x₄ K σ c * g⁻¹ = d4x₄ K σ c := by
  obtain ⟨w, hw, b, hb, b', hb', rfl⟩ := exists_cell_d4 σ hg
  have hn := weyl_t_of_commute σ hσ hw hb hb' ht
  have e1 : ∀ x, b * canonicalRep (coxeterSystem TwistTag.D4.tag) K w * b' * x *
      (b * canonicalRep (coxeterSystem TwistTag.D4.tag) K w * b')⁻¹ =
      b * (canonicalRep (coxeterSystem TwistTag.D4.tag) K w * (b' * x * b'⁻¹) *
        (canonicalRep (coxeterSystem TwistTag.D4.tag) K w)⁻¹) * b⁻¹ := fun x => by group
  have hx₄ : ∀ c : K, d4x₄ K σ c = d4v K σ 0 0 (c * 1) (c * 0) (c * 0) := fun c => by
    rw [d4x₄_eq_d4v σ, mul_one, mul_zero]
  obtain ⟨D₁, E₁, F₁, hE₁, hF₁, h₁, hl₁⟩ :=
    borel_conj_d4vA_lin σ hσ hb' (D := 1) (E := 0) (F := 0) (map_zero σ) (map_zero σ)
  obtain ⟨D₂, E₂, F₂, hE₂, hF₂, h₂, hl₂⟩ : ∃ D₂ E₂ F₂ : K, σ E₂ = E₂ ∧ σ F₂ = F₂ ∧
      canonicalRep (coxeterSystem TwistTag.D4.tag) K w * d4v K σ 0 0 D₁ E₁ F₁ *
        (canonicalRep (coxeterSystem TwistTag.D4.tag) K w)⁻¹ = d4v K σ 0 0 D₂ E₂ F₂ ∧
      ∀ c : K, canonicalRep (coxeterSystem TwistTag.D4.tag) K w *
        d4v K σ 0 0 (c * D₁) (c * E₁) (c * F₁) *
          (canonicalRep (coxeterSystem TwistTag.D4.tag) K w)⁻¹ =
        d4v K σ 0 0 (c * D₂) (c * E₂) (c * F₂) := by
    rcases hn with rfl | rfl
    · refine ⟨D₁, E₁, F₁, hE₁, hF₁, ?_, fun c => ?_⟩ <;>
        rw [canonicalRep_one, one_mul, inv_one, mul_one]
    · exact ⟨D₁, F₁, E₁, hF₁, hE₁, trialityMiddleRep_conj_d4v σ hσ D₁ E₁ F₁,
        fun c => trialityMiddleRep_conj_d4v σ hσ _ _ _⟩
  obtain ⟨D₃, E₃, F₃, -, -, h₃, hl₃⟩ := borel_conj_d4vA_lin σ hσ hb (D := D₂) hE₂ hF₂
  have hg1 := ht
  rw [d4t, d4x₄_eq_d4v σ, e1, h₁, h₂, h₃] at hg1
  have hg1' := d4v_injective σ hg1
  rw [hx₄, e1, hl₁ c hc, hl₂ c, hl₃ c hc, hg1'.2.2.1, hg1'.2.2.2.1, hg1'.2.2.2.2]

end CentT3

section CentreInv

variable {K : Type} [Field K] [CharP K 2] (σ : K ≃+* K) (hσ : ∀ c, σ (σ (σ c)) = c)

include hσ in
theorem coord_conj_d4x₄
    (a b c d e f δ : K) :
    d4x₁ K σ a * d4v K σ b c d e f * d4x₄ K σ δ * (d4x₁ K σ a * d4v K σ b c d e f)⁻¹ =
      d4v K σ 0 0 δ (a * δ + σ (a * δ) + σ (σ (a * δ))) (δ * c + σ (δ * c) + σ (σ (δ * c))) := by
  have e : ∀ x y A : ModGL TwistTag.D4.tag K, x * y * A * (x * y)⁻¹ = x * (y * A * y⁻¹) * x⁻¹ :=
    fun x y A => by group
  rw [e, d4x₄_eq_d4v σ, d4v_conj_d4vA σ hσ, d4x₁_conj_d4vA σ hσ]
  refine d4v_congr σ rfl rfl rfl (by rw [add_zero]) (by rw [zero_mul, add_zero, add_zero])

include hσ in
theorem d4v_commute_imp
    {b c d e f b' c' d' e' f' : K}
    (h : d4v K σ b c d e f * d4v K σ b' c' d' e' f' = d4v K σ b' c' d' e' f' * d4v K σ b c d e f) :
    (d * c' + σ (d * c') + σ (σ (d * c'))) + e * b' =
      (d' * c + σ (d' * c) + σ (σ (d' * c))) + e' * b := by
  rw [d4v_mul σ hσ, d4v_mul σ hσ] at h
  have h5 := (d4v_injective σ h).2.2.2.2
  linear_combination h5

theorem eq_zero_of_trace_d4 {a : K} (h : ∀ δ : K, a * δ + σ (a * δ) + σ (σ (a * δ)) = 0) :
    a = 0 := by
  by_contra ha
  have h1 := h a⁻¹
  rw [mul_inv_cancel₀ ha, map_one, map_one] at h1
  have h3 : (1 : K) + 1 + 1 = 1 := by
    linear_combination (CharTwo.two_eq_zero : (2 : K) = 0)
  rw [h3] at h1
  exact one_ne_zero h1

theorem torus_eq_one_of_sq
    (a : Kˣ) (β : (trialityFixedField K σ.toRingHom)ˣ)
    (h : trialityOuterTorus K σ a * trialityMiddleTorus K σ β *
      (trialityOuterTorus K σ a * trialityMiddleTorus K σ β) = 1) :
    trialityOuterTorus K σ a * trialityMiddleTorus K σ β = 1 := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hp : (a, β) * (a, β) = 1 := by
    apply trialityTorusHom_injective (σ := σ)
    rw [map_mul, trialityTorusHom_apply, h, map_one]
  have hp1 : a * a = 1 := congrArg Prod.fst hp
  have hp2 : β * β = 1 := congrArg Prod.snd hp
  have ha : a = 1 := Units.ext (eq_one_of_mul_self_eq_one_of_two_eq_zero h2
    (by rw [← Units.val_mul, hp1, Units.val_one]))
  have hβ : β = 1 := by
    refine Units.ext (Subtype.ext (eq_one_of_mul_self_eq_one_of_two_eq_zero h2 ?_))
    have h3 := congrArg (fun u : (trialityFixedField K σ.toRingHom)ˣ =>
      ((u : trialityFixedField K σ.toRingHom) : K)) hp2
    simp only [Units.val_mul, Subfield.coe_mul, Units.val_one, Subfield.coe_one] at h3
    exact h3
  rw [← trialityTorusHom_apply, ha, hβ]
  exact map_one _

include hσ in
theorem unip_of_borel_sq
    [Finite K] {w : ModGL TwistTag.D4.tag K}
    (hw : w ∈ graphFixedRootBorel TwistTag.D4 K σ.toRingHom) (hw2 : w * w = 1) :
    ∃ a b c d e f : K, σ b = b ∧ σ e = e ∧ σ f = f ∧ w = d4x₁ K σ a * d4v K σ b c d e f := by
  obtain ⟨a, β, a₁, b₁, c₁, d₁, e₁, f₁, hb₁, he₁, hf₁, hhH, huU, rfl⟩ :=
    exists_borel_coords σ hσ hw
  set h := trialityOuterTorus K σ a * trialityMiddleTorus K σ β with hh
  set u := d4x₁ K σ a₁ * d4v K σ b₁ c₁ d₁ e₁ f₁ with hu
  have hu' : h⁻¹ * u * h * u ∈ graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom := by
    refine mul_mem ?_ huU
    have := (mem_normalizer_iff.1 (graphFixedRootTorus_le_normalizer_graphFixedPosUnipotent
      (inv_mem hhH)) u).1 huU
    rwa [inv_inv] at this
  have h1 : h * h = 1 := by
    have e : (h * u) * (h * u) = (h * h) * (h⁻¹ * u * h * u) := by group
    rw [e] at hw2
    exact (graphFixedRoot_mul_unique (mul_mem hhH hhH) (one_mem _) hu' (one_mem _)
      (by rw [hw2, mul_one])).1
  refine ⟨a₁, b₁, c₁, d₁, e₁, f₁, hb₁, he₁, hf₁, ?_⟩
  rw [hh, torus_eq_one_of_sq σ a β h1, one_mul]

include hσ in
theorem d4v_commute_d4x₆
    (b c d e f c' : K) :
    d4v K σ b c d e f * d4x₆ K c' = d4x₆ K c' * d4v K σ b c d e f := by
  rw [d4x₆_eq_d4v σ, d4v_mul σ hσ, d4v_mul σ hσ]
  refine d4v_congr σ (by ring) (by ring) (by ring) (by ring) ?_
  simp only [mul_zero, zero_mul, map_zero, add_zero, zero_add]
  ring

include hσ in
theorem commute_d4x₆_of_mem
    [Finite K] {u : ModGL TwistTag.D4.tag K}
    (hu : u ∈ graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom) (c : K) :
    u * d4x₆ K c = d4x₆ K c * u := by
  obtain ⟨a, b, c₁, d, e, f, -, -, -, rfl⟩ := exists_d4coord σ (toRingHom_pow_three_d4 σ hσ) hu
  rw [mul_assoc, d4v_commute_d4x₆ σ hσ, ← mul_assoc, (commute_d4x₁_d4x₆ σ a c).eq, mul_assoc]

theorem conj_eq_of_commute_d4 {G : Type*} [Group G] {u x : G} (h : u * x = x * u) :
    u * x * u⁻¹ = x := by
  rw [h, mul_inv_cancel_right]

include hσ in
theorem centre_inv_z
    [Finite K] {w : ModGL TwistTag.D4.tag K} (hw : w ∈ d4C K σ)
    (hwc : ∀ c ∈ d4C K σ, c * d4z K = d4z K * c → w * c = c * w) (hw2 : w * w = 1) :
    ∃ f : K, σ f = f ∧ w = d4x₆ K f := by
  have hσ3 := toRingHom_pow_three_d4 σ hσ
  have hU : ∀ u ∈ graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom, w * u = u * w := fun u hu =>
    hwc u (graphFixedPosUnipotent_le_graphFixedRootGroup _ _ _ hu) (commute_d4x₆_of_mem σ hσ hu 1)
  have hwN : w ∈ normalizer (graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom :
      Set (ModGL TwistTag.D4.tag K)) := by
    rw [mem_normalizer_iff]
    intro u
    constructor
    · intro hu
      rwa [conj_eq_of_commute_d4 (hU u hu)]
    · intro hu
      have h1 := hU _ hu
      have h2 : w * u * w⁻¹ = u := by
        calc w * u * w⁻¹ = w⁻¹ * (w * (w * u * w⁻¹)) := by group
          _ = w⁻¹ * (w * u * w⁻¹ * w) := by rw [h1]
          _ = u := by group
      rwa [h2] at hu
  have hwB : w ∈ graphFixedRootBorel TwistTag.D4 K σ.toRingHom := by
    rw [← graphFixedRootGroup_inf_normalizer_graphFixedPosUnipotent σ.surjective]
    exact mem_inf.2 ⟨hw, hwN⟩
  obtain ⟨a, b, c, d, e, f, hb, he, hf, rfl⟩ := unip_of_borel_sq σ hσ hwB hw2
  have hcw : ∀ {x : ModGL TwistTag.D4.tag K}, x ∈ d4C K σ → x * d4z K = d4z K * x →
      d4x₁ K σ a * d4v K σ b c d e f * x = x * (d4x₁ K σ a * d4v K σ b c d e f) :=
    fun hx hxz => hwc _ hx hxz
  have h4 : ∀ δ : K, (a * δ + σ (a * δ) + σ (σ (a * δ))) = 0 ∧
      (δ * c + σ (δ * c) + σ (σ (δ * c))) = 0 := fun δ => by
    have h := conj_eq_of_commute_d4 (hcw (d4x_short_mem σ hσ3 δ).2.2
      (commute_d4x₄_d4x₆ σ δ 1).eq)
    rw [coord_conj_d4x₄ σ hσ, d4x₄_eq_d4v σ] at h
    have h' := d4v_injective σ h
    exact ⟨h'.2.2.2.1, h'.2.2.2.2⟩
  have ha : a = 0 := eq_zero_of_trace_d4 σ fun δ => (h4 δ).1
  have hc : c = 0 := eq_zero_of_trace_d4 σ fun δ => by rw [mul_comm]; exact (h4 δ).2
  subst ha hc
  simp only [d4x₁_zero, one_mul] at hcw ⊢
  have h5 := hcw (d4x_long_mem σ (map_one σ)).2.1 (commute_d4x₅_d4x₆ K 1 1).eq
  rw [d4x₅_eq_d4v σ] at h5
  have hb0 := d4v_commute_imp σ hσ h5
  simp only [mul_zero, map_zero, add_zero, zero_add, one_mul] at hb0
  have h2 := hcw (d4x_long_mem σ (map_one σ)).1 (commute_d4x₆_d4x₂ K 1 1).eq.symm
  rw [d4x₂_eq_d4v σ] at h2
  have he0 := d4v_commute_imp σ hσ h2
  simp only [mul_zero, zero_mul, map_zero, add_zero, zero_add, mul_one] at he0
  have hd0 : d = 0 := eq_zero_of_trace_d4 σ fun γ => by
    have h := hcw (d4x_short_mem σ hσ3 γ).2.1 (commute_d4x₆_d4x₃ σ 1 γ).eq.symm
    rw [d4x₃_eq_d4v σ] at h
    have h' := d4v_commute_imp σ hσ h
    simpa using h'
  exact ⟨f, hf, by rw [d4x₆_eq_d4v σ, ← hb0, hd0, he0]⟩

include hσ in
theorem d4v_conj_d4v
    (b c d e f B C D E F : K) :
    ∃ F', d4v K σ b c d e f * d4v K σ B C D E F * (d4v K σ b c d e f)⁻¹ = d4v K σ B C D E F' := by
  rw [d4v_inv σ hσ, d4v_mul σ hσ, d4v_mul σ hσ]
  have h : ∀ x y : K, x + y + x = y := fun x y => by rw [add_comm x y, add_assoc, add_self_d4,
    add_zero]
  exact ⟨_, d4v_congr σ (h b B) (h c C) (h d D) (h e E) rfl⟩

include hσ in
theorem borel_conj_d4v_fst
    [Finite K] {b : ModGL TwistTag.D4.tag K}
    (hb : b ∈ graphFixedRootBorel TwistTag.D4 K σ.toRingHom) :
    ∃ μ : K, μ ≠ 0 ∧ ∀ B C D E F : K, σ B = B → ∃ C' D' E' F' : K,
      b * d4v K σ B C D E F * b⁻¹ = d4v K σ (μ * B) C' D' E' F' := by
  obtain ⟨a, β, a₁, b₁, c₁, d₁, e₁, f₁, -, -, -, -, -, rfl⟩ := exists_borel_coords σ hσ hb
  have ha : (a : K) ≠ 0 := a.ne_zero
  have hσa : σ (a : K) ≠ 0 := (map_ne_zero σ).2 ha
  have hσσa : σ (σ (a : K)) ≠ 0 := (map_ne_zero σ).2 hσa
  refine ⟨((a : K) * σ a * σ (σ a))⁻¹ * ((trialityFixedUnit K σ β : Kˣ) : K) ^ 2,
    mul_ne_zero (inv_ne_zero (mul_ne_zero (mul_ne_zero ha hσa) hσσa))
      (pow_ne_zero _ (Units.ne_zero _)), fun B C D E F hB => ?_⟩
  have e : ∀ x y u v A : ModGL TwistTag.D4.tag K, x * y * (u * v) * A * (x * y * (u * v))⁻¹ =
      x * (y * (u * (v * A * v⁻¹) * u⁻¹) * y⁻¹) * x⁻¹ := fun x y u v A => by group
  obtain ⟨F₁, hF₁⟩ := d4v_conj_d4v σ hσ b₁ c₁ d₁ e₁ f₁ B C D E F
  obtain ⟨F₂, hF₂⟩ := d4x₁_conj_d4v σ hσ a₁ B C D E F₁ hB
  rw [e, hF₁, hF₂, hm_conj_d4v, ho_conj_d4v σ hσ]
  exact ⟨_, _, _, _, d4v_congr σ (by ring) rfl rfl rfl rfl⟩

include hσ in
theorem borel_conj_d4x₅
    [Finite K] {b : ModGL TwistTag.D4.tag K}
    (hb : b ∈ graphFixedRootBorel TwistTag.D4 K σ.toRingHom) :
    ∃ ε φ : K, ε ≠ 0 ∧ σ ε = ε ∧ b * d4x₅ K 1 * b⁻¹ = d4v K σ 0 0 0 ε φ := by
  obtain ⟨a, β, a₁, b₁, c₁, d₁, e₁, f₁, -, -, -, -, -, rfl⟩ := exists_borel_coords σ hσ hb
  have hβ : σ ((trialityFixedUnit K σ β : Kˣ) : K) = (trialityFixedUnit K σ β : Kˣ) :=
    sigma_trialityFixedUnit β
  have ha : (a : K) ≠ 0 := a.ne_zero
  have hσa : σ (a : K) ≠ 0 := (map_ne_zero σ).2 ha
  have hσσa : σ (σ (a : K)) ≠ 0 := (map_ne_zero σ).2 hσa
  refine ⟨_, _, ?_, ?_, by rw [d4x₅_eq_d4v σ, borel_conj_d4vA σ hσ, mul_zero]⟩
  · simp only [mul_zero, map_zero, zero_add, add_zero]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero ha hσa) hσσa)
      (mul_ne_zero (inv_ne_zero (Units.ne_zero _)) one_ne_zero)
  · simp only [mul_zero, map_zero, zero_add, add_zero, mul_one, map_mul, map_inv₀, hβ, hσ]
    ring

include hσ in
theorem centre_inv_t
    [Finite K] {w : ModGL TwistTag.D4.tag K} (hw : w ∈ d4C K σ)
    (hwc : ∀ c ∈ d4C K σ, c * d4t K σ = d4t K σ * c → w * c = c * w) (hw2 : w * w = 1) :
    ∃ d : K, σ d = d ∧ w = d4x₄ K σ d := by
  have hσ3 := toRingHom_pow_three_d4 σ hσ
  have h5C := (d4x_long_mem σ (map_one σ)).2.1
  have h5t : d4x₅ K 1 * d4t K σ = d4t K σ * d4x₅ K 1 := (commute_d4x₅_d4x₄ σ 1 1).eq
  have hwz : w * d4z K * w⁻¹ = d4z K := conj_eq_of_commute_d4
    (hwc _ (d4x_long_mem σ (map_one σ)).2.2 (commute_d4x₄_d4x₆ σ 1 1).eq.symm)
  obtain ⟨v, hv, b, hb, b', hb', rfl⟩ := exists_cell_d4 σ hw
  have hθ := (weyl_theta_of_commute σ hσ hb hb' hwz).1
  rcases relWeyl_stab_theta hv hθ with rfl | rfl
  · rw [canonicalRep_one, mul_one] at hw2 hwc ⊢
    obtain ⟨a, b₁, c, d, e, f, hb₁, he, hf, hw'⟩ := unip_of_borel_sq σ hσ (mul_mem hb hb') hw2
    rw [hw'] at hwc ⊢
    have hcw : ∀ {x : ModGL TwistTag.D4.tag K}, x ∈ d4C K σ → x * d4t K σ = d4t K σ * x →
        d4x₁ K σ a * d4v K σ b₁ c d e f * x = x * (d4x₁ K σ a * d4v K σ b₁ c d e f) :=
      fun hx hxt => hwc _ hx hxt
    have h4 : ∀ δ : K, (a * δ + σ (a * δ) + σ (σ (a * δ))) = 0 ∧
        (δ * c + σ (δ * c) + σ (σ (δ * c))) = 0 := fun δ => by
      have h := conj_eq_of_commute_d4 (hcw (d4x_short_mem σ hσ3 δ).2.2
        (by rw [d4t, ← d4x₄_add, ← d4x₄_add, add_comm]))
      rw [coord_conj_d4x₄ σ hσ, d4x₄_eq_d4v σ] at h
      have h' := d4v_injective σ h
      exact ⟨h'.2.2.2.1, h'.2.2.2.2⟩
    have ha : a = 0 := eq_zero_of_trace_d4 σ fun δ => (h4 δ).1
    have hc : c = 0 := eq_zero_of_trace_d4 σ fun δ => by rw [mul_comm]; exact (h4 δ).2
    subst ha hc
    simp only [d4x₁_zero, one_mul] at hcw ⊢
    have h5 := hcw h5C h5t
    rw [d4x₅_eq_d4v σ] at h5
    have hb0 := d4v_commute_imp σ hσ h5
    simp only [mul_zero, map_zero, add_zero, zero_add, one_mul] at hb0
    have h2 := hcw (d4x_long_mem σ (map_one σ)).1 (commute_d4x₄_d4x₂ σ 1 1).eq.symm
    rw [d4x₂_eq_d4v σ] at h2
    have he0 := d4v_commute_imp σ hσ h2
    simp only [mul_zero, zero_mul, map_zero, add_zero, zero_add, mul_one] at he0
    have h3 : ∀ s : K, s + σ s + σ (σ s) = 0 → d * s + σ (d * s) + σ (σ (d * s)) = 0 := by
      intro s hs
      have hst : d4x₃ K σ s * d4t K σ = d4t K σ * d4x₃ K σ s := by
        have hc := comm_d4x₄_d4x₃ σ hσ 1 s
        rw [one_mul, hs, d4x₆_zero, commutatorElement_eq_one_iff_mul_comm] at hc
        exact hc.symm
      have h := hcw (d4x_short_mem σ hσ3 s).2.1 hst
      rw [d4x₃_eq_d4v σ] at h
      have h' := d4v_commute_imp σ hσ h
      simpa using h'
    have hd : σ d = d := by
      have h6 : d + σ (σ d) = 0 := eq_zero_of_trace_d4 σ fun x => by
        have hx := h3 (x + σ x) (by
          rw [map_add, map_add, hσ]
          linear_combination (x + σ x + σ (σ x)) * (CharTwo.two_eq_zero : (2 : K) = 0))
        have e1 : σ (σ d) * x + σ (σ (σ d) * x) + σ (σ (σ (σ d) * x)) =
            d * σ x + σ (d * σ x) + σ (σ (d * σ x)) := by
          simp only [map_mul, hσ]
          ring
        have ex : d * (x + σ x) + σ (d * (x + σ x)) + σ (σ (d * (x + σ x))) =
            (d * x + σ (d * x) + σ (σ (d * x))) + (d * σ x + σ (d * σ x) + σ (σ (d * σ x))) := by
          simp only [mul_add, map_add]
          ring
        have eg : (d + σ (σ d)) * x + σ ((d + σ (σ d)) * x) + σ (σ ((d + σ (σ d)) * x)) =
            (d * x + σ (d * x) + σ (σ (d * x))) +
              (σ (σ d) * x + σ (σ (σ d) * x) + σ (σ (σ (σ d) * x))) := by
          simp only [add_mul, map_add]
          ring
        rw [eg, e1, ← ex]
        exact hx
      have h7 : σ (σ d) = d := by
        linear_combination h6 - d * (CharTwo.two_eq_zero : (2 : K) = 0)
      calc σ d = σ (σ (σ d)) := by rw [h7]
        _ = d := hσ d
    have hna : trialityMiddleRep K * d4t K σ = d4t K σ * trialityMiddleRep K := by
      have h : trialityMiddleRep K * d4t K σ * (trialityMiddleRep K)⁻¹ = d4t K σ :=
        trialityMiddleRep_conj_d4x₄ σ (1 : K)
      calc trialityMiddleRep K * d4t K σ =
          trialityMiddleRep K * d4t K σ * (trialityMiddleRep K)⁻¹ * trialityMiddleRep K := by group
        _ = d4t K σ * trialityMiddleRep K := by rw [h]
    have hn := conj_eq_of_commute_d4 (hcw (trialityRep_mem σ).2 hna).symm
    subst hb0 he0
    rw [trialityMiddleRep_conj_d4v σ hσ] at hn
    have hf0 := (d4v_injective σ hn).2.2.2.1
    exact ⟨d, hd, by rw [d4x₄_eq_d4v σ, hf0]⟩
  · exfalso
    have h5 := conj_eq_of_commute_d4 (hwc _ h5C h5t)
    obtain ⟨ε, φ, hε, hεσ, h₁⟩ := borel_conj_d4x₅ σ hσ hb'
    obtain ⟨μ, hμ, hfst⟩ := borel_conj_d4v_fst σ hσ hb
    have e1 : ∀ x, b * trialityOuterRep K * b' * x * (b * trialityOuterRep K * b')⁻¹ =
        b * (trialityOuterRep K * (b' * x * b'⁻¹) * (trialityOuterRep K)⁻¹) * b⁻¹ := fun x => by
      group
    change b * trialityOuterRep K * b' * d4x₅ K 1 * (b * trialityOuterRep K * b')⁻¹ =
      d4x₅ K 1 at h5
    rw [e1, h₁, trialityOuterRep_conj_d4v σ hσ] at h5
    obtain ⟨C', D', E', F', hC⟩ := hfst ε 0 0 0 _ hεσ
    rw [hC, d4x₅_eq_d4v σ] at h5
    exact mul_ne_zero hμ hε (d4v_injective σ h5).1

end CentreInv

section CentreData

variable {K : Type} [Field K] [CharP K 2] (σ : K ≃+* K) (hσ : ∀ c, σ (σ (σ c)) = c)

omit [CharP K 2] in
theorem mem_d4Zz
    {x : ModGL TwistTag.D4.tag K} :
    x ∈ d4Zz K σ ↔ ∃ c : K, σ c = c ∧ x = d4x₆ K c := by
  constructor
  · intro hx
    induction hx using closure_induction with
    | mem x hx =>
      obtain ⟨c, rfl⟩ := hx
      exact ⟨c, c.2, rfl⟩
    | one => exact ⟨0, map_zero σ, (d4x₆_zero K).symm⟩
    | mul x y _ _ hx hy =>
      obtain ⟨c, hc, rfl⟩ := hx
      obtain ⟨c', hc', rfl⟩ := hy
      exact ⟨c + c', by rw [map_add, hc, hc'], (d4x₆_add K c c').symm⟩
    | inv x _ hx =>
      obtain ⟨c, hc, rfl⟩ := hx
      exact ⟨-c, by rw [map_neg, hc], inv_eq_of_mul_eq_one_right (by
        rw [← d4x₆_add, add_neg_cancel, d4x₆_zero])⟩
  · rintro ⟨c, hc, rfl⟩
    exact subset_closure ⟨⟨c, hc⟩, rfl⟩

omit [CharP K 2] in
theorem mem_d4Zt
    {x : ModGL TwistTag.D4.tag K} :
    x ∈ d4Zt K σ ↔ ∃ c : K, σ c = c ∧ x = d4x₄ K σ c := by
  constructor
  · intro hx
    induction hx using closure_induction with
    | mem x hx =>
      obtain ⟨c, rfl⟩ := hx
      exact ⟨c, c.2, rfl⟩
    | one => exact ⟨0, map_zero σ, (d4x₄_zero σ).symm⟩
    | mul x y _ _ hx hy =>
      obtain ⟨c, hc, rfl⟩ := hx
      obtain ⟨c', hc', rfl⟩ := hy
      exact ⟨c + c', by rw [map_add, hc, hc'], (d4x₄_add σ c c').symm⟩
    | inv x _ hx =>
      obtain ⟨c, hc, rfl⟩ := hx
      exact ⟨-c, by rw [map_neg, hc], inv_eq_of_mul_eq_one_right (by
        rw [← d4x₄_add, add_neg_cancel, d4x₄_zero])⟩
  · rintro ⟨c, hc, rfl⟩
    exact subset_closure ⟨⟨c, hc⟩, rfl⟩

omit [CharP K 2] in
theorem d4x₄_injective
    : Function.Injective (d4x₄ K σ) := fun c c' h => by
  rw [d4x₄_eq_d4v σ, d4x₄_eq_d4v σ] at h
  exact (d4v_injective σ h).2.2.1

omit [CharP K 2] in
theorem card_d4Zz
    : Nat.card (d4Zz K σ) = Nat.card (d4k K σ) := by
  refine (Nat.card_congr (Equiv.ofBijective (fun c : d4k K σ =>
    (⟨d4x₆ K c, mem_d4Zz σ |>.2 ⟨c, c.2, rfl⟩⟩ : d4Zz K σ)) ⟨fun c c' h => ?_, fun x => ?_⟩)).symm
  · exact Subtype.ext (pinnedX_injective _ _ _ (congrArg Subtype.val h))
  · obtain ⟨c, hc, hx⟩ := (mem_d4Zz σ).1 x.2
    exact ⟨⟨c, hc⟩, Subtype.ext hx.symm⟩

omit [CharP K 2] in
theorem card_d4Zt
    : Nat.card (d4Zt K σ) = Nat.card (d4k K σ) := by
  have hset : (d4Zt K σ : Set (ModGL TwistTag.D4.tag K)) =
      Set.range (fun c : d4k K σ => d4x₄ K σ c) := by
    ext x
    simp only [SetLike.mem_coe, mem_d4Zt σ, Set.mem_range]
    constructor
    · rintro ⟨c, hc, rfl⟩
      exact ⟨⟨c, hc⟩, rfl⟩
    · rintro ⟨c, rfl⟩
      exact ⟨c, c.2, rfl⟩
  rw [← SetLike.coe_sort_coe, hset, Nat.card_range_of_injective]
  intro c c' h
  exact Subtype.ext (d4x₄_injective σ h)

include hσ in
theorem conj_d4x₆_of_commute
    [Finite K] {g : ModGL TwistTag.D4.tag K} (hg : g ∈ d4C K σ)
    (hz : g * d4z K * g⁻¹ = d4z K) (c : K) : g * d4x₆ K c * g⁻¹ = d4x₆ K c := by
  obtain ⟨w, -, b, hb, b', hb', rfl⟩ := exists_cell_d4 σ hg
  exact (weyl_theta_of_commute σ hσ hb hb' hz).2 c

theorem commute_of_conj_eq_d4 {G : Type*} [Group G] {g x : G} (h : g * x * g⁻¹ = x) :
    g * x = x * g := by
  calc g * x = g * x * g⁻¹ * g := by group
    _ = x * g := by rw [h]

include hσ in
theorem d4_centreData_z
    [Finite K] {z : ↥(d4C K σ)}
    (hz : (z : ModGL TwistTag.D4.tag K) = d4z K) :
    Exc.CentreData z ((d4Zz K σ).subgroupOf (d4C K σ)) := by
  obtain ⟨z, hzC⟩ := z
  change z = d4z K at hz
  subst hz
  refine Exc.centreData_of_inf hzC ((mem_d4Zz σ).2 ⟨1, map_one σ, rfl⟩) ?_ ?_ ?_ ?_ ?_
  · intro h
    exact one_ne_zero (pinnedX_injective _ _ _ (h.trans (pinnedX_zero _ _ _).symm))
  · intro a ha b hb
    obtain ⟨c, -, rfl⟩ := (mem_d4Zz σ).1 ha
    obtain ⟨c', -, rfl⟩ := (mem_d4Zz σ).1 hb
    rw [← d4x₆_add, ← d4x₆_add, add_comm]
  · intro a ha
    obtain ⟨c, -, rfl⟩ := (mem_d4Zz σ).1 ha
    exact d4x₆_mul_self K c
  · intro a ha g hg hgz
    obtain ⟨c, -, rfl⟩ := (mem_d4Zz σ).1 ha
    exact (commute_of_conj_eq_d4 (conj_d4x₆_of_commute σ hσ hg
      (conj_eq_of_commute_d4 hgz) c)).symm
  · intro w hw _ hwc hw2
    obtain ⟨f, hf, rfl⟩ := centre_inv_z σ hσ hw hwc hw2
    exact (mem_d4Zz σ).2 ⟨f, hf, rfl⟩

include hσ in
theorem d4_centreData_t
    [Finite K] {t : ↥(d4C K σ)}
    (ht : (t : ModGL TwistTag.D4.tag K) = d4t K σ) :
    Exc.CentreData t ((d4Zt K σ).subgroupOf (d4C K σ)) := by
  obtain ⟨t, htC⟩ := t
  change t = d4t K σ at ht
  subst ht
  refine Exc.centreData_of_inf htC ((mem_d4Zt σ).2 ⟨1, map_one σ, rfl⟩) ?_ ?_ ?_ ?_ ?_
  · intro h
    exact one_ne_zero (d4x₄_injective σ (h.trans (d4x₄_zero σ).symm))
  · intro a ha b hb
    obtain ⟨c, -, rfl⟩ := (mem_d4Zt σ).1 ha
    obtain ⟨c', -, rfl⟩ := (mem_d4Zt σ).1 hb
    rw [← d4x₄_add, ← d4x₄_add, add_comm]
  · intro a ha
    obtain ⟨c, -, rfl⟩ := (mem_d4Zt σ).1 ha
    exact d4x₄_mul_self σ c
  · intro a ha g hg hgt
    obtain ⟨c, hc, rfl⟩ := (mem_d4Zt σ).1 ha
    exact (commute_of_conj_eq_d4 (conj_d4x₄_of_commute σ hσ hg
      (conj_eq_of_commute_d4 hgt) hc)).symm
  · intro w hw _ hwc hw2
    obtain ⟨d, hd, rfl⟩ := centre_inv_t σ hσ hw hwc hw2
    exact (mem_d4Zt σ).2 ⟨d, hd, rfl⟩

end CentreData

end CFSG.ComponentClassification.RankTwoExceptional.D4
