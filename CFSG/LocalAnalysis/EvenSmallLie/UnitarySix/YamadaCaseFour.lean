module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaOmega
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaSocle
public import CFSG.LocalAnalysis.EvenSmallLie.CatalogOrders

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.EvenSmallLie.UnitarySix.Yamada

open Subgroup CFSG.Sporadic.Schreier
open SolomonWong (mul_comm_of_sq_eq_one)
open scoped Pointwise

section G

variable {G : Type} [Group G] {L : Subgroup G}

@[expose] def omegaConj (D : ToddParabolic L) (t : G) (x : normalizer (toddE D t : Set G)) :
    Equiv.Perm (omegaSet D t) where
  toFun ω := ⟨x * ω * (x : G)⁻¹, conj_mem_conjOrbit' x.2 ω.2⟩
  invFun ω := ⟨(x : G)⁻¹ * ω * x, conj_mem_conjOrbit x.2 ω.2⟩
  left_inv ω := Subtype.ext (by simp [mul_assoc])
  right_inv ω := Subtype.ext (by simp [mul_assoc])

@[expose] def omegaPerm (D : ToddParabolic L) (t : G) :
    normalizer (toddE D t : Set G) →* Equiv.Perm (omegaSet D t) where
  toFun := omegaConj D t
  map_one' := Equiv.ext fun ω => Subtype.ext (by simp [omegaConj])
  map_mul' x y := Equiv.ext fun ω => Subtype.ext (by simp [omegaConj, mul_assoc])

theorem omegaPerm_apply (D : ToddParabolic L) (t : G) (x : normalizer (toddE D t : Set G))
    (ω : omegaSet D t) : ((omegaPerm D t x ω : omegaSet D t) : G) = x * ω * (x : G)⁻¹ := rfl

theorem isPretransitive_omegaPerm (D : ToddParabolic L) (t : G) :
    MulAction.IsPretransitive (omegaPerm D t).range (omegaSet D t) := by
  refine ⟨fun ω₁ ω₂ => ?_⟩
  obtain ⟨n₁, hn₁, e₁⟩ := ω₁.2
  obtain ⟨n₂, hn₂, e₂⟩ := ω₂.2
  refine ⟨⟨omegaPerm D t ⟨n₂⁻¹ * n₁, mul_mem (inv_mem hn₂) hn₁⟩, MonoidHom.mem_range.2 ⟨_, rfl⟩⟩,
    Subtype.ext ?_⟩
  change n₂⁻¹ * n₁ * (ω₁ : G) * (n₂⁻¹ * n₁)⁻¹ = ω₂
  rw [← e₁, ← e₂]
  group

theorem not_isPrimePow_561 : ¬ IsPrimePow 561 := by
  rw [isPrimePow_iff_unique_prime_dvd]
  rintro ⟨p, -, hp⟩
  have h3 := hp 3 ⟨Nat.prime_three, by norm_num⟩
  have h17 := hp 17 ⟨by norm_num, by norm_num⟩
  omega

end G

namespace Setting

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {D : ToddParabolic L} {t : G}

theorem mem_omega_case_iv (h : Setting G L D t)
    (hΩ : ∀ e ∈ toddE D t, e ∈ omegaSet D t ↔
      (e = t ∨ e ∈ conjClass (toddK D) (D.a₃ : G) ∨ e ∈ conjClass (toddK D) ((D.a₃ : G) * t))) :
    (D.a₃ : G) ∈ omegaSet D t ∧ (D.a₃ : G) * t ∈ omegaSet D t ∧
      (D.a₁ : G) * t ∉ omegaSet D t ∧ (D.a₂ : G) * t ∉ omegaSet D t := by
  obtain ⟨o₁, o₂, -⟩ := a_ne_one D (G := G)
  obtain ⟨-, d₁₃, d₂₃⟩ := a_not_mem_delta D (G := G)
  obtain ⟨m₁, m₂, m₃⟩ := D.a_mem
  have mA : ∀ a : L, a ∈ D.A → (a : G) ∈ toddA D := fun a ha => ⟨a, ha, rfl⟩
  have hE : ∀ a : L, a ∈ D.A → (a : G) * t ∈ toddE D t := fun a ha =>
    mul_mem (toddA_le_toddE D t (mA a ha)) (t_mem_toddE D t)
  have key : ∀ a : L, a ∈ D.A → (a : G) ≠ 1 → (D.a₃ : G) ∉ conjClass (toddK D) (a : G) →
      (a : G) * t ∉ omegaSet D t := by
    intro a ha ha1 ha3 hat
    rcases (hΩ _ (hE a ha)).1 hat with h1 | h1 | h1
    · exact ha1 (mul_eq_right.1 h1)
    · apply h.t_not_mem
      have h2 := mul_mem (inv_mem (mA a ha)) (conjClass_toddK_subset D m₃ h1)
      rw [inv_mul_cancel_left] at h2
      exact toddA_le D h2
    · rw [h.conjClass_mul_t] at h1
      obtain ⟨c, hc, hct⟩ := h1
      rw [mul_left_injective t hct] at hc
      apply ha3
      rw [conjClass_eq_of_mem hc]
      exact self_mem_conjClass _ _
  exact ⟨(hΩ _ (toddA_le_toddE D t (mA _ m₃))).2 (Or.inr (Or.inl (self_mem_conjClass _ _))),
    (hΩ _ (hE _ m₃)).2 (Or.inr (Or.inr (self_mem_conjClass _ _))), key _ m₁ o₁ d₁₃,
    key _ m₂ o₂ d₂₃⟩

open Classical in
theorem ncard_of_subset_omega (h : Setting G L D t)
    (hΩ : ∀ e ∈ toddE D t, e ∈ omegaSet D t ↔
      (e = t ∨ e ∈ conjClass (toddK D) (D.a₃ : G) ∨ e ∈ conjClass (toddK D) ((D.a₃ : G) * t)))
    {S : Set G} (hS : S ⊆ omegaSet D t) (hinv : ∀ c ∈ toddK D, ∀ y ∈ S, c * y * c⁻¹ ∈ S)
    (ht : t ∈ S) :
    S.ncard = 1 + (if (D.a₃ : G) ∈ S then 280 else 0) +
      (if (D.a₃ : G) * t ∈ S then 280 else 0) := by
  obtain ⟨-, -, n₁, n₂⟩ := h.mem_omega_case_iv hΩ
  rw [h.ncard_eq_of_invariant (hS.trans omegaSet_subset) hinv]
  have k0 : (1 : G) ∉ S := fun h1 => h.one_not_mem_omega (hS h1)
  have k1 : (D.a₁ : G) ∉ S := fun h1 => h.a₁_not_mem_omega (hS h1)
  have k2 : (D.a₂ : G) ∉ S := fun h1 => h.a₂_not_mem_omega (hS h1)
  have k5 : (D.a₁ : G) * t ∉ S := fun h1 => n₁ (hS h1)
  have k6 : (D.a₂ : G) * t ∉ S := fun h1 => n₂ (hS h1)
  simp only [k0, k1, k2, k5, k6, ht, ite_false, ite_true]
  ring

theorem ncard_omega_case_iv (h : Setting G L D t)
    (hΩ : ∀ e ∈ toddE D t, e ∈ omegaSet D t ↔
      (e = t ∨ e ∈ conjClass (toddK D) (D.a₃ : G) ∨ e ∈ conjClass (toddK D) ((D.a₃ : G) * t))) :
    (omegaSet D t).ncard = 561 := by
  obtain ⟨m₃, m₃t, -, -⟩ := h.mem_omega_case_iv hΩ
  rw [h.ncard_of_subset_omega hΩ subset_rfl h.omega_invariant t_mem_omega]
  simp [m₃, m₃t]

theorem omegaPerm_eq_one (h : Setting G L D t) (x : normalizer (toddE D t : Set G))
    (hx : (x : G) ∈ toddE D t) : omegaPerm D t x = 1 := by
  refine Equiv.ext fun ω => Subtype.ext ?_
  rw [omegaPerm_apply, Equiv.Perm.one_apply,
    mul_comm_of_sq_eq_one h.toddE_sq hx (omegaSet_subset ω.2), mul_inv_cancel_right]

theorem card_range_omegaPerm_dvd (h : Setting G L D t) (hΩ : (omegaSet D t).ncard = 561) :
    Nat.card (omegaPerm D t).range ∣ 2 ^ 7 * 3 ^ 4 * 5 * 7 * 11 * 17 := by
  have hX := h.ncard_omega_mul
  rw [hΩ] at hX
  have hker : 2 ^ 10 ∣ Nat.card (omegaPerm D t).ker := by
    have hle : (toddE D t).subgroupOf (normalizer (toddE D t : Set G)) ≤ (omegaPerm D t).ker :=
      fun x hx => h.omegaPerm_eq_one x hx
    have hc : Nat.card ((toddE D t).subgroupOf (normalizer (toddE D t : Set G))) = 2 ^ 10 := by
      rw [← h.card_toddE]
      exact Nat.card_congr (subgroupOfEquivOfLe le_normalizer).toEquiv
    rw [← hc]
    exact Subgroup.card_dvd_of_le hle
  obtain ⟨k, hk⟩ := hker
  have hXc := card_eq_card_ker_mul_card_range' (omegaPerm D t)
  have h1 : 2 ^ 10 * (k * Nat.card (omegaPerm D t).range) ∣
      2 ^ 10 * (2 ^ 7 * 3 ^ 4 * 5 * 7 * 11 * 17) := by
    rw [show 2 ^ 10 * (k * Nat.card (omegaPerm D t).range) = Nat.card (omegaPerm D t).ker *
      Nat.card (omegaPerm D t).range by rw [hk, mul_assoc], ← hXc, ← hX,
      show 2 ^ 10 * (2 ^ 7 * 3 ^ 4 * 5 * 7 * 11 * 17) = 561 * (2 ^ 10 * 20160 * 6) by norm_num]
    exact Nat.mul_dvd_mul_left 561 h.card_NHA.2
  exact (Dvd.intro_left k rfl).trans (Nat.dvd_of_mul_dvd_mul_left (by norm_num) h1)

theorem isPreprimitive_case_iv (h : Setting G L D t)
    (hΩ : ∀ e ∈ toddE D t, e ∈ omegaSet D t ↔
      (e = t ∨ e ∈ conjClass (toddK D) (D.a₃ : G) ∨ e ∈ conjClass (toddK D) ((D.a₃ : G) * t))) :
    MulAction.IsPreprimitive (omegaPerm D t).range (omegaSet D t) := by
  have := isPretransitive_omegaPerm D t
  have hcard : Nat.card (omegaSet D t) = 561 := by
    rw [Nat.card_coe_set_eq, h.ncard_omega_case_iv hΩ]
  refine MulAction.IsPreprimitive.of_isTrivialBlock_base (⟨t, t_mem_omega⟩ : omegaSet D t) ?_
  intro B htB hB
  have hSΩ : Subtype.val '' B ⊆ omegaSet D t := by
    rintro _ ⟨ω, -, rfl⟩
    exact ω.2
  have hinv : ∀ c ∈ toddK D, ∀ y ∈ Subtype.val '' B, c * y * c⁻¹ ∈ Subtype.val '' B := by
    rintro c hc _ ⟨ω, hω, rfl⟩
    set g : (omegaPerm D t).range :=
      ⟨omegaPerm D t ⟨c, h.toddK_le_X hc⟩, MonoidHom.mem_range.2 ⟨_, rfl⟩⟩
    have hgt : g ∈ MulAction.stabilizer (omegaPerm D t).range
        (⟨t, t_mem_omega⟩ : omegaSet D t) := by
      rw [MulAction.mem_stabilizer_iff]
      apply Subtype.ext
      change c * t * c⁻¹ = t
      rw [h.comm_toddK hc, mul_inv_cancel_right]
    have hgB := hB.stabilizer_le htB hgt
    rw [MulAction.mem_stabilizer_iff] at hgB
    refine ⟨g • ω, ?_, rfl⟩
    rw [← hgB]
    exact Set.smul_mem_smul_set hω
  have hS := h.ncard_of_subset_omega hΩ hSΩ hinv ⟨_, htB, rfl⟩
  rw [Set.ncard_image_of_injective _ Subtype.val_injective] at hS
  have hdvd : B.ncard ∣ 561 := hcard ▸ hB.ncard_dvd_card ⟨_, htB⟩
  have hB1 : B.ncard = 1 ∨ B.ncard = 561 := by
    rw [hS] at hdvd ⊢
    split_ifs at hdvd ⊢ <;> omega
  rcases hB1 with h1 | h1
  · exact Or.inl (Set.ncard_le_one_iff_subsingleton.1 h1.le)
  · exact Or.inr ((Set.eq_univ_iff_ncard B).2 (h1.trans hcard.symm))

theorem normalizer_toddE_ne_top (h : Setting G L D t) :
    normalizer (toddE D t : Set G) ≠ ⊤ := by
  intro htop
  have := h.std.simple
  have : (toddE D t).Normal := normalizer_eq_top_iff.1 htop
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (toddE D t) with hb | ht
  · exact h.t_ne_one ((Subgroup.mem_bot).1 (hb ▸ t_mem_toddE D t))
  · obtain ⟨a, b, hab⟩ := h.std.nonab
    exact hab (mul_comm_of_sq_eq_one h.toddE_sq (ht ▸ mem_top a) (ht ▸ mem_top b))

theorem not_case_iv
    (h : Setting G L D t)
    (hΩ : ∀ e ∈ toddE D t, e ∈ omegaSet D t ↔
      (e = t ∨ e ∈ conjClass (toddK D) (D.a₃ : G) ∨ e ∈ conjClass (toddK D) ((D.a₃ : G) * t))) :
    False := by
  have hcard : Nat.card (omegaSet D t) = 561 := by
    rw [Nat.card_coe_set_eq, h.ncard_omega_case_iv hΩ]
  have := h.isPreprimitive_case_iv hΩ
  have hdvd := h.card_range_omegaPerm_dvd (h.ncard_omega_case_iv hΩ)
  have : Nonempty (omegaSet D t) := ⟨⟨t, t_mem_omega⟩⟩
  obtain ⟨T, -, hTs, hnonab, hΩT, -, -⟩ := exists_simple_normal_of_isPreprimitive
    (X := (omegaPerm D t).range) (Ω := omegaSet D t) (by norm_num : Nat.Prime 17)
    (by rw [hcard]; norm_num) (fun h2 => absurd (h2.trans hdvd) (by norm_num))
    (by rw [hcard]; exact not_isPrimePow_561)
  have hcat := CatalogOrders.catalog_of_kProper_of_le_quotient h.std.kProper
    h.normalizer_toddE_ne_top (omegaPerm D t).rangeRestrict
    (omegaPerm D t).rangeRestrict_surjective T hnonab
  exact CatalogOrders.c3_false hcat hnonab ((Subgroup.card_subgroup_dvd_card T).trans hdvd)
    ((show 11 * 17 ∣ 561 by norm_num).trans (hcard ▸ hΩT))

end Setting

end CFSG.EvenSmallLie.UnitarySix.Yamada
