module

public import CFSG.LargeExtraspecial.S4EightRes2
public import CFSG.LargeExtraspecial.S4EightRes

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S4

open Subgroup Module CFSG.LargeExtraspecial.OrthoF2

theorem exists_ne_one_ne {X : Type*} [Group X] [Finite X] {E : Subgroup X}
    (h3 : 3 ≤ Nat.card E) (e₁ : X) : ∃ e₂ ∈ E, e₂ ≠ 1 ∧ e₂ ≠ e₁ := by
  by_contra h
  push Not at h
  have hsub : (E : Set X) ⊆ {1, e₁} := by
    intro e he
    by_cases he1 : e = 1
    · exact Or.inl he1
    · exact Or.inr (h e he he1)
  have h1 : (E : Set X).ncard ≤ ({1, e₁} : Set X).ncard :=
    Set.ncard_le_ncard hsub (Set.toFinite _)
  have h2 : ({1, e₁} : Set X).ncard ≤ 2 :=
    (Set.ncard_insert_le _ _).trans (by rw [Set.ncard_singleton])
  have h3' : Nat.card E = (E : Set X).ncard := Nat.card_coe_set_eq _
  omega

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {β : LinearMap.BilinForm (ZMod 2) V}

omit [FiniteDimensional (ZMod 2) V] in
theorem eq_one_of_commute_c2 (hβ : β.IsAlt) (hnd : β.Nondegenerate) {a d : V}
    (hd : β a d = 0) {P : Subgroup (V ≃ₗ[ZMod 2] V)}
    (hPI : P ≤ TauCeti.BilinForm.isometryGroup β) (hreg : ∀ f ∈ P, f a = a → f = 1)
    {f : V ≃ₗ[ZMod 2] V} (hf : f ∈ P) (hc : spRho hβ hd 1 * f = f * spRho hβ hd 1) : f = 1 :=
  hreg f hf (apply_eq_of_commute_spRho_one hβ hnd hd (hPI hf) hc.symm)

variable (hβ : β.IsAlt) (hnd : β.Nondegenerate) (h4 : finrank (ZMod 2) V = 4) {a : V}
  (ha : a ≠ 0) {E : Subgroup (V ≃ₗ[ZMod 2] V)} (hEU : E ≤ spPointRadical β a)
  (hidx : Nat.card (spPointRadical β a) ≤ 2 * Nat.card E) (hτ : spTransvection β hβ a ∉ E)
include hβ hnd h4 ha hEU hidx hτ

omit hEU hτ in
theorem four_le_card_E : 4 ≤ Nat.card E := by
  rw [card_spPointRadical hβ hnd ha, h4] at hidx
  norm_num at hidx
  omega

omit [FiniteDimensional (ZMod 2) V] h4 hidx hτ in
theorem mul_self_and_comm_E :
    (∀ e ∈ E, e * e = 1) ∧ ∀ e ∈ E, ∀ e' ∈ E, e * e' = e' * e := by
  have := isElementaryAbelian_spPointRadical hβ hnd ha
  refine ⟨fun e he => ?_, fun e he e' he' => ?_⟩
  · have := elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := spPointRadical β a) e (hEU he)
    rwa [pow_two] at this
  · have := (IsMulCommutative.is_comm (M := spPointRadical β a)).comm ⟨e, hEU he⟩ ⟨e', hEU he'⟩
    exact congrArg Subtype.val this

variable {P : Subgroup (V ≃ₗ[ZMod 2] V)} (hPI : P ≤ TauCeti.BilinForm.isometryGroup β)
  (hEP : E ≤ normalizer (P : Set (V ≃ₗ[ZMod 2] V))) (hreg : ∀ f ∈ P, f a = a → f = 1)
include hPI hEP hreg

theorem eq_bot_of_no_typeA
    (hno : ∀ d (hd : β a d = 0), d ∉ (ZMod 2) ∙ a → spRho hβ hd 0 ∉ E) : P = ⊥ := by
  have : Finite V := Module.finite_of_finite (ZMod 2)
  have : Finite (V ≃ₗ[ZMod 2] V) := finite_linearEquiv_of_finite
  obtain ⟨hsq, -⟩ := mul_self_and_comm_E hβ hnd ha hEU
  have hc2 : ∀ e ∈ E, e ≠ 1 → ∀ f ∈ P, e * f = f * e → f = 1 := by
    intro e he he1 f hf hc
    obtain ⟨d, hd, l, rfl⟩ := exists_eq_spRho hβ hnd ha (hEU he)
    have hdn := not_mem_span_of_spRho_mem hβ hd hτ he he1
    rcases zmod2_eq_zero_or_eq_one l with rfl | rfl
    · exact absurd he (hno d hd hdn)
    · exact eq_one_of_commute_c2 hβ hnd hd hPI hreg hf hc
  have h4E := four_le_card_E hβ hnd h4 ha hidx
  obtain ⟨e₁, he₁, h1, -⟩ := exists_ne_one_ne (E := E) (by omega) 1
  obtain ⟨e₂, he₂, h2, h12⟩ := exists_ne_one_ne (E := E) (by omega) e₁
  have h3 : e₁ * e₂ ≠ 1 := by
    intro h
    apply h12
    rw [mul_eq_one_iff_eq_inv.mp h, inv_eq_of_mul_eq_one_right (hsq _ he₂)]
  have hinv : ∀ e ∈ E, e ≠ 1 → ∀ f ∈ P, e * f * e⁻¹ = f⁻¹ := fun e he he1 f hf =>
    conj_eq_inv_of_centralizer (hsq e he) (hEP he) (hc2 e he he1) hf
  rw [eq_bot_iff]
  intro f hf
  exact hc2 _ (mul_mem he₁ he₂) h3 f hf
    (conj_eq_self_of_conj_eq_inv (hinv e₁ he₁ h1) (hinv e₂ he₂ h2) hf)

theorem card_odd_of_four (hPodd : Odd (Nat.card P)) :
    Nat.card P = 1 ∨ Nat.card P = 3 ∨
      (Nat.card P = 9 ∧ ∃ f ∈ P, f a ∉ (ZMod 2) ∙ a ∧ β a (f a) = 0) := by
  have : Finite V := Module.finite_of_finite (ZMod 2)
  have : Finite (V ≃ₗ[ZMod 2] V) := finite_linearEquiv_of_finite
  obtain ⟨hsq, hcommE⟩ := mul_self_and_comm_E hβ hnd ha hEU
  have h4E := four_le_card_E hβ hnd h4 ha hidx
  have hC3 : ∀ e ∈ E, e ≠ 1 →
      Nat.card (P ⊓ centralizer {e} : Subgroup (V ≃ₗ[ZMod 2] V)) ≤ 3 := by
    intro e he he1
    obtain ⟨d, hd, l, rfl⟩ := exists_eq_spRho hβ hnd ha (hEU he)
    exact card_centralizer_le_three hβ hnd h4 ha hd
      (not_mem_span_of_spRho_mem hβ hd hτ he he1) l hreg
  obtain ⟨e₁, he₁, h1, -⟩ := exists_ne_one_ne (E := E) (by omega) 1
  obtain ⟨e₂, he₂, h2, h12⟩ := exists_ne_one_ne (E := E) (by omega) e₁
  obtain ⟨d₁, hd₁, l₁, rfl⟩ := exists_eq_spRho hβ hnd ha (hEU he₁)
  obtain ⟨d₂, hd₂, l₂, rfl⟩ := exists_eq_spRho hβ hnd ha (hEU he₂)
  have hd₁n := not_mem_span_of_spRho_mem hβ hd₁ hτ he₁ h1
  have hd₂n := not_mem_span_of_spRho_mem hβ hd₂ hτ he₂ h2
  have hd12 : β a (d₁ + d₂) = 0 := by rw [map_add, hd₁, hd₂, add_zero]
  have hmul := spRho_mul hβ hd₁ hd₂ l₁ l₂ hd12
  have he₃ : spRho hβ hd12 (l₁ + l₂ + β d₁ d₂) ∈ E := hmul ▸ mul_mem he₁ he₂
  have h3 : spRho hβ hd12 (l₁ + l₂ + β d₁ d₂) ≠ 1 := by
    rw [← hmul]
    intro h
    apply h12
    rw [mul_eq_one_iff_eq_inv.mp h, inv_eq_of_mul_eq_one_right (hsq _ he₂)]
  have hd₃n := not_mem_span_of_spRho_mem hβ hd12 hτ he₃ h3
  have hβ12 : β d₁ d₂ = 1 := beta_eq_one_of_not_mem_span hβ hnd h4 ha hd₁n hd₂n hd₃n hd₁ hd₂
  obtain ⟨x, hxE, hx1, z, hzE, hzc, hxz1⟩ : ∃ x ∈ E, x ≠ 1 ∧ ∃ z ∈ E,
      (∀ f ∈ P, z * f = f * z → f = 1) ∧ x * z ≠ 1 := by
    rcases zmod2_eq_zero_or_eq_one l₁ with hl₁ | hl₁
    · rcases zmod2_eq_zero_or_eq_one l₂ with hl₂ | hl₂
      · have hl : l₁ + l₂ + β d₁ d₂ = 1 := by rw [hl₁, hl₂, hβ12]; decide
        refine ⟨_, he₁, h1, _, he₃, fun f hf hc => ?_, ?_⟩
        · rw [spRho_congr hβ hd12 hd12 rfl rfl hl] at hc
          exact eq_one_of_commute_c2 hβ hnd hd12 hPI hreg hf hc
        · rw [← hmul, ← mul_assoc, hsq _ he₁, one_mul]
          exact h2
      · subst hl₂
        exact ⟨_, he₁, h1, _, he₂, fun f hf hc => eq_one_of_commute_c2 hβ hnd hd₂ hPI hreg hf hc,
          hmul ▸ h3⟩
    · subst hl₁
      refine ⟨_, he₂, h2, _, he₁, fun f hf hc => eq_one_of_commute_c2 hβ hnd hd₁ hPI hreg hf hc,
        ?_⟩
      rw [hcommE _ he₂ _ he₁, hmul]
      exact h3
  have hzinv : ∀ f ∈ P, z * f * z⁻¹ = f⁻¹ := fun f hf =>
    conj_eq_inv_of_centralizer (hsq z hzE) (hEP hzE) hzc hf
  have hle := card_le_mul_of_conj_eq_inv hPodd (hsq x hxE) (hEP hxE) hzinv
  have hc1 := hC3 x hxE hx1
  have hc2 := hC3 (x * z) (mul_mem hxE hzE) hxz1
  have hdv1 : Nat.card (P ⊓ centralizer {x} : Subgroup (V ≃ₗ[ZMod 2] V)) ∣ Nat.card P :=
    Subgroup.card_dvd_of_le inf_le_left
  have hdv2 : Nat.card (P ⊓ centralizer {x * z} : Subgroup (V ≃ₗ[ZMod 2] V)) ∣ Nat.card P :=
    Subgroup.card_dvd_of_le inf_le_left
  have hp1 : 0 < Nat.card (P ⊓ centralizer {x} : Subgroup (V ≃ₗ[ZMod 2] V)) := Nat.card_pos
  have hp2 : 0 < Nat.card (P ⊓ centralizer {x * z} : Subgroup (V ≃ₗ[ZMod 2] V)) := Nat.card_pos
  have hp : 0 < Nat.card P := Nat.card_pos
  obtain ⟨k, hk⟩ := hPodd
  have key : Nat.card P = 1 ∨ Nat.card P = 3 ∨ (Nat.card P = 9 ∧
      Nat.card (P ⊓ centralizer {x} : Subgroup (V ≃ₗ[ZMod 2] V)) = 3) := by
    generalize Nat.card (P ⊓ centralizer {x} : Subgroup (V ≃ₗ[ZMod 2] V)) = c₁ at *
    generalize Nat.card (P ⊓ centralizer {x * z} : Subgroup (V ≃ₗ[ZMod 2] V)) = c₂ at *
    generalize Nat.card P = p at *
    interval_cases c₁ <;> interval_cases c₂ <;> omega
  rcases key with h | h | ⟨h9, hC⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  refine Or.inr (Or.inr ⟨h9, ?_⟩)
  have hne : (P ⊓ centralizer {x} : Subgroup (V ≃ₗ[ZMod 2] V)) ≠ ⊥ := by
    intro hbot
    rw [hbot, card_bot] at hC
    omega
  obtain ⟨⟨f, hf⟩, hf1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hne
  have hf1' : f ≠ 1 := fun h => hf1 (Subtype.ext h)
  obtain ⟨hfP, hfC⟩ := mem_inf.mp hf
  have hcx := mem_centralizer_singleton_iff.mp hfC
  obtain ⟨d, hd, l, rfl⟩ := exists_eq_spRho hβ hnd ha (hEU hxE)
  have hdn := not_mem_span_of_spRho_mem hβ hd hτ hxE hx1
  have hea : spRho hβ hd l a = a := (spRho_mem_spPointRadical hβ hd l).2.1
  have hfix : spRho hβ hd l (f a) = f a := by
    have := congrArg (fun w : V ≃ₗ[ZMod 2] V => w a) hcx
    simp only [LinearEquiv.mul_apply, hea] at this
    exact this.symm
  obtain ⟨hfa, -⟩ := beta_eq_zero_of_spRho_apply_eq hβ hd ha hdn hfix
  refine ⟨f, hfP, fun hmem => ?_, by rw [isAlt_symm hβ]; exact hfa⟩
  rcases mem_span_singleton_iff.mp hmem with h0 | h0
  · exact ha (f.map_eq_zero_iff.mp h0)
  · exact hf1' (hreg f hfP h0)

end CFSG.LargeExtraspecial.S4
