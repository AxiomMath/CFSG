module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsLiftCert

public section

namespace CFSG.ComponentClassification.GrSLit.L34Facts

open CFSG Subgroup CFSG.PSL3Four CFSG.ComponentClassification.PSL3Four

@[expose] def IsVFour (ρ : Equiv.Perm (Fin 42)) : Prop := ρ = 1 ∨ ρ = r₂ ∨ ρ = r₃ ∨ ρ = r₄

theorem r₄_eq : r₄ = r₂ * r₃ := rfl

theorem r₃_mul_r₂ : r₃ * r₂ = r₄ := by rw [r₄_eq, r₂_mul_r₃]

theorem r₂_mul_r₄ : r₂ * r₄ = r₃ := by
  rw [r₄_eq, ← mul_assoc, r₂_mul_self, one_mul]

theorem r₄_mul_r₂ :
    r₄ * r₂ = r₃ := by
  rw [r₄_eq, mul_assoc, ← r₂_mul_r₃, ← mul_assoc, r₂_mul_self, one_mul]

theorem r₃_mul_r₄ :
    r₃ * r₄ = r₂ := by
  rw [r₄_eq, ← mul_assoc, ← r₂_mul_r₃, mul_assoc, r₃_mul_self, mul_one]

theorem r₄_mul_r₃ : r₄ * r₃ = r₂ := by
  rw [r₄_eq, mul_assoc, r₃_mul_self, mul_one]

theorem IsVFour.mul
    {a b : Equiv.Perm (Fin 42)} (ha : IsVFour a) (hb : IsVFour b) : IsVFour (a * b) := by
  unfold IsVFour at ha hb ⊢
  rcases ha with rfl | rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl | rfl <;>
    simp only [one_mul, mul_one, r₂_mul_self, r₃_mul_self, r₄_mul_self, ← r₄_eq, r₃_mul_r₂,
      r₂_mul_r₄, r₄_mul_r₂, r₃_mul_r₄, r₄_mul_r₃, true_or, or_true]

theorem IsVFour.mul_self {a : Equiv.Perm (Fin 42)} (ha : IsVFour a) :
    a * a = 1 := by
  rcases ha with rfl | rfl | rfl | rfl
  · exact mul_one 1
  · exact r₂_mul_self
  · exact r₃_mul_self
  · exact r₄_mul_self

theorem IsVFour.inv {a : Equiv.Perm (Fin 42)} (ha : IsVFour a) :
    a⁻¹ = a :=
  inv_eq_of_mul_eq_one_right ha.mul_self

theorem IsVFour.mem_R {a : Equiv.Perm (Fin 42)} (ha : IsVFour a) : a ∈ R := by
  rcases ha with rfl | rfl | rfl | rfl
  exacts [R.one_mem, r₂_mem_R, r₃_mem_R, r₄_mem_R]

theorem IsVFour.eq_one_of_mem_S {a : Equiv.Perm (Fin 42)}
    (ha : IsVFour a) (haS : a ∈ S) : a = 1 := by
  rcases ha with rfl | rfl | rfl | rfl
  · rfl
  · exact absurd haS not_mem_S_r₂
  · exact absurd haS not_mem_S_r₃
  · exact absurd haS not_mem_S_r₄

theorem IsVFour.conj_mem_T0
    {a : Equiv.Perm (Fin 42)}
    (ha : IsVFour a) {t : Equiv.Perm (Fin 42)} (ht : t ∈ T0) : a * t * a⁻¹ ∈ T0 := by
  obtain ⟨h₂, h₃⟩ := conj_r_mem_T0
  rcases ha with rfl | rfl | rfl | rfl
  · simpa using ht
  · exact h₂ t ht
  · exact h₃ t ht
  · have := h₂ _ (h₃ t ht)
    rwa [show r₂ * (r₃ * t * r₃⁻¹) * r₂⁻¹ = r₂ * r₃ * t * (r₂ * r₃)⁻¹ by group, ← r₄_eq]
      at this

@[expose] def Sigma0 :
    Subgroup (Equiv.Perm (Fin 42)) where
  carrier := {g | ∃ t ∈ T0, ∃ ρ, IsVFour ρ ∧ g = t * ρ}
  mul_mem' := by
    rintro _ _ ⟨t, ht, ρ, hρ, rfl⟩ ⟨t', ht', ρ', hρ', rfl⟩
    refine ⟨t * (ρ * t' * ρ⁻¹), T0.mul_mem ht (hρ.conj_mem_T0 ht'), ρ * ρ', hρ.mul hρ', ?_⟩
    group
  one_mem' := ⟨1, T0.one_mem, 1, Or.inl rfl, (mul_one 1).symm⟩
  inv_mem' := by
    rintro _ ⟨t, ht, ρ, hρ, rfl⟩
    have hρ' : IsVFour ρ⁻¹ := by rw [hρ.inv]; exact hρ
    exact ⟨ρ⁻¹ * t⁻¹ * ρ⁻¹⁻¹, hρ'.conj_mem_T0 (T0.inv_mem ht), ρ⁻¹, hρ', by group⟩

theorem mem_Sigma0
    {g : Equiv.Perm (Fin 42)} :
    g ∈ Sigma0 ↔ ∃ t ∈ T0, ∃ ρ, IsVFour ρ ∧ g = t * ρ :=
  Iff.rfl

theorem Sigma0_le_R :
    Sigma0 ≤ R := by
  rintro _ ⟨t, ht, ρ, hρ, rfl⟩
  exact R.mul_mem (S_le_R (T0_le_S ht)) hρ.mem_R

theorem mem_T0_of_mem_Sigma0
    {g : Equiv.Perm (Fin 42)}
    (hg : g ∈ Sigma0) (hgS : g ∈ S) : g ∈ T0 := by
  obtain ⟨t, ht, ρ, hρ, rfl⟩ := hg
  have hρS : ρ ∈ S := by
    have := S.mul_mem (S.inv_mem (T0_le_S ht)) hgS
    rwa [inv_mul_cancel_left] at this
  rw [hρ.eq_one_of_mem_S hρS, mul_one]
  exact ht

@[expose] def vFourEl (i : Fin 4) : Equiv.Perm (Fin 42) := ![1, r₂, r₃, r₄] i

theorem isVFour_vFourEl (i : Fin 4) : IsVFour (vFourEl i) := by
  fin_cases i
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr (Or.inl rfl))
  · exact Or.inr (Or.inr (Or.inr rfl))

theorem exists_vFourEl {ρ : Equiv.Perm (Fin 42)} (hρ : IsVFour ρ) : ∃ i, vFourEl i = ρ := by
  rcases hρ with rfl | rfl | rfl | rfl
  exacts [⟨0, rfl⟩, ⟨1, rfl⟩, ⟨2, rfl⟩, ⟨3, rfl⟩]

theorem one_ne_r₂ : (1 : Equiv.Perm (Fin 42)) ≠ r₂ :=
  fun h => not_mem_S_r₂ (h ▸ S.one_mem)

theorem one_ne_r₃ : (1 : Equiv.Perm (Fin 42)) ≠ r₃ :=
  fun h => not_mem_S_r₃ (h ▸ S.one_mem)

theorem one_ne_r₄ : (1 : Equiv.Perm (Fin 42)) ≠ r₄ :=
  fun h => not_mem_S_r₄ (h ▸ S.one_mem)

theorem r₂_ne_r₃ : r₂ ≠ r₃ := fun h =>
  not_mem_S_r₄ (by rw [r₄_eq, ← h, r₂_mul_self]; exact S.one_mem)

theorem r₂_ne_r₄ : r₂ ≠ r₄ := fun h =>
  not_mem_S_r₃ (by rw [← r₂_mul_r₄, ← h, r₂_mul_self]; exact S.one_mem)

theorem r₃_ne_r₄ : r₃ ≠ r₄ :=
  fun h => not_mem_S_r₂ (by rw [← r₃_mul_r₄, ← h, r₃_mul_self]; exact S.one_mem)

theorem vFourEl_injective :
    Function.Injective vFourEl := by
  intro i j h
  fin_cases i <;> fin_cases j
  all_goals first
    | rfl
    | exact absurd (show (1 : Equiv.Perm (Fin 42)) = r₂ from h) one_ne_r₂
    | exact absurd (show (1 : Equiv.Perm (Fin 42)) = r₃ from h) one_ne_r₃
    | exact absurd (show (1 : Equiv.Perm (Fin 42)) = r₄ from h) one_ne_r₄
    | exact absurd (show r₂ = 1 from h).symm one_ne_r₂
    | exact absurd (show r₃ = 1 from h).symm one_ne_r₃
    | exact absurd (show r₄ = 1 from h).symm one_ne_r₄
    | exact absurd (show r₂ = r₃ from h) r₂_ne_r₃
    | exact absurd (show r₂ = r₄ from h) r₂_ne_r₄
    | exact absurd (show r₃ = r₄ from h) r₃_ne_r₄
    | exact absurd (show r₃ = r₂ from h).symm r₂_ne_r₃
    | exact absurd (show r₄ = r₂ from h).symm r₂_ne_r₄
    | exact absurd (show r₄ = r₃ from h).symm r₃_ne_r₄

theorem card_Sigma0 :
    Nat.card Sigma0 = 256 := by
  let f : ↥T0 × Fin 4 → ↥Sigma0 := fun x =>
    ⟨(x.1 : Equiv.Perm (Fin 42)) * vFourEl x.2, x.1, x.1.2, vFourEl x.2, isVFour_vFourEl x.2, rfl⟩
  have hf : Function.Bijective f := by
    constructor
    · rintro ⟨t, i⟩ ⟨t', j⟩ h
      have h1 : (t : Equiv.Perm (Fin 42)) * vFourEl i = t' * vFourEl j := congrArg Subtype.val h
      have h2 : vFourEl j * (vFourEl i)⁻¹ ∈ S := by
        have : (t' : Equiv.Perm (Fin 42))⁻¹ * t = vFourEl j * (vFourEl i)⁻¹ := by
          rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, ← h1]; group
        rw [← this]
        exact S.mul_mem (S.inv_mem (T0_le_S t'.2)) (T0_le_S t.2)
      have hVi : IsVFour (vFourEl i)⁻¹ := by rw [(isVFour_vFourEl i).inv]; exact isVFour_vFourEl i
      have h3 := ((isVFour_vFourEl j).mul hVi).eq_one_of_mem_S h2
      have hij : vFourEl j = vFourEl i := mul_inv_eq_one.mp h3
      have hji := vFourEl_injective hij
      subst hji
      have : (t : Equiv.Perm (Fin 42)) = t' := mul_right_cancel h1
      exact Prod.ext (Subtype.ext this) rfl
    · rintro ⟨g, t, ht, ρ, hρ, rfl⟩
      obtain ⟨i, rfl⟩ := exists_vFourEl hρ
      exact ⟨(⟨t, ht⟩, i), rfl⟩
  rw [← Nat.card_congr (Equiv.ofBijective f hf), Nat.card_prod, card_T0,
    Nat.card_eq_fintype_card (α := Fin 4), Fintype.card_fin]

theorem card_Sigma0_subgroupOf :
    Nat.card (Sigma0.subgroupOf R) = 256 := by
  rw [Nat.card_congr (subgroupOfEquivOfLe Sigma0_le_R).toEquiv, card_Sigma0]

theorem isPGroup_Sigma0 :
    IsPGroup 2 (Sigma0.subgroupOf R) :=
  IsPGroup.of_card (n := 8) (by rw [card_Sigma0_subgroupOf]; norm_num)

theorem not_two_dvd_index_Sigma0 :
    ¬ 2 ∣ (Sigma0.subgroupOf R).index := by
  have h := Subgroup.card_mul_index (Sigma0.subgroupOf R)
  rw [card_Sigma0_subgroupOf, card_R] at h
  have h945 : (Sigma0.subgroupOf R).index = 945 := by omega
  rw [h945]
  decide

end CFSG.ComponentClassification.GrSLit.L34Facts
