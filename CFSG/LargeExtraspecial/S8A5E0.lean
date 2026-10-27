module

public import CFSG.LargeExtraspecial.S8A5D

public section

namespace CFSG.LargeExtraspecial.S8

open Subgroup CFSG.CGT.Timmesfeld75

universe u

variable {Γ : Type u} [Group Γ]

theorem conjSubgroup_inf (g : Γ) (A B : Subgroup Γ) :
    conjSubgroup g (A ⊓ B) = conjSubgroup g A ⊓ conjSubgroup g B :=
  map_inf_eq _ _ _ (MulAut.conj g).injective

theorem conjSubgroup_eq_bot_iff {g : Γ} {A : Subgroup Γ} : conjSubgroup g A = ⊥ ↔ A = ⊥ :=
  map_eq_bot_iff_of_injective _ (MulAut.conj g).injective

theorem conjSubgroup_inv_conj (g : Γ) (A : Subgroup Γ) :
    conjSubgroup g⁻¹ (conjSubgroup g A) = A := by
  rw [← S9.TIX.conjSubgroup_mul, inv_mul_cancel, S9.TIX.conjSubgroup_one]

theorem conjSubgroup_conj_inv (g : Γ) (A : Subgroup Γ) :
    conjSubgroup g (conjSubgroup g⁻¹ A) = A := by
  rw [← S9.TIX.conjSubgroup_mul, mul_inv_cancel, S9.TIX.conjSubgroup_one]

theorem conjSubgroup_sup (g : Γ) (A B : Subgroup Γ) :
    conjSubgroup g (A ⊔ B) = conjSubgroup g A ⊔ conjSubgroup g B :=
  Subgroup.map_sup _ _ _

theorem mem_normalizer_conj_iff {T : Subgroup Γ} {g y : Γ} :
    g * y * g⁻¹ ∈ normalizer (conjSubgroup g T : Set Γ) ↔ y ∈ normalizer (T : Set Γ) := by
  constructor
  · intro h
    have := conj_mem_normalizer_conjSubgroup (x := g⁻¹) h
    rwa [conjSubgroup_inv_conj, show g⁻¹ * (g * y * g⁻¹) * g⁻¹⁻¹ = y by group] at this
  · exact conj_mem_normalizer_conjSubgroup

theorem isTIIn_conjSubgroup {T X : Subgroup Γ} (hT : S9.TIX.IsTIIn T X) (g : Γ) :
    S9.TIX.IsTIIn (conjSubgroup g T) (conjSubgroup g X) := by
  intro c hc hne
  obtain ⟨c', hc', rfl⟩ := hc
  have e : conjSubgroup ((MulAut.conj g).toMonoidHom c') (conjSubgroup g T) =
      conjSubgroup g (conjSubgroup c' T) := by
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [← S9.TIX.conjSubgroup_mul, ← S9.TIX.conjSubgroup_mul,
      show g * c' * g⁻¹ * g = g * c' by group]
  rw [e] at hne ⊢
  rw [← conjSubgroup_inf] at hne
  have hne' : T ⊓ CFSG.CGT.Timmesfeld75.conjSubgroup c' T ≠ ⊥ := fun h =>
    hne (by rw [h]; exact conjSubgroup_eq_bot_iff.mpr rfl)
  rw [hT c' hc' hne']

theorem card_le_two_of_le_zpowers [Finite Γ] {t : Γ} (htt : t * t = 1) {F : Subgroup Γ}
    (hF : F ≤ zpowers t) : Nat.card F ≤ 2 := by
  have h1 := Subgroup.card_le_of_le hF
  rw [Nat.card_zpowers] at h1
  have h2 : orderOf t ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two, htt])
  exact h1.trans (Nat.le_of_dvd (by norm_num) h2)

end CFSG.LargeExtraspecial.S8
