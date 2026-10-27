module

public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.GH74.GLS.C3.Layer1.Bk

open Equiv Equiv.Perm Subgroup

@[expose] def a5V : Fin 4 → Perm (Fin 5) :=
  ![1, swap 0 1 * swap 2 3, swap 0 2 * swap 1 3, swap 0 3 * swap 1 2]

theorem a5V_mul : ∀ i j : Fin 4, ∃ k : Fin 4, a5V i * a5V j = a5V k := by decide +kernel

theorem a5V_inv : ∀ i : Fin 4, ∃ k : Fin 4, (a5V i)⁻¹ = a5V k := by decide +kernel

theorem a5V_sign : ∀ i : Fin 4, sign (a5V i) = 1 := by decide +kernel

theorem a5V_injective : Function.Injective a5V := by decide +kernel

@[expose] def a5Sub : Subgroup (alternatingGroup (Fin 5)) where
  carrier := {x | ∃ i, a5V i = x.1}
  mul_mem' := by
    rintro x y ⟨i, hi⟩ ⟨j, hj⟩
    obtain ⟨k, hk⟩ := a5V_mul i j
    exact ⟨k, by rw [← hk, hi, hj]; rfl⟩
  one_mem' := ⟨0, rfl⟩
  inv_mem' := by
    rintro x ⟨i, hi⟩
    obtain ⟨k, hk⟩ := a5V_inv i
    exact ⟨k, by rw [← hk, hi]; rfl⟩

theorem card_a5Sub : Nat.card a5Sub = 4 := by
  let e : Fin 4 ≃ a5Sub := Equiv.ofBijective
    (fun i => ⟨⟨a5V i, (mem_alternatingGroup).2 (a5V_sign i)⟩, i, rfl⟩)
    ⟨fun i j h => a5V_injective (congrArg (fun x => x.1.1) h),
      fun ⟨_, i, hi⟩ => ⟨i, Subtype.ext (Subtype.ext hi)⟩⟩
  rw [← Nat.card_congr e, Nat.card_fin]

theorem a5V_centralizer : ∀ σ : Perm (Fin 5), (∀ i : Fin 4, σ * a5V i = a5V i * σ) →
    ∃ i : Fin 4, σ = a5V i := by decide +kernel

theorem exists_conj_model5 {X : Subgroup (alternatingGroup (Fin 5))} (hX : Nat.card ↥X = 4) :
    ∃ c : alternatingGroup (Fin 5), (∀ y ∈ a5Sub, c * y * c⁻¹ ∈ X) ∧
      (∀ x ∈ X, c⁻¹ * x * c ∈ a5Sub) := by
  have hA : Nat.card (alternatingGroup (Fin 5)) = 60 := by
    rw [Nat.card_eq_fintype_card, card_alternatingGroup]
    simp [Nat.factorial]
  have hsyl : ∀ Y : Subgroup (alternatingGroup (Fin 5)), Nat.card ↥Y = 4 →
      Nat.card ↥Y = 2 ^ (Nat.card (alternatingGroup (Fin 5))).factorization 2 := by
    intro Y hY
    have h60 : (60 : ℕ).factorization 2 = 2 := by
      have h : (60 : ℕ) = 2 ^ 2 * 15 := by norm_num
      rw [h, Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
        Nat.Prime.factorization_pow Nat.prime_two, Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
      simp
    rw [hY, hA, h60]
    norm_num
  let SY : Sylow 2 (alternatingGroup (Fin 5)) := Sylow.ofCard a5Sub (hsyl _ card_a5Sub)
  let SX : Sylow 2 (alternatingGroup (Fin 5)) := Sylow.ofCard X (hsyl _ hX)
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq (alternatingGroup (Fin 5)) SY SX
  refine ⟨c, fun y hy => ?_, fun x hx => ?_⟩
  · have h2 : c * y * c⁻¹ ∈ ((c • SY : Sylow 2 (alternatingGroup (Fin 5))) :
        Subgroup (alternatingGroup (Fin 5))) := by
      rw [Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists]
      exact ⟨y, hy, by simp [MulAut.smul_def, MulAut.conj_apply]⟩
    rw [hc] at h2
    exact h2
  · have h2 : x ∈ ((c • SY : Sylow 2 (alternatingGroup (Fin 5))) :
        Subgroup (alternatingGroup (Fin 5))) := by
      rw [hc]
      exact hx
    rw [Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists] at h2
    obtain ⟨y, hy, rfl⟩ := h2
    have e : c⁻¹ * (MulAut.conj c • y) * c = y := by
      simp only [MulAut.smul_def, MulAut.conj_apply]
      group
    rw [e]
    exact hy

theorem alt5_centralizer_mem {X : Subgroup (alternatingGroup (Fin 5))} (hX : Nat.card ↥X = 4)
    (σ : Perm (Fin 5))
    (hσ : ∀ y ∈ X, σ * (y : Perm (Fin 5)) = (y : Perm (Fin 5)) * σ) :
    ∃ y ∈ X, (y : Perm (Fin 5)) = σ := by
  obtain ⟨c, hcY, hcX⟩ := exists_conj_model5 hX
  set τ : Perm (Fin 5) := (c : Perm (Fin 5))⁻¹ * σ * (c : Perm (Fin 5)) with hτ
  have hτc : ∀ i : Fin 4, τ * a5V i = a5V i * τ := by
    intro i
    have hyi : (⟨a5V i, (mem_alternatingGroup).2 (a5V_sign i)⟩ : alternatingGroup (Fin 5)) ∈
        a5Sub := ⟨i, rfl⟩
    have h1 := hσ _ (hcY _ hyi)
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h1
    calc τ * a5V i = (c : Perm (Fin 5))⁻¹ * (σ * ((c : Perm (Fin 5)) * a5V i *
          (c : Perm (Fin 5))⁻¹)) * (c : Perm (Fin 5)) := by rw [hτ]; group
      _ = (c : Perm (Fin 5))⁻¹ * (((c : Perm (Fin 5)) * a5V i *
          (c : Perm (Fin 5))⁻¹) * σ) * (c : Perm (Fin 5)) := by rw [h1]
      _ = a5V i * τ := by rw [hτ]; group
  obtain ⟨i, hi⟩ := a5V_centralizer τ hτc
  have hyi : (⟨a5V i, (mem_alternatingGroup).2 (a5V_sign i)⟩ : alternatingGroup (Fin 5)) ∈
      a5Sub := ⟨i, rfl⟩
  refine ⟨c * ⟨a5V i, (mem_alternatingGroup).2 (a5V_sign i)⟩ * c⁻¹, hcY _ hyi, ?_⟩
  have e : σ = (c : Perm (Fin 5)) * τ * (c : Perm (Fin 5))⁻¹ := by rw [hτ]; group
  rw [e, hi]
  simp

end CFSG.GH74.GLS.C3.Layer1.Bk
