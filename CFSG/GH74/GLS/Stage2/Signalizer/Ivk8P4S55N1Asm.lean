module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55N1

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Subgroup CFSG CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS
open scoped commutatorElement

section Cover

variable {k : Kind} {p : ℕ} {Γ : Type} [Group Γ] {V : Type} [AddCommGroup V]
  [Module (ZMod p) V] {ρ : Γ →* (V →ₗ[ZMod p] V)ˣ} {K : Subgroup Γ} {a : Γ} {P R : Subgroup Γ}

theorem Frame55.no_three [Finite Γ] (hf : Frame55 k p ρ K a P R) (hp3 : p = 3) :
    ¬ 3 ∣ Nat.card (center ↥K) := by
  intro h3
  have hK := hf.normal
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' 3 h3
  let N : Subgroup Γ :=
    { carrier := {x | x ∈ K ∧ (∀ y ∈ K, x * y = y * x) ∧ x ^ 3 = 1}
      one_mem' := ⟨K.one_mem, fun y _ => by simp, one_pow 3⟩
      mul_mem' := by
        rintro x y ⟨hxK, hxc, hx3⟩ ⟨hyK, hyc, hy3⟩
        refine ⟨K.mul_mem hxK hyK, fun w hw => ?_, ?_⟩
        · rw [mul_assoc, hyc w hw, ← mul_assoc, hxc w hw, mul_assoc]
        · rw [Commute.mul_pow (hxc y hyK), hx3, hy3, one_mul]
      inv_mem' := by
        rintro x ⟨hxK, hxc, hx3⟩
        refine ⟨K.inv_mem hxK, fun w hw => ?_, by rw [inv_pow, hx3, inv_one]⟩
        have := hxc w hw
        calc x⁻¹ * w = x⁻¹ * (w * x) * x⁻¹ := by group
          _ = x⁻¹ * (x * w) * x⁻¹ := by rw [← this]
          _ = w * x⁻¹ := by group }
  have hNn : N.Normal := by
    refine ⟨fun x hx g => ?_⟩
    obtain ⟨hxK, hxc, hx3⟩ := hx
    refine ⟨hK.conj_mem x hxK g, fun w hw => ?_, ?_⟩
    · have h1 : g⁻¹ * w * g⁻¹⁻¹ ∈ K := hK.conj_mem w hw g⁻¹
      have h2 := hxc _ h1
      calc g * x * g⁻¹ * w = g * (x * (g⁻¹ * w * g)) * g⁻¹ := by group
        _ = g * ((g⁻¹ * w * g) * x) * g⁻¹ := by
          have := hxc (g⁻¹ * w * g) (by simpa using h1)
          rw [this]
        _ = w * (g * x * g⁻¹) := by group
    · calc (g * x * g⁻¹) ^ 3 = g * x ^ 3 * g⁻¹ := by rw [conj_pow]
        _ = 1 := by rw [hx3]; group
  have hNp : IsPGroup 3 ↥N := fun x =>
    ⟨1, Subtype.ext (by simpa using x.2.2.2)⟩
  have hbot : N = ⊥ := by
    have := hf.opbot N hNn (by rw [← hp3] at hNp; exact hNp)
    exact this
  have hzN : ((z : ↥(center ↥K)) : ↥K).1 ∈ N := by
    refine ⟨(z : ↥K).2, fun y hy => ?_, ?_⟩
    · have := Subgroup.mem_center_iff.mp (z : ↥(center ↥K)).2 ⟨y, hy⟩
      exact congrArg Subtype.val this.symm
    · have h3' : (z : ↥(center ↥K)) ^ 3 = 1 := by
        rw [← hz]
        exact pow_orderOf_eq_one _
      have := congrArg (fun w : ↥(center ↥K) => ((w : ↥K) : Γ)) h3'
      simpa using this
  rw [hbot, Subgroup.mem_bot] at hzN
  have hz1 : (z : ↥(center ↥K)) = 1 := by
    apply Subtype.ext
    apply Subtype.ext
    exact hzN
  rw [hz1, orderOf_one] at hz
  exact absurd hz (by norm_num)

end Cover

theorem cell55_of_n1 {F : (Y : Type) → [Group Y] → Prop} (hM : MultAlt55) (hN : N1Fam F) :
    Cell55 F := by
  intro k p Γ _ _ V _ _ _ ρ K a P R hf hFK
  rcases hN _ p (bAut hf.normal a) (Rbar K R) hFK hf.n1 with ⟨hp3, hA, r, hobs⟩ | ⟨r, hobs, hNo⟩
  · have h3 := hf.no_three hp3
    have hZ6 : Nat.card (center ↥K) ∣ 6 := by
      rcases hA with hA7 | hA11
      · exact hM.1 ↥K hf.quasi hA7
      · exact (hM.2 ↥K hf.quasi hA11).trans (by norm_num)
    have hle : Nat.card (center ↥K) ≤ 6 := Nat.le_of_dvd (by norm_num) hZ6
    have hpos : 0 < Nat.card (center ↥K) := Nat.card_pos
    have hcase : Nat.card (center ↥K) = 1 ∨ Nat.card (center ↥K) = 2 := by
      generalize Nat.card (center ↥K) = c at hZ6 hle hpos h3
      interval_cases c <;> simp_all
    rcases hcase with h1 | h2
    · refine (hf.toMod55.false_of_hhobsAt (r := r) (fun _ => ?_) hobs).elim
      rw [h1]
      norm_num
    · right
      refine ⟨hp3, ?_⟩
      rcases hA with e | e
      · exact Or.inl ⟨hf.quasi, h2, e⟩
      · exact Or.inr ⟨hf.quasi, h2, e⟩
  · exact (hf.toMod55.false_of_hhobsAt
      (fun hr2 => hNo hr2 ↥K hf.quasi ⟨MulEquiv.refl _⟩) hobs).elim

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
