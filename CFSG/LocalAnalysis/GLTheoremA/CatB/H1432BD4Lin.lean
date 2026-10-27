module

public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.FieldTheory.Finiteness

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H1420.BD4

open Module

@[expose] def bd4OuterIdx : Fin 3 → Fin 4 := ![0, 1, 3]

private theorem outer_cover : ∀ i : Fin 4, i = 2 ∨ ∃ j, bd4OuterIdx j = i := by decide

private theorem add_one_ne_self_three : ∀ j : Fin 3, j + 1 ≠ j := by decide

variable {K : Type*} [Field K]

private theorem span_cond {V W : Type*} [AddCommGroup V] [Module K V] (f : V → W → K)
    (hadd : ∀ x x' y, f (x + x') y = f x y + f x' y)
    (hsmul : ∀ (r : K) x y, f (r • x) y = r * f x y) {S : Set V} {y : W}
    (h : ∀ x ∈ S, f x y = 0) {x : V} (hx : x ∈ Submodule.span K S) : f x y = 0 := by
  induction hx using Submodule.span_induction with
  | mem x hx => exact h x hx
  | zero => simpa using hsmul 0 0 y
  | add x x' _ _ hx hx' => rw [hadd, hx, hx', add_zero]
  | smul r x _ hx => rw [hsmul, hx, mul_zero]

private theorem finrank_add_le_three {S₂ S₃ : Set (Fin 3 → K)} (d : Fin 3 → K)
    (hd : ∀ j, d j ≠ 0) (h₂₃ : ∀ w ∈ S₂, ∀ v ∈ S₃, ∑ j, d j * w j * v j = 0) :
    finrank K (Submodule.span K S₂) + finrank K (Submodule.span K S₃) ≤ 3 := by
  let Φ : (Fin 3 → K) →ₗ[K] Module.Dual K (Fin 3 → K) :=
    LinearMap.mk₂ K (fun w v => ∑ j, d j * w j * v j)
      (fun w w' v => by simp only [Fin.sum_univ_three, Pi.add_apply]; ring)
      (fun r w v => by simp only [Fin.sum_univ_three, Pi.smul_apply, smul_eq_mul]; ring)
      (fun w v v' => by simp only [Fin.sum_univ_three, Pi.add_apply]; ring)
      (fun r w v => by simp only [Fin.sum_univ_three, Pi.smul_apply, smul_eq_mul]; ring)
  have hΦ : ∀ w v, Φ w v = ∑ j, d j * w j * v j := fun _ _ => rfl
  have hinj : Function.Injective Φ := by
    refine (injective_iff_map_eq_zero Φ).2 fun w hw => funext fun j => ?_
    have h1 : ∑ i, d i * w i * (if i = j then (1 : K) else 0) = 0 :=
      LinearMap.congr_fun hw (fun i => if i = j then (1 : K) else 0)
    rw [Finset.sum_eq_single j, if_pos rfl, mul_one] at h1
    · exact (mul_eq_zero.1 h1).resolve_left (hd j)
    · intro i _ hi
      rw [if_neg hi, mul_zero]
    · intro h
      exact absurd (Finset.mem_univ j) h
  have hle : Submodule.span K S₃ ≤ ((Submodule.span K S₂).map Φ).dualCoannihilator := by
    refine Submodule.span_le.2 fun v hv => (Submodule.mem_dualCoannihilator v).2 ?_
    rintro _ ⟨w, hw, rfl⟩
    rw [hΦ]
    exact span_cond (fun (w v : Fin 3 → K) => ∑ j, d j * w j * v j)
      (fun w w' v => by simp only [Fin.sum_univ_three, Pi.add_apply]; ring)
      (fun r w v => by simp only [Fin.sum_univ_three, Pi.smul_apply, smul_eq_mul]; ring)
      (fun w hw' => h₂₃ w hw' v hv) hw
  have h1 := Subspace.finrank_add_finrank_dualCoannihilator_eq ((Submodule.span K S₂).map Φ)
  have h2 := (Submodule.equivMapOfInjective Φ hinj (Submodule.span K S₂)).finrank_eq
  have h3 := Submodule.finrank_mono hle
  rw [Module.finrank_fin_fun] at h1
  omega

theorem finrank_span_add_le_five {S₁ : Set (Fin 4 → K)} {S₂ S₃ : Set (Fin 3 → K)}
    (a b : Fin 3 → K) (hb : ∀ j, b j ≠ 0)
    (h₁₁ : ∀ x ∈ S₁, ∀ x' ∈ S₁, ∀ j,
      a j * x (bd4OuterIdx j) * x' 2 + b j * x 2 * x' (bd4OuterIdx j) = 0)
    (e f : Fin 3 → Fin 3 → K) (he : ∀ j j', j ≠ j' → e j j' ≠ 0)
    (h₁₂ : ∀ x ∈ S₁, ∀ w ∈ S₂, ∀ j j', j ≠ j' →
      e j j' * x (bd4OuterIdx j) * w j' + f j j' * x (bd4OuterIdx j') * w j = 0)
    (c : Fin 3 → K) (hc : ∀ j, c j ≠ 0)
    (h₁₃ : ∀ x ∈ S₁, ∀ v ∈ S₃, ∑ j, c j * x (bd4OuterIdx j) * v j = 0)
    (d : Fin 3 → K) (hd : ∀ j, d j ≠ 0)
    (h₂₃ : ∀ w ∈ S₂, ∀ v ∈ S₃, ∑ j, d j * w j * v j = 0) :
    finrank K (Submodule.span K S₁) + finrank K (Submodule.span K S₂) +
      finrank K (Submodule.span K S₃) ≤ 5 := by
  classical
  have h23 := finrank_add_le_three d hd h₂₃
  by_cases hx : ∃ x₀ ∈ S₁, x₀ 2 ≠ 0
  ·
    obtain ⟨x₀, hx₀, hx₀2⟩ := hx
    have hinj : Function.Injective
        ((LinearMap.proj 2 : (Fin 4 → K) →ₗ[K] K).comp (Submodule.span K S₁).subtype) := by
      refine (injective_iff_map_eq_zero _).2 fun x hx2 => Subtype.ext (funext fun i => ?_)
      have hx2' : (x : Fin 4 → K) 2 = 0 := hx2
      have hxo : ∀ j, (x : Fin 4 → K) (bd4OuterIdx j) = 0 := fun j => by
        have h := span_cond (y := x₀)
          (fun x y => a j * y (bd4OuterIdx j) * x 2 + b j * y 2 * x (bd4OuterIdx j))
          (fun x x' y => by simp only [Pi.add_apply]; ring)
          (fun r x y => by simp only [Pi.smul_apply, smul_eq_mul]; ring)
          (fun x hx => h₁₁ x₀ hx₀ x hx j) x.2
        simp only [hx2', mul_zero, zero_add] at h
        exact (mul_eq_zero.1 h).resolve_left (mul_ne_zero (hb j) hx₀2)
      rcases outer_cover i with rfl | ⟨j, rfl⟩
      · exact hx2'
      · exact hxo j
    have h1 := (LinearMap.finrank_le_finrank_of_injective hinj).trans (Module.finrank_self K).le
    omega
  · push Not at hx
    let π : ↥(Submodule.span K S₁) →ₗ[K] (Fin 3 → K) :=
      (LinearMap.funLeft K K bd4OuterIdx).comp (Submodule.span K S₁).subtype
    have hπ : ∀ x j, π x j = (x : Fin 4 → K) (bd4OuterIdx j) := fun _ _ => rfl
    have hinj : Function.Injective π := by
      refine (injective_iff_map_eq_zero π).2 fun x hx0 => Subtype.ext (funext fun i => ?_)
      have hx2 : (x : Fin 4 → K) 2 = 0 :=
        span_cond (y := ()) (fun x (_ : Unit) => x 2) (fun _ _ _ => rfl) (fun _ _ _ => rfl)
          (fun x hx' => hx x hx') x.2
      rcases outer_cover i with rfl | ⟨j, rfl⟩
      · exact hx2
      · exact (hπ x j).symm.trans (congrFun hx0 j)
    have hle3 : finrank K (Submodule.span K S₁) ≤ 3 :=
      (LinearMap.finrank_le_finrank_of_injective hinj).trans (Module.finrank_fin_fun K).le
    by_cases h3 : finrank K (Submodule.span K S₁) ≤ 2
    · omega
    have heq : finrank K (Submodule.span K S₁) = finrank K (Fin 3 → K) := by
      rw [Module.finrank_fin_fun]
      omega
    have hsurj := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank heq).1 hinj
    have hunit : ∀ j, ∃ x ∈ Submodule.span K S₁, ∀ j',
        x (bd4OuterIdx j') = if j' = j then (1 : K) else 0 := by
      intro j
      obtain ⟨x, hx'⟩ := hsurj fun j' => if j' = j then (1 : K) else 0
      exact ⟨x, x.2, fun j' => by rw [← hπ, hx']⟩
    have hS₂ : ∀ w ∈ S₂, w = 0 := by
      intro w hw
      funext j'
      obtain ⟨x, hxS, hxu⟩ := hunit (j' + 1)
      have hne := add_one_ne_self_three j'
      have hx1 : x (bd4OuterIdx (j' + 1)) = 1 := by rw [hxu, if_pos rfl]
      have hx0 : x (bd4OuterIdx j') = 0 := by rw [hxu, if_neg (Ne.symm hne)]
      have h := span_cond (y := w)
        (fun x w => e (j' + 1) j' * x (bd4OuterIdx (j' + 1)) * w j' +
          f (j' + 1) j' * x (bd4OuterIdx j') * w (j' + 1))
        (fun x x' w => by simp only [Pi.add_apply]; ring)
        (fun r x w => by simp only [Pi.smul_apply, smul_eq_mul]; ring)
        (fun x hx' => h₁₂ x hx' w hw (j' + 1) j' hne) hxS
      simp only [hx1, hx0, mul_one, mul_zero, zero_mul, add_zero] at h
      exact (mul_eq_zero.1 h).resolve_left (he _ _ hne)
    have hS₃ : ∀ v ∈ S₃, v = 0 := by
      intro v hv
      funext j
      obtain ⟨x, hxS, hxu⟩ := hunit j
      have h := span_cond (y := v) (fun x v => ∑ i, c i * x (bd4OuterIdx i) * v i)
        (fun x x' v => by simp only [Fin.sum_univ_three, Pi.add_apply]; ring)
        (fun r x v => by simp only [Fin.sum_univ_three, Pi.smul_apply, smul_eq_mul]; ring)
        (fun x hx' => h₁₃ x hx' v hv) hxS
      simp only [hxu] at h
      rw [Finset.sum_eq_single j, if_pos rfl, mul_one] at h
      · exact (mul_eq_zero.1 h).resolve_left (hc j)
      · intro i _ hi
        rw [if_neg hi, mul_zero, zero_mul]
      · intro h'
        exact absurd (Finset.mem_univ j) h'
    have hV₂ : Submodule.span K S₂ = ⊥ := Submodule.span_eq_bot.2 hS₂
    have hV₃ : Submodule.span K S₃ = ⊥ := Submodule.span_eq_bot.2 hS₃
    rw [hV₂, hV₃, finrank_bot]
    omega

theorem card_mul_le_pow_five [Finite K] {S₁ : Set (Fin 4 → K)} {S₂ S₃ : Set (Fin 3 → K)}
    (a b : Fin 3 → K) (hb : ∀ j, b j ≠ 0)
    (h₁₁ : ∀ x ∈ S₁, ∀ x' ∈ S₁, ∀ j,
      a j * x (bd4OuterIdx j) * x' 2 + b j * x 2 * x' (bd4OuterIdx j) = 0)
    (e f : Fin 3 → Fin 3 → K) (he : ∀ j j', j ≠ j' → e j j' ≠ 0)
    (h₁₂ : ∀ x ∈ S₁, ∀ w ∈ S₂, ∀ j j', j ≠ j' →
      e j j' * x (bd4OuterIdx j) * w j' + f j j' * x (bd4OuterIdx j') * w j = 0)
    (c : Fin 3 → K) (hc : ∀ j, c j ≠ 0)
    (h₁₃ : ∀ x ∈ S₁, ∀ v ∈ S₃, ∑ j, c j * x (bd4OuterIdx j) * v j = 0)
    (d : Fin 3 → K) (hd : ∀ j, d j ≠ 0)
    (h₂₃ : ∀ w ∈ S₂, ∀ v ∈ S₃, ∑ j, d j * w j * v j = 0) :
    Nat.card S₁ * Nat.card S₂ * Nat.card S₃ ≤ Nat.card K ^ 5 := by
  have h := finrank_span_add_le_five a b hb h₁₁ e f he h₁₂ c hc h₁₃ d hd h₂₃
  have hS : ∀ {n : ℕ} (S : Set (Fin n → K)),
      Nat.card S ≤ Nat.card K ^ finrank K (Submodule.span K S) := by
    intro n S
    rw [← Module.natCard_eq_pow_finrank]
    exact Nat.card_le_card_of_injective
      (fun x : S => (⟨x.1, Submodule.subset_span x.2⟩ : Submodule.span K S))
      (fun x y hxy => Subtype.ext
        (congrArg (fun z : Submodule.span K S => (z : Fin n → K)) hxy))
  calc Nat.card S₁ * Nat.card S₂ * Nat.card S₃
      ≤ Nat.card K ^ finrank K (Submodule.span K S₁) *
          Nat.card K ^ finrank K (Submodule.span K S₂) *
          Nat.card K ^ finrank K (Submodule.span K S₃) :=
        Nat.mul_le_mul (Nat.mul_le_mul (hS S₁) (hS S₂)) (hS S₃)
    _ = Nat.card K ^ (finrank K (Submodule.span K S₁) + finrank K (Submodule.span K S₂) +
          finrank K (Submodule.span K S₃)) := by rw [pow_add, pow_add]
    _ ≤ Nat.card K ^ 5 := Nat.pow_le_pow_right Nat.card_pos h

end CFSG.LocalAnalysis.GLTheoremA.H1420.BD4

end
