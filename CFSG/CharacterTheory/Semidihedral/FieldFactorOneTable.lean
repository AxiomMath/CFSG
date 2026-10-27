module

public import CFSG.CharacterTheory.Semidihedral.FieldFactorOneTableRelations
public import Mathlib.RingTheory.SimpleRing.Principal

public section

open Finset

namespace CFSG.Semidihedral.FieldFactorOne

namespace TableCoordinates

variable {L : Type*} [DecidableEq L]

section Final

variable {k : ℕ} {B : Finset L} {deg Θ : L → ℤ} {E F : ℕ → L → ℤ} {U V : L → ℤ}
  {c₀ c₁ c₂ c₃ c₄ : L} {δ₀ δ₁ δ₂ δ₃ δ₄ δ δF : ℤ} {ψ ν : ℕ → L}

theorem FSystem.swap (T : FSystem k B F c₀ c₁ c₂ c₃ c₄ ψ ν δF) (hk : k = 2) :
    FSystem k B F c₀ c₁ c₂ c₃ c₄ ψ (fun i => if i = 0 then ν 1 else if i = 1 then ν 0 else ν i)
      (-δF) := by
  subst hk
  have h0 : 0 ∈ range 2 := by simp
  have h1 : 1 ∈ range 2 := by simp
  have hr : ∀ i ∈ range 2, i = 0 ∨ i = 1 := fun i hi => by
    rw [Finset.mem_range] at hi
    omega
  refine ⟨?_, fun i hi => ?_, fun i hi l hl => ?_, fun i hi i' hi' e => ?_, fun j hj x hx => ?_⟩
  · rcases T.hδF with e | e <;> rw [e] <;> norm_num
  · rcases hr i hi with rfl | rfl
    · exact T.hν 1 h1
    · exact T.hν 0 h0
  · rcases hr i hi with rfl | rfl
    · exact T.νψ 1 h1 l hl
    · exact T.νψ 0 h0 l hl
  · have hne : ν 0 ≠ ν 1 := fun e' => absurd (T.inj h0 h1 e') (by norm_num)
    rcases hr i (Finset.mem_coe.mp hi) with rfl | rfl <;>
      rcases hr i' (Finset.mem_coe.mp hi') with rfl | rfl
    · rfl
    · exact absurd e hne.symm
    · exact absurd e hne
    · rfl
  · have hj1 : j = 1 := by
      rw [Finset.mem_Icc] at hj
      omega
    subst hj1
    rw [T.hF 1 hj x hx]
    simp only [one_ne_zero, ↓reduceIte]
    ring

theorem ShapeA.cast_sum_mul_Θ {R : Type*} [CommRing R]
    (A : ShapeA B Θ U c₀ c₁ c₂ c₃ c₄ δ₀ δ₁ δ₂ δ₃ δ₄) (X : L → R) :
    ∑ x ∈ B, X x * (Θ x : R) = δ₀ * X c₀ + δ₁ * X c₁ + δ₂ * X c₂ + δ₃ * X c₃ := by
  rw [← sum_mul_formΘ X A.h₀ A.h₁ A.h₂ A.h₃]
  refine Finset.sum_congr rfl fun x hx => ?_
  rw [A.hΘ x hx]
  push_cast
  rfl

theorem ShapeA.cast_sum_mul_U {R : Type*} [CommRing R]
    (A : ShapeA B Θ U c₀ c₁ c₂ c₃ c₄ δ₀ δ₁ δ₂ δ₃ δ₄) (X : L → R) :
    ∑ x ∈ B, X x * (U x : R) = δ₀ * X c₀ - δ₁ * X c₁ + δ₂ * X c₂ - δ₃ * X c₃ + 2 * δ₄ * X c₄ := by
  rw [← sum_mul_formU X A.h₀ A.h₁ A.h₂ A.h₃ A.h₄]
  refine Finset.sum_congr rfl fun x hx => ?_
  rw [A.hU x hx]
  push_cast
  rfl

theorem ESystem.cast_sum_mul_E {R : Type*} [CommRing R]
    (S : ESystem k B E c₀ c₁ c₂ c₃ c₄ δ₀ δ₁ δ ψ) (h₀ : c₀ ∈ B) (h₁ : c₁ ∈ B) {l : ℕ}
    (hl : l ∈ Icc 1 (k - 1)) (X : L → R) :
    ∑ x ∈ B, X x * (E l x : R) = δ₀ * X c₀ + δ₁ * X c₁ - δ * X (ψ l) := by
  rw [← sum_mul_formE X h₀ h₁ (Finset.mem_sdiff.mp (S.hψ l hl)).1]
  refine Finset.sum_congr rfl fun x hx => ?_
  rw [S.hE l hl x hx]
  push_cast
  rfl

theorem FSystem.cast_sum_mul_F {R : Type*} [CommRing R]
    (T : FSystem k B F c₀ c₁ c₂ c₃ c₄ ψ ν δF) (hk : 2 ≤ k) {j : ℕ} (hj : j ∈ Icc 1 (k - 1))
    (X : L → R) : ∑ x ∈ B, X x * (F j x : R) = δF * (X (ν j) - X (ν 0)) := by
  have hjr : j ∈ range k := by
    rw [Finset.mem_Icc] at hj
    exact Finset.mem_range.mpr (by omega)
  rw [← sum_mul_formF X (Finset.mem_sdiff.mp (T.hν j hjr)).1
    (Finset.mem_sdiff.mp (T.hν 0 (Finset.mem_range.mpr (by omega)))).1]
  refine Finset.sum_congr rfl fun x hx => ?_
  rw [T.hF j hj x hx]
  push_cast
  rfl

theorem Hyp.table (h : Hyp k B deg Θ E F U V) :
    ∃ (c₀ c₁ c₂ c₃ c₄ : L) (δ₀ δ₁ δ₂ δ₃ δ₄ δ : ℤ) (ψ ν : ℕ → L),
      ShapeA B Θ U c₀ c₁ c₂ c₃ c₄ δ₀ δ₁ δ₂ δ₃ δ₄ ∧ ESystem k B E c₀ c₁ c₂ c₃ c₄ δ₀ δ₁ δ ψ ∧
      FSystem k B F c₀ c₁ c₂ c₃ c₄ ψ ν δ ∧
      ∀ x ∈ B, V x = δ₁ * (if x = c₁ then 1 else 0) - δ₂ * (if x = c₂ then 1 else 0) -
        δ₄ * (if x = c₄ then 1 else 0) + δ * ∑ l ∈ Icc 1 (k - 1), (if x = ψ l then 1 else 0) -
        δ * ∑ i ∈ range k, (if x = ν i then 1 else 0) := by
  obtain ⟨c₀, c₁, c₂, c₃, c₄, δ₀, δ₁, δ₂, δ₃, δ₄, A, ψ, δ, S⟩ := h.stageE
  obtain ⟨ν, δF, T⟩ := h.stageF A S
  obtain ⟨hV, hδF⟩ := h.stageV A S T
  by_cases hFδ : δF = δ
  · subst hFδ
    exact ⟨c₀, c₁, c₂, c₃, c₄, δ₀, δ₁, δ₂, δ₃, δ₄, δF, ψ, ν, A, S, T, hV⟩
  have hk2 : k = 2 := by
    rcases h.hk24 with h2 | h4
    · exact h2
    · exact absurd (hδF h4) hFδ
  have hneg : -δF = δ := by
    rcases T.hδF with e | e <;> rcases S.hδ with e' | e' <;> rw [e, e'] at hFδ ⊢ <;>
      first | rfl | exact absurd rfl hFδ
  have T' := T.swap hk2
  rw [hneg] at T'
  refine ⟨c₀, c₁, c₂, c₃, c₄, δ₀, δ₁, δ₂, δ₃, δ₄, δ, ψ, _, A, S, T', fun x hx => ?_⟩
  rw [hV x hx]
  subst hk2
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, one_ne_zero, ↓reduceIte]
  ring

end Final

end TableCoordinates

open TableCoordinates in
theorem type_star_table_coordinates_weak {L : Type*} [DecidableEq L]
    (k : ℕ) (hk : 2 ≤ k) (hkpow : ∃ m : ℕ, k = 2 ^ m)
    (B : Finset L) (deg : L → ℤ) (hdeg : ∀ x ∈ B, 0 < deg x)
    (Θ : L → ℤ) (E F : ℕ → L → ℤ) (U V : L → ℤ)
    (hΘΘ : ∑ x ∈ B, Θ x * Θ x = 4)
    (hΘE : ∀ l ∈ Finset.Icc 1 (k - 1), ∑ x ∈ B, Θ x * E l x = 2)
    (hEE : ∀ l ∈ Finset.Icc 1 (k - 1), ∀ l' ∈ Finset.Icc 1 (k - 1),
      ∑ x ∈ B, E l x * E l' x = 2 + if l = l' then 1 else 0)
    (hΘF : ∀ j ∈ Finset.Icc 1 (k - 1), ∑ x ∈ B, Θ x * F j x = 0)
    (hEF : ∀ l ∈ Finset.Icc 1 (k - 1), ∀ j ∈ Finset.Icc 1 (k - 1),
      ∑ x ∈ B, E l x * F j x = 0)
    (hFF : ∀ j ∈ Finset.Icc 1 (k - 1), ∀ j' ∈ Finset.Icc 1 (k - 1),
      ∑ x ∈ B, F j x * F j' x = 1 + if j = j' then 1 else 0)
    (hUU : ∑ x ∈ B, U x * U x = 8) (hUV : ∑ x ∈ B, U x * V x = -4)
    (hVV : ∑ x ∈ B, V x * V x = 2 * k + 2)
    (hUΘ : ∑ x ∈ B, U x * Θ x = 0) (hVΘ : ∑ x ∈ B, V x * Θ x = 0)
    (hUE : ∀ l ∈ Finset.Icc 1 (k - 1), ∑ x ∈ B, U x * E l x = 0)
    (hVE : ∀ l ∈ Finset.Icc 1 (k - 1), ∑ x ∈ B, V x * E l x = 0)
    (hUF : ∀ j ∈ Finset.Icc 1 (k - 1), ∑ x ∈ B, U x * F j x = 0)
    (hVF : ∀ j ∈ Finset.Icc 1 (k - 1), ∑ x ∈ B, V x * F j x = 0)
    (hdegΘ : ∑ x ∈ B, deg x * Θ x = 0)
    (hdegE : ∀ l ∈ Finset.Icc 1 (k - 1), ∑ x ∈ B, deg x * E l x = 0)
    (hdegF : ∀ j ∈ Finset.Icc 1 (k - 1), ∑ x ∈ B, deg x * F j x = 0)
    (hdegU : ∑ x ∈ B, deg x * U x = 0) (hdegV : ∑ x ∈ B, deg x * V x = 0)
    (hcong : ∀ x ∈ B, (2 * k : ℤ) ∣ U x + 2 * V x + Θ x +
      2 * ∑ l ∈ Finset.Icc 1 (k - 1), E l x + 2 * ∑ j ∈ Finset.Icc 1 (k - 1), F j x) :
    ∃ (c₀ c₁ c₂ c₃ c₄ : L) (δ₀ δ₁ δ₂ δ₃ δ₄ δ : ℤ) (ψ ν : ℕ → L),
      (δ₀ = 1 ∨ δ₀ = -1) ∧ (δ₁ = 1 ∨ δ₁ = -1) ∧ (δ₂ = 1 ∨ δ₂ = -1) ∧
      (δ₃ = 1 ∨ δ₃ = -1) ∧ (δ₄ = 1 ∨ δ₄ = -1) ∧ (δ = 1 ∨ δ = -1) ∧
      [c₀, c₁, c₂, c₃, c₄].Nodup ∧
      Set.InjOn ψ (Finset.Icc 1 (k - 1) : Set ℕ) ∧ Set.InjOn ν (Finset.range k : Set ℕ) ∧
      (∀ l ∈ Finset.Icc 1 (k - 1),
        ψ l ≠ c₀ ∧ ψ l ≠ c₁ ∧ ψ l ≠ c₂ ∧ ψ l ≠ c₃ ∧ ψ l ≠ c₄) ∧
      (∀ i ∈ Finset.range k, ν i ≠ c₀ ∧ ν i ≠ c₁ ∧ ν i ≠ c₂ ∧ ν i ≠ c₃ ∧ ν i ≠ c₄) ∧
      (∀ i ∈ Finset.range k, ∀ l ∈ Finset.Icc 1 (k - 1), ν i ≠ ψ l) ∧
      ({c₀, c₁, c₂, c₃, c₄} ∪ (Finset.Icc 1 (k - 1)).image ψ ∪
        (Finset.range k).image ν : Finset L) ⊆ B ∧
      (∀ x ∈ B, Θ x = δ₀ * (if x = c₀ then 1 else 0) + δ₁ * (if x = c₁ then 1 else 0) +
        δ₂ * (if x = c₂ then 1 else 0) + δ₃ * (if x = c₃ then 1 else 0)) ∧
      (∀ l ∈ Finset.Icc 1 (k - 1), ∀ x ∈ B,
        E l x = δ₀ * (if x = c₀ then 1 else 0) + δ₁ * (if x = c₁ then 1 else 0) -
          δ * (if x = ψ l then 1 else 0)) ∧
      (∀ j ∈ Finset.Icc 1 (k - 1), ∀ x ∈ B,
        F j x = δ * ((if x = ν j then 1 else 0) - (if x = ν 0 then 1 else 0))) ∧
      (∀ x ∈ B, U x = δ₀ * (if x = c₀ then 1 else 0) - δ₁ * (if x = c₁ then 1 else 0) +
        δ₂ * (if x = c₂ then 1 else 0) - δ₃ * (if x = c₃ then 1 else 0) +
        2 * δ₄ * (if x = c₄ then 1 else 0)) ∧
      (∀ x ∈ B, V x = δ₁ * (if x = c₁ then 1 else 0) - δ₂ * (if x = c₂ then 1 else 0) -
        δ₄ * (if x = c₄ then 1 else 0) +
        δ * ∑ l ∈ Finset.Icc 1 (k - 1), (if x = ψ l then 1 else 0) -
        δ * ∑ i ∈ Finset.range k, (if x = ν i then 1 else 0)) ∧
      (∀ X : L → ℂ,
        ∑ x ∈ B, X x * (Θ x : ℂ) = 0 →
        (∀ l ∈ Finset.Icc 1 (k - 1), ∑ x ∈ B, X x * (E l x : ℂ) = 0) →
        (∀ j ∈ Finset.Icc 1 (k - 1), ∑ x ∈ B, X x * (F j x : ℂ) = 0) →
        ∑ x ∈ B, X x * (U x : ℂ) = 0 → ∑ x ∈ B, X x * (V x : ℂ) = 0 →
        (δ₀ : ℂ) * X c₀ + δ₁ * X c₁ + δ₂ * X c₂ + δ₃ * X c₃ = 0 ∧
        (∀ l ∈ Finset.Icc 1 (k - 1), (δ : ℂ) * X (ψ l) = δ₀ * X c₀ + δ₁ * X c₁) ∧
        (∀ i ∈ Finset.range k, (δ : ℂ) * X (ν i) = δ₀ * X c₀ + δ₁ * X c₁) ∧
        (δ₀ : ℂ) * X c₀ + δ₂ * X c₂ + δ₄ * X c₄ = 0) ∧
      δ₀ * deg c₀ + δ₁ * deg c₁ + δ₂ * deg c₂ + δ₃ * deg c₃ = 0 ∧
      (∀ l ∈ Finset.Icc 1 (k - 1), δ * deg (ψ l) = δ₀ * deg c₀ + δ₁ * deg c₁) ∧
      (∀ i ∈ Finset.range k, δ * deg (ν i) = δ₀ * deg c₀ + δ₁ * deg c₁) ∧
      δ₀ * deg c₀ + δ₂ * deg c₂ + δ₄ * deg c₄ = 0 := by
  have hk24 : k = 2 ∨ 4 ≤ k := by
    obtain ⟨m, rfl⟩ := hkpow
    rcases m with _ | _ | m
    · norm_num at hk
    · left
      norm_num
    · right
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ (m + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have heven : Even k := by
    obtain ⟨m, rfl⟩ := hkpow
    rcases m with _ | m
    · norm_num at hk
    · exact ⟨2 ^ m, by rw [pow_succ]; ring⟩
  have h : Hyp k B deg Θ E F U V :=
    ⟨hk, hk24, heven, hdeg, hΘΘ, hΘE, hEE, hΘF, hEF, hFF, hUU, hUV, hVV, hUΘ, hVΘ, hUE, hVE,
      hUF, hVF, hdegΘ, hdegE, hdegF, hdegU, hdegV, hcong⟩
  obtain ⟨c₀, c₁, c₂, c₃, c₄, δ₀, δ₁, δ₂, δ₃, δ₄, δ, ψ, ν, A, S, T, hVf⟩ := h.table
  have hψB : ∀ l ∈ Icc 1 (k - 1), ψ l ∈ B := fun l hl => (Finset.mem_sdiff.mp (S.hψ l hl)).1
  have hνB : ∀ i ∈ range k, ν i ∈ B := fun i hi => (Finset.mem_sdiff.mp (T.hν i hi)).1
  have hrel : ∀ X : L → ℂ,
      ∑ x ∈ B, X x * (Θ x : ℂ) = 0 →
      (∀ l ∈ Finset.Icc 1 (k - 1), ∑ x ∈ B, X x * (E l x : ℂ) = 0) →
      (∀ j ∈ Finset.Icc 1 (k - 1), ∑ x ∈ B, X x * (F j x : ℂ) = 0) →
      ∑ x ∈ B, X x * (U x : ℂ) = 0 → ∑ x ∈ B, X x * (V x : ℂ) = 0 →
      (δ₀ : ℂ) * X c₀ + δ₁ * X c₁ + δ₂ * X c₂ + δ₃ * X c₃ = 0 ∧
      (∀ l ∈ Finset.Icc 1 (k - 1), (δ : ℂ) * X (ψ l) = δ₀ * X c₀ + δ₁ * X c₁) ∧
      (∀ i ∈ Finset.range k, (δ : ℂ) * X (ν i) = δ₀ * X c₀ + δ₁ * X c₁) ∧
      (δ₀ : ℂ) * X c₀ + δ₂ * X c₂ + δ₄ * X c₄ = 0 := by
    intro X eΘ eE eF eU eV
    rw [A.cast_sum_mul_Θ X] at eΘ
    rw [A.cast_sum_mul_U X] at eU
    have eE' : ∀ l ∈ Icc 1 (k - 1), (δ₀ : ℂ) * X c₀ + δ₁ * X c₁ - δ * X (ψ l) = 0 :=
      fun l hl => by rw [← S.cast_sum_mul_E A.h₀ A.h₁ hl X]; exact eE l hl
    have eF' : ∀ j ∈ Icc 1 (k - 1), (δ : ℂ) * (X (ν j) - X (ν 0)) = 0 :=
      fun j hj => by rw [← T.cast_sum_mul_F hk hj X]; exact eF j hj
    have eV' : (δ₁ : ℂ) * X c₁ - δ₂ * X c₂ - δ₄ * X c₄ + δ * ∑ l ∈ Icc 1 (k - 1), X (ψ l) -
        δ * ∑ i ∈ range k, X (ν i) = 0 := by
      have hpt : ∀ x ∈ B, X x * (V x : ℂ) = X x * ((δ₁ : ℂ) * (if x = c₁ then 1 else 0) -
          δ₂ * (if x = c₂ then 1 else 0) - δ₄ * (if x = c₄ then 1 else 0) +
          δ * ∑ l ∈ Icc 1 (k - 1), (if x = ψ l then 1 else 0) -
          δ * ∑ i ∈ range k, (if x = ν i then 1 else 0)) := fun x hx => by
        rw [hVf x hx]
        push_cast
        rfl
      rw [Finset.sum_congr rfl hpt, sum_mul_formV X A.h₁ A.h₂ A.h₄ hψB hνB] at eV
      exact eV
    have hδ0 : (δ : ℂ) ≠ 0 := by exact_mod_cast sign_ne_zero S.hδ
    exact orth_relations (Xψ := fun l => X (ψ l)) (Xν := fun i => X (ν i)) hk hδ0 eΘ eE' eF'
      eU eV'
  obtain ⟨d15, d14, d17, d16⟩ := hrel (fun x => (deg x : ℂ)) (by exact_mod_cast hdegΘ)
    (fun l hl => by exact_mod_cast hdegE l hl) (fun j hj => by exact_mod_cast hdegF j hj)
    (by exact_mod_cast hdegU) (by exact_mod_cast hdegV)
  have hψC : ∀ l ∈ Icc 1 (k - 1), ψ l ≠ c₀ ∧ ψ l ≠ c₁ ∧ ψ l ≠ c₂ ∧ ψ l ≠ c₃ ∧ ψ l ≠ c₄ :=
    fun l hl => (mem_sdiff_five.mp (S.hψ l hl)).2
  have hνC : ∀ i ∈ range k, ν i ≠ c₀ ∧ ν i ≠ c₁ ∧ ν i ≠ c₂ ∧ ν i ≠ c₃ ∧ ν i ≠ c₄ :=
    fun i hi => (mem_sdiff_five.mp (T.hν i hi)).2
  refine ⟨c₀, c₁, c₂, c₃, c₄, δ₀, δ₁, δ₂, δ₃, δ₄, δ, ψ, ν, A.s₀, A.s₁, A.s₂, A.s₃, A.s₄, S.hδ,
    ?_, S.inj, T.inj, hψC, hνC, T.νψ, ?_, A.hΘ, S.hE, T.hF, A.hU, hVf, hrel,
    by exact_mod_cast d15, fun l hl => by exact_mod_cast d14 l hl,
    fun i hi => by exact_mod_cast d17 i hi, by exact_mod_cast d16⟩
  · simp [A.n01, A.n02, A.n03, A.n04, A.n12, A.n13, A.n14, A.n23, A.n24, A.n34]
  · intro x hx
    simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, Finset.mem_image] at hx
    rcases hx with ((rfl | rfl | rfl | rfl | rfl) | ⟨l, hl, rfl⟩) | ⟨i, hi, rfl⟩
    exacts [A.h₀, A.h₁, A.h₂, A.h₃, A.h₄, hψB l hl, hνB i hi]

theorem type_star_table_coordinates {L : Type*} [DecidableEq L]
    (k : ℕ) (hk : 2 ≤ k) (hkpow : ∃ m : ℕ, k = 2 ^ m)
    (B : Finset L) (deg : L → ℤ) (hdeg : ∀ x ∈ B, 0 < deg x)
    (Θ : L → ℤ) (E F : ℕ → L → ℤ) (U V : L → ℤ)
    (hΘΘ : ∑ x ∈ B, Θ x * Θ x = 4)
    (hΘE : ∀ l ∈ Finset.Icc 1 (k - 1), ∑ x ∈ B, Θ x * E l x = 2)
    (hEE : ∀ l ∈ Finset.Icc 1 (k - 1), ∀ l' ∈ Finset.Icc 1 (k - 1),
      ∑ x ∈ B, E l x * E l' x = 2 + if l = l' then 1 else 0)
    (hΘF : ∀ j ∈ Finset.Icc 1 (k - 1), ∑ x ∈ B, Θ x * F j x = 0)
    (hEF : ∀ l ∈ Finset.Icc 1 (k - 1), ∀ j ∈ Finset.Icc 1 (k - 1),
      ∑ x ∈ B, E l x * F j x = 0)
    (hFF : ∀ j ∈ Finset.Icc 1 (k - 1), ∀ j' ∈ Finset.Icc 1 (k - 1),
      ∑ x ∈ B, F j x * F j' x = 1 + if j = j' then 1 else 0)
    (hUU : ∑ x ∈ B, U x * U x = 8) (hUV : ∑ x ∈ B, U x * V x = -4)
    (hVV : ∑ x ∈ B, V x * V x = 2 * k + 2)
    (hUΘ : ∑ x ∈ B, U x * Θ x = 0) (hVΘ : ∑ x ∈ B, V x * Θ x = 0)
    (hUE : ∀ l ∈ Finset.Icc 1 (k - 1), ∑ x ∈ B, U x * E l x = 0)
    (hVE : ∀ l ∈ Finset.Icc 1 (k - 1), ∑ x ∈ B, V x * E l x = 0)
    (hUF : ∀ j ∈ Finset.Icc 1 (k - 1), ∑ x ∈ B, U x * F j x = 0)
    (hVF : ∀ j ∈ Finset.Icc 1 (k - 1), ∑ x ∈ B, V x * F j x = 0)
    (hdegΘ : ∑ x ∈ B, deg x * Θ x = 0)
    (hdegE : ∀ l ∈ Finset.Icc 1 (k - 1), ∑ x ∈ B, deg x * E l x = 0)
    (hdegF : ∀ j ∈ Finset.Icc 1 (k - 1), ∑ x ∈ B, deg x * F j x = 0)
    (hdegU : ∑ x ∈ B, deg x * U x = 0) (hdegV : ∑ x ∈ B, deg x * V x = 0)
    (hcong : ∀ x ∈ B, (2 * k : ℤ) ∣ U x + 2 * V x + Θ x +
      2 * ∑ l ∈ Finset.Icc 1 (k - 1), E l x + 2 * ∑ j ∈ Finset.Icc 1 (k - 1), F j x)
    (hexh : ∀ x ∈ B, U x ≠ 0 ∨ V x ≠ 0) :
    ∃ (c₀ c₁ c₂ c₃ c₄ : L) (δ₀ δ₁ δ₂ δ₃ δ₄ δ : ℤ) (ψ ν : ℕ → L),
      (δ₀ = 1 ∨ δ₀ = -1) ∧ (δ₁ = 1 ∨ δ₁ = -1) ∧ (δ₂ = 1 ∨ δ₂ = -1) ∧
      (δ₃ = 1 ∨ δ₃ = -1) ∧ (δ₄ = 1 ∨ δ₄ = -1) ∧ (δ = 1 ∨ δ = -1) ∧
      [c₀, c₁, c₂, c₃, c₄].Nodup ∧
      Set.InjOn ψ (Finset.Icc 1 (k - 1) : Set ℕ) ∧ Set.InjOn ν (Finset.range k : Set ℕ) ∧
      (∀ l ∈ Finset.Icc 1 (k - 1),
        ψ l ≠ c₀ ∧ ψ l ≠ c₁ ∧ ψ l ≠ c₂ ∧ ψ l ≠ c₃ ∧ ψ l ≠ c₄) ∧
      (∀ i ∈ Finset.range k, ν i ≠ c₀ ∧ ν i ≠ c₁ ∧ ν i ≠ c₂ ∧ ν i ≠ c₃ ∧ ν i ≠ c₄) ∧
      (∀ i ∈ Finset.range k, ∀ l ∈ Finset.Icc 1 (k - 1), ν i ≠ ψ l) ∧
      B = ({c₀, c₁, c₂, c₃, c₄} ∪ (Finset.Icc 1 (k - 1)).image ψ ∪
        (Finset.range k).image ν : Finset L) ∧
      B.card = 2 * k + 4 ∧
      (∀ x ∈ B, Θ x = δ₀ * (if x = c₀ then 1 else 0) + δ₁ * (if x = c₁ then 1 else 0) +
        δ₂ * (if x = c₂ then 1 else 0) + δ₃ * (if x = c₃ then 1 else 0)) ∧
      (∀ l ∈ Finset.Icc 1 (k - 1), ∀ x ∈ B,
        E l x = δ₀ * (if x = c₀ then 1 else 0) + δ₁ * (if x = c₁ then 1 else 0) -
          δ * (if x = ψ l then 1 else 0)) ∧
      (∀ j ∈ Finset.Icc 1 (k - 1), ∀ x ∈ B,
        F j x = δ * ((if x = ν j then 1 else 0) - (if x = ν 0 then 1 else 0))) ∧
      (∀ x ∈ B, U x = δ₀ * (if x = c₀ then 1 else 0) - δ₁ * (if x = c₁ then 1 else 0) +
        δ₂ * (if x = c₂ then 1 else 0) - δ₃ * (if x = c₃ then 1 else 0) +
        2 * δ₄ * (if x = c₄ then 1 else 0)) ∧
      (∀ x ∈ B, V x = δ₁ * (if x = c₁ then 1 else 0) - δ₂ * (if x = c₂ then 1 else 0) -
        δ₄ * (if x = c₄ then 1 else 0) +
        δ * ∑ l ∈ Finset.Icc 1 (k - 1), (if x = ψ l then 1 else 0) -
        δ * ∑ i ∈ Finset.range k, (if x = ν i then 1 else 0)) ∧
      (∀ X : L → ℂ,
        ∑ x ∈ B, X x * (Θ x : ℂ) = 0 →
        (∀ l ∈ Finset.Icc 1 (k - 1), ∑ x ∈ B, X x * (E l x : ℂ) = 0) →
        (∀ j ∈ Finset.Icc 1 (k - 1), ∑ x ∈ B, X x * (F j x : ℂ) = 0) →
        ∑ x ∈ B, X x * (U x : ℂ) = 0 → ∑ x ∈ B, X x * (V x : ℂ) = 0 →
        (δ₀ : ℂ) * X c₀ + δ₁ * X c₁ + δ₂ * X c₂ + δ₃ * X c₃ = 0 ∧
        (∀ l ∈ Finset.Icc 1 (k - 1), (δ : ℂ) * X (ψ l) = δ₀ * X c₀ + δ₁ * X c₁) ∧
        (∀ i ∈ Finset.range k, (δ : ℂ) * X (ν i) = δ₀ * X c₀ + δ₁ * X c₁) ∧
        (δ₀ : ℂ) * X c₀ + δ₂ * X c₂ + δ₄ * X c₄ = 0) ∧
      δ₀ * deg c₀ + δ₁ * deg c₁ + δ₂ * deg c₂ + δ₃ * deg c₃ = 0 ∧
      (∀ l ∈ Finset.Icc 1 (k - 1), δ * deg (ψ l) = δ₀ * deg c₀ + δ₁ * deg c₁) ∧
      (∀ i ∈ Finset.range k, δ * deg (ν i) = δ₀ * deg c₀ + δ₁ * deg c₁) ∧
      δ₀ * deg c₀ + δ₂ * deg c₂ + δ₄ * deg c₄ = 0 := by
  obtain ⟨c₀, c₁, c₂, c₃, c₄, δ₀, δ₁, δ₂, δ₃, δ₄, δ, ψ, ν, s₀, s₁, s₂, s₃, s₄, s, hnodup, hψinj,
    hνinj, hψC, hνC, hνψ, hsub, hΘ, hE, hF, hU, hV, hrel, d15, d14, d17, d16⟩ :=
    type_star_table_coordinates_weak k hk hkpow B deg hdeg Θ E F U V hΘΘ hΘE hEE hΘF hEF hFF
      hUU hUV hVV hUΘ hVΘ hUE hVE hUF hVF hdegΘ hdegE hdegF hdegU hdegV hcong
  have hB : B = ({c₀, c₁, c₂, c₃, c₄} ∪ (Finset.Icc 1 (k - 1)).image ψ ∪
      (Finset.range k).image ν : Finset L) := by
    refine le_antisymm (fun x hx => ?_) hsub
    by_contra hnot
    simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, Finset.mem_image,
      not_or, not_exists, not_and] at hnot
    obtain ⟨⟨⟨h0, h1, h2, h3, h4⟩, hψ'⟩, hν'⟩ := hnot
    have hψ'' : ∀ l ∈ Finset.Icc 1 (k - 1), x ≠ ψ l := fun l hl e => hψ' l hl e.symm
    have hν'' : ∀ i ∈ Finset.range k, x ≠ ν i := fun i hi e => hν' i hi e.symm
    rcases hexh x hx with hUx | hVx
    · exact hUx (by rw [hU x hx]; simp [h0, h1, h2, h3, h4])
    · exact hVx (by
        rw [hV x hx, TableCoordinates.sum_ite_eq_zero_of_forall_ne hψ'',
          TableCoordinates.sum_ite_eq_zero_of_forall_ne hν'']
        simp [h1, h2, h4])
  have hcard : B.card = 2 * k + 4 := by
    have h5 : ({c₀, c₁, c₂, c₃, c₄} : Finset L).card = 5 := by
      have := List.toFinset_card_of_nodup hnodup
      simpa using this
    have hdisj1 : Disjoint ({c₀, c₁, c₂, c₃, c₄} : Finset L) ((Finset.Icc 1 (k - 1)).image ψ) := by
      rw [Finset.disjoint_left]
      intro y hy hy'
      obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp hy'
      simp only [Finset.mem_insert, Finset.mem_singleton] at hy
      obtain ⟨e0, e1, e2, e3, e4⟩ := hψC l hl
      rcases hy with e | e | e | e | e
      exacts [e0 e, e1 e, e2 e, e3 e, e4 e]
    have hdisj2 : Disjoint (({c₀, c₁, c₂, c₃, c₄} : Finset L) ∪ (Finset.Icc 1 (k - 1)).image ψ)
        ((Finset.range k).image ν) := by
      rw [Finset.disjoint_left]
      intro y hy hy'
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hy'
      simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton,
        Finset.mem_image] at hy
      obtain ⟨e0, e1, e2, e3, e4⟩ := hνC i hi
      rcases hy with (e | e | e | e | e) | ⟨l, hl, e⟩
      exacts [e0 e, e1 e, e2 e, e3 e, e4 e, hνψ i hi l hl e.symm]
    rw [hB, Finset.card_union_of_disjoint hdisj2, Finset.card_union_of_disjoint hdisj1, h5,
      Finset.card_image_of_injOn hψinj, Finset.card_image_of_injOn hνinj, Nat.card_Icc,
      Finset.card_range]
    omega
  exact ⟨c₀, c₁, c₂, c₃, c₄, δ₀, δ₁, δ₂, δ₃, δ₄, δ, ψ, ν, s₀, s₁, s₂, s₃, s₄, s, hnodup, hψinj,
    hνinj, hψC, hνC, hνψ, hB, hcard, hΘ, hE, hF, hU, hV, hrel, d15, d14, d17, d16⟩

end CFSG.Semidihedral.FieldFactorOne
