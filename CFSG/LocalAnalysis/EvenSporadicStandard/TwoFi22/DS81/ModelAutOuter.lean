module

public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Mathlib.GroupTheory.Coset.Card
public import Mathlib.Algebra.Group.Subgroup.Finite
public import Mathlib.Tactic.NormNum.Inv
public import Mathlib.Tactic.NormNum.Pow

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81

open Subgroup

namespace AutOuter

variable {S : Type*} [Group S] {P R : Subgroup S}

theorem commute_of_fixed (ψ : R ≃* MulAut P)
    (hψ : ∀ (r : R) (g : P), ((ψ r g : P) : S) = (r : S) * g * (r : S)⁻¹) {r : R} {g : P}
    (hg : ψ r g = g) : (r : S) * g = g * r := by
  have h1 := hψ r g
  rw [hg] at h1
  exact (eq_mul_inv_iff_mul_eq.1 h1).symm

theorem aut_cent_of_centralizer (ψ : R ≃* MulAut P)
    (hψ : ∀ (r : R) (g : P), ((ψ r g : P) : S) = (r : S) * g * (r : S)⁻¹) (V : Subgroup P)
    (hC : ∀ r : R, (∀ e ∈ V, (r : S) * e = e * r) → ∃ x ∈ V, (x : S) = r) :
    ∀ α : MulAut P, (∀ e ∈ V, α e = e) → ∃ x ∈ V, α = MulAut.conj x := by
  intro α hα
  obtain ⟨r, rfl⟩ := ψ.surjective α
  obtain ⟨x, hx, hxr⟩ := hC r fun e he => commute_of_fixed ψ hψ (hα e he)
  refine ⟨x, hx, ?_⟩
  ext g
  rw [MulAut.conj_apply]
  rw [hψ, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, hxr]

theorem sq_eq_one_of_mem_closure {X : Set S} (hcomm : ∀ x ∈ X, ∀ y ∈ X, x * y = y * x)
    (hsq : ∀ x ∈ X, x ^ 2 = 1) {t : S} (ht : t ∈ closure X) : t ^ 2 = 1 := by
  have hX : X ⊆ centralizer X := fun x hx y hy => (hcomm y hy x hx)
  have hle : closure X ≤ centralizer X :=
    (closure_le_centralizer_centralizer X).trans (centralizer_le hX)
  have hcc : ∀ s ∈ closure X, ∀ t ∈ closure X, s * t = t * s := by
    intro s hs t ht
    have : s ∈ centralizer (closure X : Set S) := by
      rw [centralizer_closure]
      exact hle hs
    exact (mem_centralizer_iff.1 this t ht).symm
  induction ht using Subgroup.closure_induction with
  | mem x hx => exact hsq x hx
  | one => simp
  | mul a b ha hb iha ihb =>
    have hab := hcc b hb a ha
    calc (a * b) ^ 2 = a * (b * a) * b := by rw [pow_two]; simp only [mul_assoc]
      _ = a * (a * b) * b := by rw [hab]
      _ = a ^ 2 * b ^ 2 := by rw [pow_two, pow_two]; simp only [mul_assoc]
      _ = 1 := by rw [iha, ihb, mul_one]
  | inv a ha iha =>
    rw [inv_pow, iha, inv_one]

theorem rank_of_outer [Finite S] (ψ : R ≃* MulAut P)
    (hψ : ∀ (r : R) (g : P), ((ψ r g : P) : S) = (r : S) * g * (r : S)⁻¹) (hPR : P ≤ R)
    (hinn : (P.subgroupOf R).map ψ.toMonoidHom = (MulAut.conj : P →* MulAut P).range) {n : ℕ}
    (hrank : ∀ A : Subgroup S, A ≤ R → (∀ a ∈ A, a ^ 2 = 1) → ¬ A ≤ P →
      Nat.card A ≤ 2 ^ (n + 1)) :
    ∀ α : MulAut P, α * α = 1 → (∀ q : P, α ≠ MulAut.conj q) →
      ∀ A : Subgroup P, (∀ a ∈ A, a ^ 2 = 1) → (∀ a ∈ A, α a = a) → Nat.card A ≤ 2 ^ n := by
  intro α hα2 hαout A hA2 hAfix
  obtain ⟨r, rfl⟩ := ψ.surjective α
  have hr2 : (r : S) ^ 2 = 1 := by
    have : r * r = 1 := ψ.injective (by rw [map_mul, hα2, map_one])
    rw [pow_two, ← Subgroup.coe_mul, this, Subgroup.coe_one]
  have hrP : (r : S) ∉ P := by
    intro hrP
    have hm : ψ r ∈ (P.subgroupOf R).map ψ.toMonoidHom := ⟨r, mem_subgroupOf.2 hrP, rfl⟩
    rw [hinn] at hm
    obtain ⟨q, hq⟩ := hm
    exact hαout q hq.symm
  set A' : Subgroup S := A.map P.subtype with hA'
  have hA'P : A' ≤ P := by
    rintro _ ⟨a, -, rfl⟩
    exact a.2
  set X : Set S := (A' : Set S) ∪ {(r : S)} with hX
  have hA'sq : ∀ a ∈ A', a ^ 2 = 1 := by
    rintro _ ⟨a, ha, rfl⟩
    simpa using congrArg Subtype.val (hA2 a ha)
  have hcomm_r : ∀ a ∈ A', a * (r : S) = (r : S) * a := by
    rintro _ ⟨a, ha, rfl⟩
    exact (commute_of_fixed ψ hψ (hAfix a ha)).symm
  have hA'comm : ∀ a ∈ A', ∀ b ∈ A', a * b = b * a := by
    intro a ha b hb
    have ha1 : a⁻¹ = a := inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact hA'sq a ha)
    have hb1 : b⁻¹ = b := inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact hA'sq b hb)
    have hab1 : (a * b)⁻¹ = a * b :=
      inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact hA'sq _ (A'.mul_mem ha hb))
    calc a * b = (a * b)⁻¹ := hab1.symm
      _ = b⁻¹ * a⁻¹ := mul_inv_rev a b
      _ = b * a := by rw [ha1, hb1]
  have hXcomm : ∀ x ∈ X, ∀ y ∈ X, x * y = y * x := by
    intro x hx y hy
    rcases hx with hx | hx <;> rcases hy with hy | hy
    · exact hA'comm x hx y hy
    · rw [Set.mem_singleton_iff.1 hy]; exact hcomm_r x hx
    · rw [Set.mem_singleton_iff.1 hx]; exact (hcomm_r y hy).symm
    · rw [Set.mem_singleton_iff.1 hx, Set.mem_singleton_iff.1 hy]
  have hXsq : ∀ x ∈ X, x ^ 2 = 1 := by
    intro x hx
    rcases hx with hx | hx
    · exact hA'sq x hx
    · rw [Set.mem_singleton_iff.1 hx]; exact hr2
  set T : Subgroup S := closure X with hT
  have hTsq : ∀ t ∈ T, t ^ 2 = 1 := fun t ht => sq_eq_one_of_mem_closure hXcomm hXsq ht
  have hA'T : A' ≤ T := fun a ha => subset_closure (Or.inl ha)
  have hrT : (r : S) ∈ T := subset_closure (Or.inr rfl)
  have hrA' : (r : S) ∉ A' := fun h => hrP (hA'P h)
  have hTR : T ≤ R := by
    rw [hT, closure_le]
    rintro x (hx | hx)
    · exact hPR (hA'P hx)
    · rw [Set.mem_singleton_iff.1 hx]; exact r.2
  have hTP : ¬ T ≤ P := fun h => hrP (h hrT)
  have hbound := hrank T hTR hTsq hTP
  have hlt : Nat.card A' < Nat.card T :=
    Subgroup.card_lt_of_lt (lt_of_le_of_ne hA'T fun h => hrA' (by rw [h]; exact hrT))
  obtain ⟨k, hk⟩ := Subgroup.card_dvd_of_le hA'T
  have hAA' : Nat.card A' = Nat.card A := Subgroup.card_subtype P A
  have hk2 : 2 ≤ k := by
    by_contra hk2
    obtain rfl | rfl : k = 0 ∨ k = 1 := by omega
    · omega
    · omega
  have : 2 * Nat.card A' ≤ Nat.card T := by
    rw [hk, mul_comm 2]
    exact Nat.mul_le_mul_left _ hk2
  have h2 : 2 * Nat.card A ≤ 2 ^ (n + 1) := by rw [← hAA']; exact this.trans hbound
  rw [pow_succ] at h2
  omega

end AutOuter

end CFSG.EvenSporadicStandard.TwoFi22.DS81
