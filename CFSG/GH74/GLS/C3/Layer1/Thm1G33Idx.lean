module

public import CFSG.GH74.GLS.C3.Layer1.Thm1G33Env

public section

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.GLS.IVK CFSG.GH74.GLS.C3.Layer1
  CFSG.GH74.GLS.C3.Layer1.Thm1
open scoped commutatorElement Pointwise

namespace CFSG.GH74.GLS.C3.Layer1.Thm1G33

section Idx

variable {G : Type} [Group G] [Finite G] {x y : G} {K T V W : Subgroup G} {f z : G}

theorem factorization_two_of_eq {a b c : ℕ} (h : a = b * (2 * c)) (hc : Odd c) (hb : b ≠ 0) :
    a.factorization 2 = b.factorization 2 + 1 := by
  have hc0 : c ≠ 0 := hc.pos.ne'
  have h2c : (2 * c).factorization 2 = 1 := by
    rw [Nat.factorization_mul (by norm_num) hc0, Finsupp.add_apply,
      Nat.Prime.factorization_self Nat.prime_two,
      Nat.factorization_eq_zero_of_not_dvd (by simpa [Nat.odd_iff, Nat.two_dvd_ne_zero] using hc)]
  rw [h, Nat.factorization_mul hb (by omega), Finsupp.add_apply, h2c]

theorem Env33.hPcard (E : Env33 x y K T V W f z) :
    Nat.card ↥(T ⊓ K) = 2 * Nat.card ↥((T ⊓ K) ⊓ layerI K f) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨r, hrodd, hr5, hI, hKshape⟩ := E.hr
  have hexp : (Nat.card (kBar K)).factorization 2 =
      (Nat.card (kBar (layerI K f))).factorization 2 + 1 := by
    have hIcard := Thm1L34.card_kBar_of_hasL2Model hI
    obtain ⟨k, hk⟩ := hrodd
    have hk2 : 2 ≤ k := by omega
    rcases hKshape with hK2 | ⟨hr5', hKA7⟩
    · rw [Thm1L34.card_kBar_of_hasL2Model hK2, hIcard, hk]
      have hr2 : (2 * k + 1) ^ 2 = 2 * (2 * (k * (k + 1))) + 1 := by ring
      rw [hr2, PumpClass.ordA_one_odd, PumpClass.ordA_one_odd]
      refine factorization_two_of_eq (c := (2 * (k * (k + 1)) + 1) * (2 * k + 1)) ?_ ?_ ?_
      · ring
      · exact (odd_two_mul_add_one _).mul (odd_two_mul_add_one k)
      · have : 0 < k := by omega
        positivity
    · rw [Thm1L34.card_kBar_of_alt7 hKA7, hIcard, hr5']
      have h60 : Open.ordA 1 5 = 60 := by decide
      rw [h60]
      exact factorization_two_of_eq (c := 21) (by norm_num) (by decide) (by norm_num)
  rw [E.hPK.card_eq, E.hPI.card_eq, factorization_kBar K, factorization_kBar (layerI K f), hexp,
    pow_succ]
  ring


theorem Env33.hP_index_two (E : Env33 x y K T V W f z) :
    ∀ p ∈ T ⊓ K, ∀ q ∈ T ⊓ K, p ∉ layerI K f → q ∉ layerI K f → p⁻¹ * q ∈ layerI K f := by
  intro p hp q hq hpI hqI
  set P₁ : Subgroup G := (T ⊓ K) ⊓ layerI K f with hP₁
  set P₁' : Subgroup ↥(T ⊓ K) := P₁.subgroupOf (T ⊓ K) with hP₁'
  have hP₁le : P₁ ≤ T ⊓ K := inf_le_left
  have hcard : Nat.card ↥P₁' = Nat.card ↥P₁ :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hP₁le).toEquiv
  have hidx : P₁'.index = 2 := by
    have h := Subgroup.card_mul_index P₁'
    rw [hcard, E.hPcard] at h
    have hpos : 0 < Nat.card ↥P₁ := Nat.card_pos
    have : Nat.card ↥P₁ * P₁'.index = Nat.card ↥P₁ * 2 := by rw [h]; ring
    exact Nat.eq_of_mul_eq_mul_left hpos this
  have h1 : (⟨p⁻¹, (T ⊓ K).inv_mem hp⟩ : ↥(T ⊓ K)) ∈ P₁' ↔ (⟨q, hq⟩ : ↥(T ⊓ K)) ∈ P₁' := by
    constructor
    · intro h
      exact absurd (by simpa using ((Subgroup.mem_subgroupOf.1 h).2)) hpI
    · intro h
      exact absurd (Subgroup.mem_subgroupOf.1 h).2 hqI
  have h2 := (Subgroup.mul_mem_iff_of_index_two hidx).2 h1
  have h3 : p⁻¹ * q ∈ P₁ := Subgroup.mem_subgroupOf.1 h2
  exact h3.2

end Idx

end CFSG.GH74.GLS.C3.Layer1.Thm1G33
