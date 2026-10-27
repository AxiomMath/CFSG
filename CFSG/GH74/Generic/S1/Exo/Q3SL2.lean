module

public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card

public section

namespace CFSG.GH74.Generic.S1.Exo

open scoped MatrixGroups

private def sl2MapEquiv {R S : Type*} [CommRing R] [CommRing S] (f : R ≃+* S) :
    SL(2, R) ≃* SL(2, S) where
  toFun := Matrix.SpecialLinearGroup.map f.toRingHom
  invFun := Matrix.SpecialLinearGroup.map f.symm.toRingHom
  left_inv A := by ext i j; simp
  right_inv A := by ext i j; simp
  map_mul' := map_mul _

theorem sl2_equiv_zmod3 {F₀ : Type} [Field F₀] [Finite F₀] (h : Nat.card F₀ = 3) :
    Nonempty (SL(2, F₀) ≃* SL(2, ZMod 3)) := by
  have := Fintype.ofFinite F₀
  have hc : Fintype.card F₀ = Fintype.card (ZMod 3) := by
    rw [Fintype.card_eq_nat_card, h, ZMod.card]
  exact ⟨sl2MapEquiv (FiniteField.ringEquivOfCardEq hc)⟩

theorem natCard_sl2_three {F₀ : Type} [Field F₀] [Finite F₀] (h : Nat.card F₀ = 3) :
    Nat.card SL(2, F₀) = 24 := by
  obtain ⟨e⟩ := sl2_equiv_zmod3 h
  rw [Nat.card_congr e.toEquiv, Matrix.card_SL_field (𝔽 := ZMod 3) 2, ZMod.card, Fin.prod_univ_two]
  norm_num

private def w₁ : SL(2, ZMod 3) := ⟨!![0, 1; -1, 0], by simp [Matrix.det_fin_two]⟩

private def w₂ : SL(2, ZMod 3) := ⟨!![1, 1; 0, 1], by simp [Matrix.det_fin_two]⟩

private theorem not_conj_mem_of_order_three : ∀ g : SL(2, ZMod 3), g ≠ 1 → g ^ 3 = 1 →
    ¬ ((w₁ * g = g * w₁ ∨ w₁ * g = g ^ 2 * w₁) ∧ (w₂ * g = g * w₂ ∨ w₂ * g = g ^ 2 * w₂)) := by
  decide

private theorem normal_odd_eq_bot_zmod3 (N : Subgroup SL(2, ZMod 3)) [N.Normal]
    (hodd : Odd (Nat.card N)) : N = ⊥ := by
  have h24 : Nat.card SL(2, ZMod 3) = 24 := by
    rw [Matrix.card_SL_field (𝔽 := ZMod 3) 2, ZMod.card, Fin.prod_univ_two]
    norm_num
  have hdvd : Nat.card N ∣ 24 := h24 ▸ Subgroup.card_subgroup_dvd_card N
  have hcard : ∀ n : ℕ, n ∣ 24 → Odd n → n = 1 ∨ n = 3 := by
    intro n hn ho
    have hle : n ≤ 24 := Nat.le_of_dvd (by norm_num) hn
    rw [Nat.odd_iff] at ho
    interval_cases n <;> omega
  rcases hcard _ hdvd hodd with h1 | h3
  · exact Subgroup.eq_bot_of_card_eq N h1
  · exfalso
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have hne : N ≠ ⊥ := by
      intro hb
      rw [hb, Subgroup.card_bot] at h3
      omega
    obtain ⟨a, ha⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hne
    have hg1 : (a : SL(2, ZMod 3)) ≠ 1 := fun h => ha (Subtype.ext h)
    have hg3 : (a : SL(2, ZMod 3)) ^ 3 = 1 := by
      have := pow_card_eq_one' (G := N) (x := a)
      rw [h3] at this
      exact congrArg Subtype.val this
    have hord : orderOf (a : SL(2, ZMod 3)) = 3 := orderOf_eq_prime hg3 hg1
    have hcl : ∀ w : SL(2, ZMod 3),
        w * (a : SL(2, ZMod 3)) = (a : SL(2, ZMod 3)) * w ∨
          w * (a : SL(2, ZMod 3)) = (a : SL(2, ZMod 3)) ^ 2 * w := by
      intro w
      have hmem : w * (a : SL(2, ZMod 3)) * w⁻¹ ∈ N := Subgroup.Normal.conj_mem ‹_› _ a.2 w
      obtain ⟨n, hn⟩ := (Submonoid.mem_powers_iff _ _).1
        (mem_powers_of_prime_card h3 ha (g' := (⟨_, hmem⟩ : N)))
      have hn' : (a : SL(2, ZMod 3)) ^ n = w * (a : SL(2, ZMod 3)) * w⁻¹ :=
        congrArg Subtype.val hn
      have hmod : (a : SL(2, ZMod 3)) ^ (n % 3) = (a : SL(2, ZMod 3)) ^ n := by
        have := pow_mod_orderOf (a : SL(2, ZMod 3)) n
        rwa [hord] at this
      have hn'' : (a : SL(2, ZMod 3)) ^ (n % 3) * w = w * (a : SL(2, ZMod 3)) := by
        rw [hmod, hn', inv_mul_cancel_right]
      have : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by omega
      rcases this with h0 | h0 | h0
      · exfalso
        rw [h0, pow_zero, one_mul] at hn''
        have h' : w * (a : SL(2, ZMod 3)) = w * 1 := by rw [mul_one]; exact hn''.symm
        exact hg1 (mul_left_cancel h')
      · rw [h0, pow_one] at hn''
        exact Or.inl hn''.symm
      · rw [h0] at hn''
        exact Or.inr hn''.symm
    exact not_conj_mem_of_order_three _ hg1 hg3 ⟨hcl w₁, hcl w₂⟩

theorem sl23_no_odd_normal {J : Type} [Group J] {F₀ : Type} [Field F₀] [Finite F₀]
    (h : Nat.card F₀ = 3) (e : SL(2, F₀) ≃* J) (N : Subgroup J) [N.Normal]
    (hodd : Odd (Nat.card N)) : N = ⊥ := by
  obtain ⟨e₀⟩ := sl2_equiv_zmod3 h
  let φ : J ≃* SL(2, ZMod 3) := e.symm.trans e₀
  have hN : (N.map φ.toMonoidHom).Normal := Subgroup.Normal.map ‹_› _ φ.surjective
  have hcard : Nat.card (N.map φ.toMonoidHom) = Nat.card N :=
    Subgroup.card_map_of_injective φ.injective
  have := normal_odd_eq_bot_zmod3 (N.map φ.toMonoidHom) (hcard ▸ hodd)
  exact (Subgroup.map_eq_bot_iff_of_injective N φ.injective).1 this

end CFSG.GH74.Generic.S1.Exo
