module

public import Mathlib.FieldTheory.Finite.GaloisField
public import CFSG.Quasithin.Vol2.Ch3E213MG41SZ5

public section

namespace CFSG.GH74.Tits83

universe u

theorem exists_ringEquiv_comm {K K' : Type u} [Field K] [Field K'] [Finite K] [Finite K']
    (σ : K →+* K) (σ' : K' →+* K') (hσ : ∀ t, σ (σ t) = t ^ 2)
    (hσ' : ∀ t, σ' (σ' t) = t ^ 2) [CharP K 2] [CharP K' 2]
    (h : Nat.card K = Nat.card K') :
    ∃ θ : K ≃+* K', ∀ t, θ (σ t) = σ' (θ t) := by
  letI : Fintype K := Fintype.ofFinite K
  letI : Fintype K' := Fintype.ofFinite K'
  by_cases h2 : Nat.card K = 2
  ·
    have h2' : Nat.card K' = 2 := h.symm ▸ h2
    have hK : ∀ x : K, x = 0 ∨ x = 1 := by
      intro x
      by_cases hx : x = 0
      · exact Or.inl hx
      · right
        rcases (Nat.card_eq_two_iff' (0 : K)).mp h2 with ⟨y, _, hyuniq⟩
        exact (hyuniq x hx).trans (hyuniq 1 one_ne_zero).symm
    have hK' : ∀ x : K', x = 0 ∨ x = 1 := by
      intro x
      by_cases hx : x = 0
      · exact Or.inl hx
      · right
        rcases (Nat.card_eq_two_iff' (0 : K')).mp h2' with ⟨y, _, hyuniq⟩
        exact (hyuniq x hx).trans (hyuniq 1 one_ne_zero).symm
    have hσid : σ = RingHom.id K := by
      ext x
      rcases hK x with rfl | rfl <;> simp
    have hσ'id : σ' = RingHom.id K' := by
      ext x
      rcases hK' x with rfl | rfl <;> simp
    let θ : K ≃+* K' := FiniteField.ringEquivOfCardEq (by
      simpa only [Nat.card_eq_fintype_card] using h)
    refine ⟨θ, ?_⟩
    intro t
    rw [hσid, hσ'id]
    rfl
  ·
    have h3 : 2 < Nat.card K := by
      have := Finite.one_lt_card (α := K)
      omega
    have h3' : 2 < Nat.card K' := by
      rw [← h]
      exact h3
    obtain ⟨a, -, hcard, hpow⟩ :=
      CFSG.Quasithin.Ch3E213M.G41.CTwo.exists_eq_pow_of_comp_eq_sq σ hσ h3
    obtain ⟨a', -, hcard', hpow'⟩ :=
      CFSG.Quasithin.Ch3E213M.G41.CTwo.exists_eq_pow_of_comp_eq_sq σ' hσ' h3'
    have hlin : 2 * a + 1 = 2 * a' + 1 := by
      refine Nat.pow_right_injective (le_refl 2) ?_
      calc
        2 ^ (2 * a + 1) = Nat.card K := hcard.symm
        _ = Nat.card K' := h
        _ = 2 ^ (2 * a' + 1) := hcard'
    have ha : a = a' := by omega
    let θ : K ≃+* K' := FiniteField.ringEquivOfCardEq (by
      simpa only [Nat.card_eq_fintype_card] using h)
    refine ⟨θ, ?_⟩
    intro t
    rw [hpow t, hpow' (θ t), ← ha]
    exact map_pow θ t (2 ^ (a + 1))

end CFSG.GH74.Tits83
