module

public import CFSG.CGT.PushingUpLit.CGT6M.FiveInvLA

public section

namespace CFSG.CGT.PushingUpLit.CGT6M

open Matrix CFSG.Open

theorem psl4_five_inverts {K : Type} [Field K] [Finite K] (hK : Nat.card K = 5)
    (z : StatedProj (StatedSL 4 K)) (hz1 : z ≠ 1) (hz2 : z * z = 1) :
    ∃ Φ : C55 →* StatedProj (StatedSL 4 K), Function.Injective Φ ∧
      ∀ u : C55, z * Φ u * z⁻¹ = (Φ u)⁻¹ := by
  classical
  have : Fintype K := Fintype.ofFinite K
  have hcard : Fintype.card K = 5 := by rw [← Nat.card_eq_fintype_card]; exact hK
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have : CharP K 5 := charP_of_card_eq_prime hcard
  obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective z
  obtain ⟨c, hc, hM⟩ := scalar_sq_of_mk_sq h hz2
  have hnon := not_scalar_of_mk_ne_one h hz1
  obtain ⟨v, hv⟩ := exists_linearIndependent_of_not_scalar _ hnon
  obtain ⟨w₁, w₂, hw, h11, h12, h21, h22⟩ :=
    exists_two_annihilators v (((h : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *ᵥ v)
  set M : Matrix (Fin 4) (Fin 4) K := ((h : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) with hMdef
  have hAA := invNil_mul M hM v w₁ w₁ h11 h12
  have hAB := invNil_mul M hM v w₁ w₂ h11 h12
  have hBA := invNil_mul M hM v w₂ w₁ h21 h22
  have hBB := invNil_mul M hM v w₂ w₂ h21 h22
  have hH : ∀ a b : ZMod 5, Tu hAA hAB hBA hBB (zi K a) (zi K b) ∈ StatedSL 4 K := fun a b =>
    Subgroup.subset_closure (det_Ehom_eq_one hAA hAB hBA hBB (Multiplicative.ofAdd (a, b)))
  have hind : ∀ a b : ZMod 5, zi K a • invNil M c v w₁ + zi K b • invNil M c v w₂ = 0 →
      a = 0 ∧ b = 0 := by
    intro a b hab
    have h0 : invNil M c v (zi K a • w₁ + zi K b • w₂) = 0 := by
      rw [invNil_add, invNil_smul, invNil_smul]
      exact hab
    have h1 := eq_zero_of_invNil_eq_zero M c hv h0
    rw [LinearIndependent.pair_iff] at hw
    obtain ⟨ha, hb⟩ := hw _ _ h1
    exact ⟨(zi K).injective (by rw [ha, map_zero]), (zi K).injective (by rw [hb, map_zero])⟩
  exact inverted_c55_proj (StatedSL 4 K) (h : GL (Fin 4) K) h.2 hAA hAB hBA hBB
    (mul_invNil M hc hM v w₁) (mul_invNil M hc hM v w₂) hH hind

end CFSG.CGT.PushingUpLit.CGT6M
