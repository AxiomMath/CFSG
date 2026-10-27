module

public import CFSG.LargeExtraspecial.GLW4Order

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.GLW4

open Subgroup CFSG.LargeExtraspecial.GLR CFSG.GH74.GLS.Bg.Thompson

variable {G : Type*} [Group G] [Finite G] {S : Setting G}

theorem false_of_sylowIn_le [IsSimpleGroup G] (C : Config S) (h4 : S.width = 4) {τ : G}
    (hτM : τ ∈ S.M) (hτX : τ ∉ C.X) (hττ : τ * τ = 1) {S₁ : Subgroup G}
    (hS₁ : IsSylowIn 2 S₁ (centralizer {τ} ⊓ S.M)) (hS₁G : IsSylowIn 2 S₁ (centralizer {τ}))
    (hcard : Nat.card S₁ ≤ 2 ^ 10) : False := by
  have hv : (Nat.card (centralizer {τ})).factorization 2 ≤ 10 := by
    rw [card_eq_of_sylowIn hS₁G] at hcard
    exact (Nat.pow_le_pow_iff_right (by norm_num)).mp hcard
  have hτS₁ := Levi.mem_of_sylowIn hτM hττ hS₁
  obtain ⟨T, hS₁T, hT⟩ := exists_isSylowIn_le (H := S.M) (fun t ht => (SylowIn.le hS₁ ht).2)
    (SylowIn.isPGroup hS₁)
  have hTG := Config.sylowIn_top hT
  have hτT := hS₁T hτS₁
  have hUidx := C.relIndex_inf_X (SylowIn.le hT) hτT hτX
  obtain ⟨x, hxU, -⟩ := exists_extremal_conj_mem_of_sq_eq_of_isSimpleGroup C.exists_mul_ne
    (SylowIn.isPGroup hTG) (not_dvd_index_of_sylowIn_top hTG) inf_le_left hUidx hτT
    (fun h => hτX h.2) hττ (mul_one 1) (fun x _ => by simp)
  have hyX : x⁻¹ * τ * x ∈ C.X := hxU.2
  have hyy : (x⁻¹ * τ * x) * (x⁻¹ * τ * x) = 1 := by
    calc (x⁻¹ * τ * x) * (x⁻¹ * τ * x) = x⁻¹ * (τ * τ) * x := by group
      _ = 1 := by rw [hττ, mul_one, inv_mul_cancel]
  have h34 := lt_factorization_card_centralizer_four C h4 (C.X_le_normalizer hyX) hyy
  rw [card_centralizer_conj] at h34
  omega

end CFSG.LargeExtraspecial.GLW4
