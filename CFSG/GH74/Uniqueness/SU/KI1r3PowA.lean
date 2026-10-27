module

public import CFSG.Quasithin.Background.D2Involutions

public section

namespace CFSG.GH74.Uniqueness.SU.K.R3.Pow

open CFSG.Quasithin

variable {V : Type} [Group V] [Finite V]

theorem exists_eq_mul_map_of_fixed (hcomm : ∀ a b : V, a * b = b * a) (hsq : ∀ a : V, a * a = 1)
    (σ τ : MulAut V) (hτ : τ ^ 2 = 1) (hστ : τ * σ * τ⁻¹ = σ⁻¹) (hfix : ∀ v, σ v = v → v = 1)
    (v : V) (hv : τ v = v) : ∃ w : V, v = w * τ w := by
  let _ : CommGroup V := { ‹Group V› with mul_comm := hcomm }
  have hV : ∀ v : V, v ^ 2 = 1 := fun v => by rw [pow_two]; exact hsq v
  have hfixσ : fixV (Subgroup.zpowers σ) = ⊥ := by
    rw [eq_bot_iff]
    intro v hv
    exact Subgroup.mem_bot.mpr (hfix v (mem_fixV_zpowers_iff.mp hv))
  have h := fixV_eq_commV_of_inverts hV hfixσ hτ hστ
  have hv' : v ∈ commV (Subgroup.zpowers τ) := h ▸ mem_fixV_zpowers_iff.mpr hv
  rw [commV_zpowers_eq_map] at hv'
  obtain ⟨u, -, hu⟩ := Subgroup.mem_map.mp hv'
  refine ⟨u, ?_⟩
  rw [← hu, commHom_apply, inv_eq_self_of_sq_eq_one hV u, mul_comm]

theorem orderOf_eq_of_card_fixed_le_four (hcomm : ∀ a b : V, a * b = b * a)
    (hsq : ∀ a : V, a * a = 1) (σ τ : MulAut V) (hτ : τ ^ 2 = 1) (hστ : τ * σ * τ⁻¹ = σ⁻¹)
    (hfix : ∀ v, σ v = v → v = 1) (hodd : Odd (orderOf σ))
    (hc : Nat.card {v : V // τ v = v} ≤ 4) : σ = 1 ∨ orderOf σ = 3 ∨ orderOf σ = 5 := by
  by_cases hσ1 : σ = 1
  · exact Or.inl hσ1
  right
  let _ : CommGroup V := { ‹Group V› with mul_comm := hcomm }
  have hV : ∀ v : V, v ^ 2 = 1 := fun v => by rw [pow_two]; exact hsq v
  have hfixσ : fixV (Subgroup.zpowers σ) = ⊥ := by
    rw [eq_bot_iff]
    intro v hv
    exact Subgroup.mem_bot.mpr (hfix v (mem_fixV_zpowers_iff.mp hv))
  have hrk2 := rk_eq_two_mul_of_inverts hV hfixσ hτ hστ
  have hfixτ := fixV_eq_commV_of_inverts hV hfixσ hτ hστ
  have hcardF : Nat.card (fixV (Subgroup.zpowers τ)) = Nat.card {v : V // τ v = v} :=
    Nat.card_congr (Equiv.subtypeEquivRight fun v => mem_fixV_zpowers_iff)
  have hrkF : rk (fixV (Subgroup.zpowers τ)) ≤ 2 := by
    have h1 := card_eq_two_pow hV (fixV (Subgroup.zpowers τ))
    rw [hcardF] at h1
    have h2 : 2 ^ rk (fixV (Subgroup.zpowers τ)) ≤ 2 ^ 2 := by rw [← h1]; simpa using hc
    exact (Nat.pow_le_pow_iff_right (by norm_num)).mp h2
  have hrkV : rk V ≤ 4 := by rw [hrk2, ← hfixτ]; omega
  rcases small_dihedral hV hodd hσ1 hfixσ hτ hστ hrkV with ⟨-, h3⟩ | ⟨-, h35⟩
  · exact Or.inl h3
  · exact h35

end CFSG.GH74.Uniqueness.SU.K.R3.Pow
