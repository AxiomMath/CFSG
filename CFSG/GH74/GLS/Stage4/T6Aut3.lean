module

public import CFSG.GH74.GLS.Stage4.T2SL3O

public section

namespace CFSG.GH74.GLS.Stage4.Rest.T2

open Equiv CFSG.GH74.GLS.Stage4.Hex

theorem t6_s4_cent : ∀ c σ : Perm (Fin 4), c ^ 3 = 1 → c ≠ 1 → σ * c = c * σ →
    σ = 1 ∨ σ = c ∨ σ = c ^ 2 := by
  decide

theorem t6_aut_fix_u3 {F : Type} [Field F] [Finite F] (h3 : Nat.card F = 3) (α : MulAut (SL2 F))
    (hα : ∀ c : F, α (sl2U c) = sl2U c) :
    ∃ s : F, ∀ g : SL2 F, α g = sl2U s * g * (sl2U s)⁻¹ := by
  have : Fintype F := Fintype.ofFinite F
  have hc : Fintype.card F = Fintype.card (ZMod 3) := by
    rw [← Nat.card_eq_fintype_card, h3, ZMod.card]
  let r : F ≃+* ZMod 3 := FiniteField.ringEquivOfCardEq hc
  let e : SL2 F ≃* SL2 (ZMod 3) := t2oc3_slRingEquiv r
  let Θ : MulAut (SL2 F) →* Perm (Fin 4) := t2oc3_Theta.comp (MulAut.congr e).toMonoidHom
  have hΘ : Function.Injective Θ := t2oc3_Theta_injective.comp (MulAut.congr e).injective
  have hz3 : (3 : F) = 0 := by
    have : (3 : ℕ) • (1 : F) = 0 := by rw [← h3]; exact card_nsmul_eq_zero'
    simpa using this
  have h2 : (2 : F) ≠ 0 := by
    intro h
    have : (1 : F) = 0 := by linear_combination hz3 - h
    exact one_ne_zero this
  have hx1 := (t2C_sl2U_ne h2).1
  have hx2 := (t2C_sl2U_ne h2).2
  have hx3 : (sl2U (1 : F)) ^ 3 = 1 := by
    rw [t2A_sl2U_pow]
    have : ((3 : ℕ) : F) * 1 = 0 := by simpa using hz3
    rw [this, sl2U_zero]
  have hxc : sl2U (1 : F) ∉ Subgroup.center (SL2 F) := by
    intro h
    rcases (t2C_center_sl2 _).1 h with h | h
    · exact hx1 h
    · exact hx2 h
  have hcx : (MulAut.conj (sl2U (1 : F)) : MulAut (SL2 F)) ≠ 1 := by
    intro h
    apply hxc
    rw [Subgroup.mem_center_iff]
    intro g
    have := congrArg (fun f : MulAut (SL2 F) => f g) h
    simp only [MulAut.conj_apply, MulAut.one_apply] at this
    calc g * sl2U (1 : F) = (sl2U (1 : F) * g * (sl2U (1 : F))⁻¹) * sl2U 1 := by rw [this]
      _ = sl2U 1 * g := by group
  have hcomm : α * MulAut.conj (sl2U (1 : F)) = MulAut.conj (sl2U (1 : F)) * α := by
    ext g
    simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv, hα]
  have hc3 : Θ (MulAut.conj (sl2U (1 : F))) ^ 3 = 1 := by
    rw [← map_pow, ← map_pow, hx3, map_one, map_one]
  have hc1 : Θ (MulAut.conj (sl2U (1 : F))) ≠ 1 := by
    intro h
    exact hcx (hΘ (by rw [h, map_one]))
  have hσ : Θ α * Θ (MulAut.conj (sl2U (1 : F))) = Θ (MulAut.conj (sl2U (1 : F))) * Θ α := by
    rw [← map_mul, ← map_mul, hcomm]
  rcases t6_s4_cent _ _ hc3 hc1 hσ with h | h | h
  · refine ⟨0, fun g => ?_⟩
    have : α = 1 := hΘ (by rw [h, map_one])
    rw [this]
    simp [sl2U_zero]
  · refine ⟨1, fun g => ?_⟩
    have : α = MulAut.conj (sl2U (1 : F)) := hΘ h
    rw [this]
    exact MulAut.conj_apply _ _
  · refine ⟨2, fun g => ?_⟩
    have : α = MulAut.conj (sl2U (1 : F)) ^ 2 := hΘ (by rw [h, map_pow])
    have e2 : sl2U (2 : F) = sl2U (1 : F) ^ 2 := by
      rw [t2A_sl2U_pow]; norm_num
    have e3 : (MulAut.conj (sl2U (1 : F)) : MulAut (SL2 F)) ^ 2 = MulAut.conj (sl2U (1 : F) ^ 2) :=
      (map_pow _ _ _).symm
    rw [this, e3, ← e2]
    exact MulAut.conj_apply _ _

end CFSG.GH74.GLS.Stage4.Rest.T2
