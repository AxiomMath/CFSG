module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4FSetup

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {z : G} {A B : Subgroup G}
  {φ : (Fin 7 → ZMod 2) → G}

theorem Sec4FSetup.four_pts (h : Sec4FSetup t L S z A B φ) {p q r s : Option (Fin 7)}
    (hpq : p ≠ q) (hpr : p ≠ r) (hps : p ≠ s) (hqr : q ≠ r) (hqs : q ≠ s) (hrs : r ≠ s) :
    (∃ k : G, sec4MPt t φ p * sec4MPt t φ q * (sec4MPt t φ r * sec4MPt t φ s) = k⁻¹ * z * k) ∧
      sec4MPt t φ p * sec4MPt t φ q * (sec4MPt t φ r * sec4MPt t φ s) ≠ 1 := by
  have hw_even : IsEvenVec (sec4MV p + sec4MV q + sec4MV r + sec4MV s) :=
    isEvenVec_add (isEvenVec_add (isEvenVec_add (sec4MV_even p) (sec4MV_even q))
      (sec4MV_even r)) (sec4MV_even s)
  have hw_weight : vecWeight (sec4MV p + sec4MV q + sec4MV r + sec4MV s) = 4 :=
    sec4MV_weight_four hpq hpr hps hqr hqs hrs
  have hw0 : sec4MV p + sec4MV q + sec4MV r + sec4MV s ≠ 0 := by
    intro hw
    have hzero : vecWeight (0 : Fin 7 → ZMod 2) = 0 := by simp [vecWeight]
    rw [hw] at hw_weight
    omega
  rw [sec4MPt_mul_four h.data]
  constructor
  · have hv : IsI4PlusIn L (φ (sec4MV p + sec4MV q + sec4MV r + sec4MV s)) :=
      (h.data.bdata.type4 _ hw_even hw0).mp hw_weight
    obtain ⟨l, hl, hlw⟩ := h.inputs.hf43c G L h.omega7 z _ h.ctx.pocket hv
    exact ⟨l⁻¹, by rw [hlw, inv_inv]⟩
  · intro h1
    have h0 : φ (sec4MV p + sec4MV q + sec4MV r + sec4MV s) = φ 0 := by
      rw [h1, IsPermModuleVia.map_zero h.data.bdata.perm]
    exact hw0 (h.data.bdata.perm.2.1 _ _ hw_even (by simp [IsEvenVec]) h0)

theorem Sec4FSetup.pair_eq (h : Sec4FSetup t L S z A B φ) {g₁ g₂ a a' : Option (Fin 7)}
    (hg : g₁ ≠ g₂) (ha : a ≠ a')
    (hprod : sec4MPt t φ g₁ * sec4MPt t φ g₂ = sec4MPt t φ a * sec4MPt t φ a') :
    (g₁ = a ∧ g₂ = a') ∨ (g₁ = a' ∧ g₂ = a) := by
  have hinj := sec4MPt_injective h.data
  have hcomm : ∀ p q, sec4MPt t φ p * sec4MPt t φ q = sec4MPt t φ q * sec4MPt t φ p :=
    fun p q => h.A_comm (sec4MPt_mem_A h.data p) (sec4MPt_mem_A h.data q)
  have hsq : ∀ p, sec4MPt t φ p * sec4MPt t φ p = 1 :=
    fun p => h.A_sq (sec4MPt_mem_A h.data p)
  rcases eq_or_ne g₁ a with h1 | h1
  · left
    refine ⟨h1, ?_⟩
    rw [h1] at hprod
    exact hinj (mul_left_cancel hprod)
  rcases eq_or_ne g₁ a' with h2 | h2
  · right
    refine ⟨h2, ?_⟩
    rw [h2, hcomm a a'] at hprod
    exact hinj (mul_left_cancel hprod)
  rcases eq_or_ne g₂ a with h3 | h3
  · right
    refine ⟨?_, h3⟩
    rw [h3] at hprod
    have h4 : sec4MPt t φ g₁ * sec4MPt t φ a = sec4MPt t φ a' * sec4MPt t φ a := by
      rw [hprod, hcomm a a']
    exact hinj (mul_right_cancel h4)
  rcases eq_or_ne g₂ a' with h4 | h4
  · left
    refine ⟨?_, h4⟩
    rw [h4] at hprod
    exact hinj (mul_right_cancel hprod)
  exfalso
  obtain ⟨-, hne1⟩ := h.four_pts hg h1 h2 h3 h4 ha
  apply hne1
  rw [hprod]
  calc sec4MPt t φ a * sec4MPt t φ a' * (sec4MPt t φ a * sec4MPt t φ a')
      = sec4MPt t φ a * (sec4MPt t φ a' * sec4MPt t φ a) * sec4MPt t φ a' := by group
    _ = sec4MPt t φ a * (sec4MPt t φ a * sec4MPt t φ a') * sec4MPt t φ a' := by
        rw [hcomm a' a]
    _ = (sec4MPt t φ a * sec4MPt t φ a) * (sec4MPt t φ a' * sec4MPt t φ a') := by group
    _ = 1 := by rw [hsq a, hsq a', mul_one]

end CFSG.OddStandard.SmallF3.Omega
