module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4FBlocks
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4FFour

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

theorem sec4F_dihedral {G : Type} [Group G] {y p κ : G} (hy : y * y = 1) (hp : p * p = 1)
    (hκ : (p * y) * (p * y) * ((p * y) * (p * y)) = κ) : ∃ k : G, y * κ = k⁻¹ * y * k := by
  refine ⟨(p * y) * (p * y), ?_⟩
  have hy' : y⁻¹ = y := inv_eq_of_mul_eq_one_right hy
  have hp' : p⁻¹ = p := inv_eq_of_mul_eq_one_right hp
  rw [← hκ]
  simp only [mul_inv_rev, hy', hp', inv_inv]
  group

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {z : G} {A B P : Subgroup G}
  {x : G} {φ : (Fin 7 → ZMod 2) → G}

private lemma sec4F_conj_mul_of_sq_one {G : Type*} [Group G] {y u v : G} (hyy : y * y = 1) :
    y * (u * v) * y = (y * u * y) * (y * v * y) := by
  rw [show (y * u * y) * (y * v * y) = y * u * (y * y) * v * y by group, hyy]
  group

theorem Sec4FSetup.K_fixed (h : Sec4FSetup t L S z A B φ) (hT : Sec4FTwo A P x) {y : G}
    (hy : ∃ g : G, y = g⁻¹ * t * g)
    (h1 : ∀ a, ∃ e, y * sec4MPt t φ a * y = sec4FD t φ x e)
    {a a' c c' : Option (Fin 7)} (hb : Sec4FBlock (sec4FR t φ x) a a' c c')
    (hfix : y * (sec4MPt t φ a * sec4MPt t φ a') * y = sec4MPt t φ a * sec4MPt t φ a') :
    ∃ k : G, y * (sec4MPt t φ a * sec4MPt t φ a') = k⁻¹ * t * k := by
  obtain ⟨g, hg⟩ := hy
  have hyy : y * y = 1 := by
    rw [hg]
    calc (g⁻¹ * t * g) * (g⁻¹ * t * g) = g⁻¹ * (t * t) * g := by group
      _ = 1 := by rw [h.t_sq]; group
  have hκ : sec4MPt t φ a * sec4MPt t φ a' = sec4FD t φ x c * sec4FD t φ x c' :=
    h.block_kappa hT hb
  obtain ⟨e₁, he₁⟩ := h1 a
  obtain ⟨e₂, he₂⟩ := h1 a'
  have he12 : e₁ ≠ e₂ := by
    intro heq
    have h12 : y * sec4MPt t φ a * y = y * sec4MPt t φ a' * y := by rw [he₁, he₂, heq]
    exact hb.1 (h.pt_injective (mul_left_cancel (mul_right_cancel h12)))
  have hκ' : y * (sec4MPt t φ a * sec4MPt t φ a') * y
      = sec4FD t φ x e₁ * sec4FD t φ x e₂ := by
    rw [← he₁, ← he₂, sec4F_conj_mul_of_sq_one hyy]
  have hprod : sec4FD t φ x e₁ * sec4FD t φ x e₂ = sec4FD t φ x c * sec4FD t φ x c' := by
    rw [← hκ', hfix, hκ]
  have hprod_pt : sec4MPt t φ e₁ * sec4MPt t φ e₂ = sec4MPt t φ c * sec4MPt t φ c' := by
    have hx : x⁻¹ * (sec4MPt t φ e₁ * sec4MPt t φ e₂) * x
        = x⁻¹ * (sec4MPt t φ c * sec4MPt t φ c') * x := by
      calc x⁻¹ * (sec4MPt t φ e₁ * sec4MPt t φ e₂) * x
          = sec4FD t φ x e₁ * sec4FD t φ x e₂ := by simp only [sec4FD]; group
        _ = sec4FD t φ x c * sec4FD t φ x c' := hprod
        _ = x⁻¹ * (sec4MPt t φ c * sec4MPt t φ c') * x := by simp only [sec4FD]; group
    exact mul_left_cancel (mul_right_cancel hx)
  have hswap : Equiv.swap c c' e₁ = e₂ := by
    rcases h.pair_eq he12 hb.2.1 hprod_pt with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp
  have hpt_sq : sec4MPt t φ a * sec4MPt t φ a = 1 := h.A_sq (sec4MPt_mem_A h.data a)
  have hpd : sec4MPt t φ a * sec4FD t φ x e₁ * (sec4MPt t φ a)⁻¹ = sec4FD t φ x e₂ := by
    rw [(h.block_act hT hb).1 e₁, hswap]
  have hsq : (sec4MPt t φ a * sec4FD t φ x e₁) * (sec4MPt t φ a * sec4FD t φ x e₁)
      = sec4MPt t φ a * sec4MPt t φ a' := by
    have hpinv : (sec4MPt t φ a)⁻¹ = sec4MPt t φ a := inv_eq_of_mul_eq_one_right hpt_sq
    calc (sec4MPt t φ a * sec4FD t φ x e₁) * (sec4MPt t φ a * sec4FD t φ x e₁)
        = (sec4MPt t φ a * sec4FD t φ x e₁ * (sec4MPt t φ a)⁻¹) * sec4FD t φ x e₁ := by
          rw [hpinv]; group
      _ = sec4FD t φ x e₂ * sec4FD t φ x e₁ := by rw [hpd]
      _ = sec4FD t φ x e₁ * sec4FD t φ x e₂ := (h.d_comm e₁ e₂).symm
      _ = sec4MPt t φ a * sec4MPt t φ a' := by rw [hprod, ← hκ]
  have hκ4 : (sec4MPt t φ a * y) * (sec4MPt t φ a * y)
        * ((sec4MPt t φ a * y) * (sec4MPt t φ a * y))
      = sec4MPt t φ a * sec4MPt t φ a' := by
    have hry : (sec4MPt t φ a * y) * (sec4MPt t φ a * y)
        = sec4MPt t φ a * sec4FD t φ x e₁ := by
      calc (sec4MPt t φ a * y) * (sec4MPt t φ a * y)
          = sec4MPt t φ a * (y * sec4MPt t φ a * y) := by group
        _ = sec4MPt t φ a * sec4FD t φ x e₁ := by rw [he₁]
    rw [hry]
    exact hsq
  obtain ⟨k, hk⟩ := sec4F_dihedral hyy hpt_sq hκ4
  refine ⟨g * k, ?_⟩
  rw [hk, hg]
  group

end CFSG.OddStandard.SmallF3.Omega
