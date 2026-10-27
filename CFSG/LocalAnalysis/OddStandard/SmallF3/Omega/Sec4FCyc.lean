module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4FDelta

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {z : G} {A B : Subgroup G}
  {φ : (Fin 7 → ZMod 2) → G}

theorem Sec4FSetup.false_of_two_cycles (h : Sec4FSetup t L S z A B φ) {s : G}
    (hs : ∃ g : G, s = g⁻¹ * t * g) {σ : Equiv.Perm (Option (Fin 7))}
    (hσ : Sec4MRealizes t φ s σ) {x y : Option (Fin 7)}
    (hx : σ x ≠ x) (hy : σ y ≠ y) (hxy : y ≠ x) (hyx : y ≠ σ x) : False := by
  obtain ⟨g, hg⟩ := hs
  have hsq : s * s = 1 := by
    rw [hg]
    calc g⁻¹ * t * g * (g⁻¹ * t * g)
        = g⁻¹ * (t * t) * g := by group
      _ = g⁻¹ * 1 * g := by rw [h.t_sq]
      _ = 1 := by group
  have hσ2 : σ * σ = 1 := Sec4MRealizes.sq_eq_one h.pt_injective hσ hsq
  have hσy : σ (σ y) = y := by
    have h1 := congrArg (fun τ : Equiv.Perm (Option (Fin 7)) => τ y) hσ2
    simpa [Equiv.Perm.mul_apply] using h1
  have hxσy : x ≠ σ y := by
    intro hxy'
    have h2 : σ x = y := by rw [hxy', hσy]
    exact hyx h2.symm
  have hσxσy : σ x ≠ σ y := fun hxy2 => hxy (σ.injective hxy2).symm
  have hx_ne_y : x ≠ y := hxy.symm
  have hx_ne_σx : x ≠ σ x := hx.symm
  have hy_ne_σy : y ≠ σ y := hy.symm
  let w : Fin 7 → ZMod 2 := sec4MV x + sec4MV y + sec4MV (σ x) + sec4MV (σ y)
  have hw_even : IsEvenVec w := by
    show IsEvenVec (sec4MV x + sec4MV y + sec4MV (σ x) + sec4MV (σ y))
    exact isEvenVec_add (isEvenVec_add (isEvenVec_add (sec4MV_even x) (sec4MV_even y))
      (sec4MV_even (σ x))) (sec4MV_even (σ y))
  have hw_weight : vecWeight w = 4 := by
    show vecWeight (sec4MV x + sec4MV y + sec4MV (σ x) + sec4MV (σ y)) = 4
    exact sec4MV_weight_four hx_ne_y hx_ne_σx hxσy hyx hy_ne_σy hσxσy
  have hw0 : w ≠ 0 := by
    intro hw
    have hzero : vecWeight (0 : Fin 7 → ZMod 2) = 0 := by simp [vecWeight]
    rw [hw] at hw_weight
    omega
  have hv : IsI4PlusIn L (φ w) := (h.data.bdata.type4 w hw_even hw0).mp hw_weight
  let a : G := sec4MPt t φ x * sec4MPt t φ y
  have ha : a = sec4MPt t φ x * sec4MPt t φ y := rfl
  have hsa : s * a * s⁻¹ = sec4MPt t φ (σ x) * sec4MPt t φ (σ y) := by
    rw [ha]
    rw [show s * (sec4MPt t φ x * sec4MPt t φ y) * s⁻¹
        = (s * sec4MPt t φ x * s⁻¹) * (s * sec4MPt t φ y * s⁻¹) by group,
      hσ x, hσ y]
  have hφw_split : φ w =
      φ (sec4MV x + sec4MV y) * φ (sec4MV (σ x) + sec4MV (σ y)) := by
    have hw' : w = (sec4MV x + sec4MV y) + (sec4MV (σ x) + sec4MV (σ y)) := by
      show sec4MV x + sec4MV y + sec4MV (σ x) + sec4MV (σ y)
          = (sec4MV x + sec4MV y) + (sec4MV (σ x) + sec4MV (σ y))
      abel
    rw [hw']
    exact h.data.bdata.perm.1 _ _ (isEvenVec_add (sec4MV_even x) (sec4MV_even y))
      (isEvenVec_add (sec4MV_even (σ x)) (sec4MV_even (σ y)))
  have hφw : φ w = a * (s * a * s⁻¹) := by
    rw [hsa]
    rw [ha, hφw_split, ← sec4MPt_mul h.data x y, ← sec4MPt_mul h.data (σ x) (σ y)]
  have haA : a ∈ A := by
    rw [ha]
    exact A.mul_mem (sec4MPt_mem_A h.data x) (sec4MPt_mem_A h.data y)
  have hbA : s * a * s⁻¹ ∈ A := by
    rw [hsa]
    exact A.mul_mem (sec4MPt_mem_A h.data (σ x)) (sec4MPt_mem_A h.data (σ y))
  have hsb : s * (s * a * s⁻¹) * s⁻¹ = a := by
    have hsinv : s⁻¹ = s := inv_eq_of_mul_eq_one_right hsq
    rw [hsinv]
    calc s * (s * a * s) * s = (s * s) * a * (s * s) := by group
      _ = 1 * a * 1 := by rw [hsq]
      _ = a := by group
  have hconj : s * φ w * s⁻¹ = φ w := by
    rw [hφw]
    calc s * (a * (s * a * s⁻¹)) * s⁻¹
        = (s * a * s⁻¹) * (s * (s * a * s⁻¹) * s⁻¹) := by group
      _ = (s * a * s⁻¹) * a := by rw [hsb]
      _ = a * (s * a * s⁻¹) := (h.A_comm haA hbA).symm
  have hvs : φ w * s = s * φ w := by
    have h1 : s * φ w = φ w * s := by
      calc s * φ w = (s * φ w * s⁻¹) * s := by group
        _ = φ w * s := by rw [hconj]
    exact h1.symm
  have hφws : φ w * s = a * s * a := by
    rw [hφw]
    calc a * (s * a * s⁻¹) * s
        = a * ((s * a * s⁻¹) * s) := by group
      _ = a * (s * a) := by rw [show (s * a * s⁻¹) * s = s * a by group]
      _ = a * s * a := by group
  have hsv_eq : s * φ w = a * s * a := by rw [← hvs, hφws]
  have ha_inv : a⁻¹ = a := inv_eq_of_mul_eq_one_right (h.A_sq haA)
  have hsv : ∃ g : G, s * φ w = g⁻¹ * s * g := by
    refine ⟨a⁻¹, ?_⟩
    rw [hsv_eq, inv_inv, ha_inv]
  have hwz : ∃ k : G, φ w = k⁻¹ * z * k := by
    obtain ⟨l, hl, hlw⟩ := h.inputs.hf43c G L h.omega7 z (φ w) h.ctx.pocket hv
    exact ⟨l⁻¹, by rw [hlw, inv_inv]⟩
  exact sec4_lemmaZ h.inputs.h43 h.ctx h.not_tz ⟨g, hg⟩ hwz
    (Subgroup.mem_centralizer_singleton_iff.mpr hvs)
    (by
      obtain ⟨c, hc⟩ := hsv
      exact ⟨g * c, by rw [hc, hg]; group⟩)

end CFSG.OddStandard.SmallF3.Omega
