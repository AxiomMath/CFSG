module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.RouteP.Ext.T0
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.RouteP.F10.Mog22

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP

open CFSG.Monster.Code CFSG.Quasithin.H.Mathieu CFSG.Quasithin.H.Coc
open CFSG.Quasithin (pairVec)

universe u

theorem kappa_pairVec_zero_one : cocodeCoords.κ (pairVec 0 1) = toW 11 95 := by
  rw [kappa11_pairVec_mask 0 1 (by decide)]
  exact congrArg (toW 11) (by decide)

theorem kappa_pairVec_ne_one {i j : Fin 24} (hij : i ≠ j) : cocodeCoords.κ (pairVec i j) ≠ 1 := by
  have hall : ∀ i j : Fin 24, i ≠ j → pairImg11 i j ≠ 0 := by decide +kernel
  have h0 : toW 11 (pairImg11 i j) ≠ toW 11 0 := fun h =>
    hall i j hij (toW_inj (actM_lt ccECols_lt _) (by norm_num) h)
  rw [toW_zero] at h0
  rwa [kappa11_pairVec_mask i j hij]

theorem fixed_mog22 {w : W11}
    (hw : ∀ g : ↥mog22, rho11 mog22 mog22_le_autPerm g w = w) :
    w = 1 ∨ w = cocodeCoords.κ (pairVec 0 1) := by
  obtain ⟨m, hm, rfl⟩ := toW_surj 11 w
  have hA : actM mog22ColsA m = m := by
    have h1 : mog22RhoA (toW 11 m) = toW 11 m :=
      hw ⟨CFSG.Monster.B.TwoA.mogA, CFSG.Quasithin.H.Code22.mogA_mem22⟩
    have h2 : mog22RhoA (toW 11 m) = toW 11 (actM mog22ColsA m) := actsBy_mog22RhoA m
    rw [h2] at h1
    exact toW_inj (actM_lt (fun c hc => mog22Cols_lt c (List.mem_append_left _ hc)) m) hm h1
  have hB : actM mog22ColsB m = m := by
    have h1 : mog22RhoB (toW 11 m) = toW 11 m :=
      hw ⟨CFSG.Monster.B.TwoA.mogB, CFSG.Quasithin.H.Code22.mogB_mem22⟩
    have h2 : mog22RhoB (toW 11 m) = toW 11 (actM mog22ColsB m) := actsBy_mog22RhoB m
    rw [h2] at h1
    exact toW_inj (actM_lt (fun c hc => mog22Cols_lt c (List.mem_append_right _ hc)) m) hm h1
  have hfix : ∀ u ∈ mog22EndG, wAct [mog22ColsA, mog22ColsB] u m = m := by
    intro u hu
    simp only [mog22EndG, List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl
    · change actM mog22ColsA m = m
      exact hA
    · change actM mog22ColsB m = m
      exact hB
  rcases mog22EndG_fixed m hm hfix with hm0 | hm95
  · left
    rw [hm0, toW_zero]
  · right
    rw [hm95, kappa_pairVec_zero_one]

namespace CocodeExtension

variable {N : Type u} [Group N] {E : Subgroup N} {e : ↥E ≃* W11} (h : CocodeExtension N E e)

theorem eq_of_mem_centralizer_Bduad
    {i j : Fin 24} (hij : i ≠ j) {x : ↥E}
    (hx : ∀ b ∈ h.Bduad i j, b * (x : N) = (x : N) * b) :
    e x = 1 ∨ e x = cocodeCoords.κ (pairVec i j) := by
  let w : W11 := e x
  have hfix : ∀ σ : ↥AutPerm,
      ((σ : Equiv.Perm (Fin 24)) i = i) → ((σ : Equiv.Perm (Fin 24)) j = j) →
      rho11 AutPerm le_rfl σ w = w := by
    intro σ hi hj
    obtain ⟨b, hb⟩ := h.π_surjective σ
    have hbB : b ∈ h.Bduad i j := by
      rw [h.mem_Bduad_iff, hb]
      exact ⟨hi, hj⟩
    have hcomm : b * (x : N) = (x : N) * b := hx b hbB
    have hconj : h.conjE b x = x := by
      apply Subtype.ext
      rw [h.coe_conjE, hcomm]
      group
    have h1 := h.π_apply_e b x
    rw [hb] at h1
    change rho11 AutPerm le_rfl σ (e x) = e x
    rw [h1, hconj]
  obtain ⟨τ, hτ, hτ0, hτ1⟩ := CFSG.Monster.B.TwoA.autPerm_maps_two i j hij
  let t : ↥AutPerm := ⟨τ, hτ⟩
  let w' : W11 := rho11 AutPerm le_rfl t⁻¹ w
  have ht : rho11 AutPerm le_rfl t w' = w := by
    change rho11 AutPerm le_rfl t (rho11 AutPerm le_rfl t⁻¹ w) = w
    rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one, MulAut.one_apply]
  have hw' : ∀ g : ↥mog22, rho11 mog22 mog22_le_autPerm g w' = w' := by
    intro g
    let k : ↥K22 := eK22.symm g
    have hkg : eK22 k = g := by simp [k]
    let σ : ↥AutPerm := t * (k : ↥AutPerm) * t⁻¹
    have hσeq : σ = t * (k : ↥AutPerm) * t⁻¹ := rfl
    have hσfix : ((σ : Equiv.Perm (Fin 24)) i = i) ∧
        ((σ : Equiv.Perm (Fin 24)) j = j) := by
      have hσmem : t⁻¹ * σ * t ∈ K22 := by
        have hσeq' : t⁻¹ * σ * t = (k : ↥AutPerm) := by
          rw [hσeq]
          group
        rw [hσeq']
        exact k.2
      exact (conj_mem_K22_iff (τ := t) hτ0 hτ1 σ).1 hσmem
    have hfixσ : rho11 AutPerm le_rfl σ w = w := hfix σ hσfix.1 hσfix.2
    have hkfix : rho11 AutPerm le_rfl (k : ↥AutPerm) w' = w' := by
      have h := hfixσ
      rw [← ht] at h
      rw [hσeq, map_mul, map_mul, MulAut.mul_apply, MulAut.mul_apply] at h
      have htinv : rho11 AutPerm le_rfl t⁻¹ (rho11 AutPerm le_rfl t w') = w' := by
        rw [← MulAut.mul_apply, ← map_mul, inv_mul_cancel, map_one, MulAut.one_apply]
      rw [htinv] at h
      exact (rho11 AutPerm le_rfl t).injective h
    have hk' : rho11 mog22 mog22_le_autPerm g w' = w' := by
      rw [← hkg, ← rho11_comp_K22 k]
      exact hkfix
    exact hk'
  rcases fixed_mog22 hw' with hw1 | hwk
  · left
    change w = 1
    rw [← ht, hw1, map_one]
  · right
    change w = cocodeCoords.κ (pairVec i j)
    rw [← ht, hwk, rho11_kappa_pairVec, hτ0, hτ1]

end CocodeExtension

end CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP
