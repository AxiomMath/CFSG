module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf3HexC
public import CFSG.ClassicalInvolution.Q3.Q3T6DHexD

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf

open CFSG.ClassicalInvolution.Q3.PhilipHall.InductionBridge (FrameSimple)

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Asc77.T3CII CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight CFSG.ClassicalInvolution.Q3.Q3T6D
open scoped commutatorElement


open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Asc77.T3CII CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight
open scoped commutatorElement

section Std

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K K' J : Subgroup G} {S : Sylow 2 G} {R R' W V : Subgroup G} {z t : G}

namespace HexDataF

variable {d : Std20Frame K K' J S R R' W V z t} {u r v t₀ : G} {T : Subgroup G}
  (hh : HexDataF d u r v t₀ T)
include hh

theorem hrz' : r⁻¹ * z * r = z := by
  have h2 : r * z = z * r := by
    calc r * z = (r * z * r⁻¹) * r := by group
      _ = z * r := by rw [hh.hrz]
  calc r⁻¹ * z * r = r⁻¹ * (z * r) := by group
    _ = r⁻¹ * (r * z) := by rw [h2]
    _ = z := by group

theorem hrt' : r⁻¹ * t * r = t * z := by
  have h1 : r⁻¹ * (t * z) * r = t := by rw [← hh.hrt]; group
  have h2 : r⁻¹ * (t * z) * r = (r⁻¹ * t * r) * (r⁻¹ * z * r) := by group
  rw [h2, hh.hrz'] at h1
  calc r⁻¹ * t * r = ((r⁻¹ * t * r) * z) * z := by
        rw [mul_assoc (r⁻¹ * t * r) z z, d.viol.hzK.sq, mul_one]
    _ = t * z := by rw [h1]

theorem hw_t : (r * t₀ * r⁻¹) * t * (r * t₀ * r⁻¹)⁻¹ = z := by
  calc (r * t₀ * r⁻¹) * t * (r * t₀ * r⁻¹)⁻¹ = r * t₀ * (r⁻¹ * t * r) * t₀⁻¹ * r⁻¹ := by group
    _ = r * t₀ * (t * z) * t₀⁻¹ * r⁻¹ := by rw [hh.hrt']
    _ = r * ((t₀ * t * t₀⁻¹) * (t₀ * z * t₀⁻¹)) * r⁻¹ := by group
    _ = r * (t * (z * t)) * r⁻¹ := by rw [hh.ht₀t, hh.htz]
    _ = r * z * r⁻¹ := by rw [d.late_zt_comm, ← mul_assoc t t z, d.viol.hzJ.sq, one_mul]
    _ = z := hh.hrz

theorem hw_z : (r * t₀ * r⁻¹) * z * (r * t₀ * r⁻¹)⁻¹ = t := by
  calc (r * t₀ * r⁻¹) * z * (r * t₀ * r⁻¹)⁻¹ = r * t₀ * (r⁻¹ * z * r) * t₀⁻¹ * r⁻¹ := by group
    _ = r * (t₀ * z * t₀⁻¹) * r⁻¹ := by rw [hh.hrz']; group
    _ = r * (z * t) * r⁻¹ := by rw [hh.htz]
    _ = (r * z * r⁻¹) * (r * t * r⁻¹) := by group
    _ = z * (t * z) := by rw [hh.hrz, hh.hrt]
    _ = t := by rw [← d.late_zt_comm, ← mul_assoc, d.viol.hzK.sq, one_mul]

end HexDataF

theorem Std20Frame.late_a_mem_Z (d : Std20Frame K K' J S R R' W V z t) {u r v t₀ : G}
    {T : Subgroup G} (hh : HexDataF d u r v t₀ T) {L₁ T₁ : Subgroup G} {a w₁ s₁ : G}
    (hL₁ : L₁ ∈ CoreAssembly.conjClass K) (ha : IsUniqueInvolution L₁ a) (haW : a ∈ W)
    (hd₁ : Sec71.DData (CoreAssembly.conjClass K) W T₁ L₁ w₁ s₁ a) :
    a = z ∨ a = t ∨ a = z * t := by
  by_contra hcon
  push Not at hcon
  obtain ⟨haz, hat, hazt⟩ := hcon
  have hΩ := d.late_hΩ
  have hWc := d.late_hWc
  have hzW := d.late_z_mem_W
  have htW := d.late_t_mem_W
  have hKL : K ≠ L₁ := by
    intro h
    exact haz (d.viol.hzK.eq (h ▸ ha)).symm
  have hnot : L₁ ∉ omegaNbr (CoreAssembly.conjClass K) K := by
    intro h
    obtain ⟨-, z', hz', hz'L⟩ := d.late_nbr L₁ h
    exact haz ((ha.eq hz'L).trans (d.viol.hzK.eq hz').symm)
  obtain ⟨i₁, k₁, hio, hko, hi, hk, hra, hsz⟩ := late_pairGen hΩ d.late_cls hWc hh.hd hd₁ hKL
    (Ne.symm haz) hnot
  have hza : z * a = a * z := hWc z hzW a haW
  have hta : t * a = a * t := hWc t htW a haW
  obtain ⟨k₂, hk₂⟩ := hd₁.exists_rel hh.hd'.u_memW (hd₁.le_normalizer hh.hd'.u_memW)
  have hst := conj_z_eqGen hΩ hh.hd' hd₁ hWc hk₂
  have hLsyl : IsSylow2In T₁ L₁ := hd₁.sylow
  have hT₁s : s₁ ∈ T₁ := hd₁.r_mem
  have hΩg := d.late_hΩ
  rcases Int.even_or_odd k₂ with hke | hko₂
  ·
    rw [Sec71.zpow_eq_one_of_even ha.sq hke, mul_one] at hst
    have hTt : T₁ ≤ Subgroup.centralizer ({t} : Set G) := hd₁.le_centralizer hWc htW hst
    set w : G := r * t₀ * r⁻¹ with hwdef
    have hwz : w * z * w⁻¹ = t := hh.hw_z
    have hwt : w * t * w⁻¹ = z := hh.hw_t
    have h1 : IsUniqueInvolution (conjSub w K) t := hwz ▸ d.viol.hzK.conj w
    have h2 : IsUniqueInvolution (conjSub w K') t := hwz ▸ d.late_hzK'.conj w
    have hzM : z ∈ conjSub w K ⊔ conjSub w K' := by
      rw [← late_conjSub_sup, mem_conjSub_iff]
      have : w⁻¹ * z * w = t := by
        calc w⁻¹ * z * w = w⁻¹ * (w * t * w⁻¹) * w := by rw [hwt]
          _ = t := by group
      rw [this]
      exact d.htKK
    exact late_keyGen hΩ (d.hyp.conjInvariant w K d.late_mem_K)
      (d.hyp.conjInvariant w K' d.late_mem_K') (fun h => d.ne (conjSub_injective w h).symm) h1 h2
      hL₁ ha (Ne.symm hat) hLsyl hTt hzM hT₁s hsz hza
  ·
    rw [Sec71.zpow_eq_self_of_odd ha.sq hko₂] at hst
    have hszt : s₁ * (z * t) * s₁⁻¹ = z * t := by
      calc s₁ * (z * t) * s₁⁻¹ = (s₁ * z * s₁⁻¹) * (s₁ * t * s₁⁻¹) := by group
        _ = (z * a) * (t * a) := by rw [hsz, hst]
        _ = z * (a * t) * a := by group
        _ = z * (t * a) * a := by rw [hta]
        _ = z * t := by rw [mul_assoc, mul_assoc, ha.sq, mul_one]
    have hTzt : T₁ ≤ Subgroup.centralizer ({z * t} : Set G) :=
      hd₁.le_centralizer hWc (W.mul_mem hzW htW) hszt
    have hwz : t₀ * (z * t) * t₀⁻¹ = z := by
      calc t₀ * (z * t) * t₀⁻¹ = (t₀ * z * t₀⁻¹) * (t₀ * t * t₀⁻¹) := by group
        _ = (z * t) * t := by rw [hh.htz, hh.ht₀t]
        _ = z := by rw [mul_assoc, d.viol.hzJ.sq, mul_one]
    have h1 : IsUniqueInvolution (conjSub t₀ K) (z * t) := hh.htz ▸ d.viol.hzK.conj t₀
    have h2 : IsUniqueInvolution (conjSub t₀ K') (z * t) := hh.htz ▸ d.late_hzK'.conj t₀
    have hzM : z ∈ conjSub t₀ K ⊔ conjSub t₀ K' := by
      rw [← late_conjSub_sup, mem_conjSub_iff]
      have : t₀⁻¹ * z * t₀ = z * t := by
        calc t₀⁻¹ * z * t₀ = t₀⁻¹ * (t₀ * (z * t) * t₀⁻¹) * t₀ := by rw [hwz]
          _ = z * t := by group
      rw [this]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left d.viol.hzK.mem) d.htKK
    exact late_keyGen hΩ (d.hyp.conjInvariant t₀ K d.late_mem_K)
      (d.hyp.conjInvariant t₀ K' d.late_mem_K') (fun h => d.ne (conjSub_injective t₀ h).symm)
      h1 h2 hL₁ ha (Ne.symm hazt) hLsyl hTzt hzM hT₁s hsz hza

end Std


end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf
