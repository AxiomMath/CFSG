module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711Main

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinE4Perf

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.TC CFSG.ClassicalInvolution.Q3.TC.Graph
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711

set_option linter.unusedSectionVars false
open scoped commutatorElement

section General

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {K : Subgroup G}
  {π : Set (Subgroup G)} {z g : G}

theorem kernel_le_center_of_cfg (h : Cfg' Ω K π z g) {w : G}
    (hw : IsUniqueInvolution (conjSub g K) w) (hwX : w ∈ piGen π)
    {Q : Type} [Group Q] (F : ↥(piGen π) →* Q) (hker : IsPGroup 2 ↥F.ker)
    (ht : F ⟨w, hwX⟩ ≠ 1) : F.ker ≤ Subgroup.center ↥(piGen π) := by
  have hwe : w = g * z * g⁻¹ := hw.eq h.R_inv
  subst hwe
  let PG : Subgroup G := F.ker.map (piGen π).subtype
  have hPGX : PG ≤ piGen π := Subgroup.map_subtype_le _
  have hPG2 : IsPGroup 2 ↥PG := IsPGroup.map hker (piGen π).subtype
  have hconj : ∀ y ∈ piGen π, ∀ p ∈ PG, y * p * y⁻¹ ∈ PG := by
    rintro y hy _ ⟨p, hp, rfl⟩
    exact ⟨⟨y, hy⟩ * p * ⟨y, hy⟩⁻¹, (MonoidHom.normal_ker F).conj_mem p hp ⟨y, hy⟩, rfl⟩
  have hPGn : ∀ y ∈ piGen π, conjSub y PG = PG := by
    intro y hy
    ext x
    rw [mem_conjSub_iff]
    constructor
    · intro hx
      have := hconj y hy _ hx
      simpa [mul_assoc] using this
    · intro hx
      have := hconj y⁻¹ ((piGen π).inv_mem hy) _ hx
      simpa [mul_assoc] using this
  have hxo := h.xOrbit_eq
  have hcen : ∀ J ∈ π, J ≤ Subgroup.centralizer (PG : Set G) := by
    intro J hJ
    have hJΩ : J ∈ Ω := (adj_of_mem_isMaxOrb h.std.graph h.max hJ).2.1
    obtain ⟨u, hu⟩ := (h.std.hyp.omega1 J hJΩ).1
    have hJX : J ≤ piGen π := le_piGen hJ
    have huPG : u ∉ PG := by
      intro huP
      rw [← hxo] at hJ
      obtain ⟨a, ha, rfl⟩ := hJ
      have hua : u = a * (g * z * g⁻¹) * a⁻¹ := hu.eq (h.R_inv.conj a)
      have htP : g * z * g⁻¹ ∈ PG := by
        have := hconj a⁻¹ ((piGen π).inv_mem ha) _ huP
        rw [hua] at this
        simpa [mul_assoc] using this
      obtain ⟨p, hp, hpe⟩ := htP
      apply ht
      have : p = ⟨g * z * g⁻¹, hwX⟩ := Subtype.ext hpe
      rw [← this]
      exact hp
    have hJP : J ⊓ PG = ⊥ := by
      by_contra hne
      exact huPG (mem_of_inf_ne_bot (h.std.two J hJΩ) hu hne)
    have hc := comm613Gen h.std.hyp (mem_RSet_of_isPGroup hJΩ (h.std.two J hJΩ)) hJX hPGX hPGn hJP
    rw [oddCoreOf_eq_bot_of_isPGroup hPG2, le_bot_iff] at hc
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp hc
  have hXc : piGen π ≤ Subgroup.centralizer (PG : Set G) := piGen_le hcen
  intro p hp
  rw [Subgroup.mem_center_iff]
  intro y
  have := Subgroup.mem_centralizer_iff.mp (hXc y.2) p ⟨p, hp, rfl⟩
  exact Subtype.ext this.symm

end General
