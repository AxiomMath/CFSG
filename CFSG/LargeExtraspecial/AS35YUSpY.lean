module

public import CFSG.LargeExtraspecial.AS35YUSpF

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions CFSG.ClassicalGroups.Orthogonal

namespace AS35YR

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] {q : QuadraticForm (ZMod 2) V}

namespace Frame

namespace RadHyp

variable {F : Frame q} {P : Subgroup (V ≃ₗ[ZMod 2] V)} (h : F.RadHyp P)
  {U : Submodule (ZMod 2) V}

include h

theorem mem_of_mem_Y_YU (hPU : ∀ p ∈ P, ∀ u ∈ U, p u ∈ U) (haU : F.a ∈ U) (hbU : F.b ∈ U)
    (hcU : F.c ∈ U) {y : V} (hy : y ∈ F.Y P h.inU) : y ∈ U := by
  obtain ⟨p, hp, rfl, -⟩ := hy
  rw [tau_def, proj_apply]
  exact U.sub_mem (U.sub_mem (hPU p hp _ hcU) hcU)
    (U.add_mem (U.smul_mem _ haU) (U.smul_mem _ hbU))

theorem mem_Xp_of_mem_Y_YU {y : V} (hy : y ∈ F.Y P h.inU) : y ∈ F.Xp := by
  obtain ⟨ha, hb, hc, hc'⟩ := h.polar_of_mem_Y hy
  exact mem_Xp.mpr ⟨ha, hb, hc, hc'⟩

omit h in
theorem mem_Xp_of_perp_YU {r : V} (hrU : ∀ u ∈ U, polar q u r = 0) (haU : F.a ∈ U)
    (hbU : F.b ∈ U) (hcU : F.c ∈ U) (hc'U : F.c' ∈ U) : r ∈ F.Xp := by
  refine mem_Xp.mpr ⟨?_, ?_, ?_, ?_⟩ <;> rw [polar_comm]
  · exact hrU _ haU
  · exact hrU _ hbU
  · exact hrU _ hcU
  · exact hrU _ hc'U

theorem add_mem_Y_YU (hPU : ∀ p ∈ P, ∀ u ∈ U, p u ∈ U) (haU : F.a ∈ U) (hbU : F.b ∈ U)
    (hcU : F.c ∈ U) (hc'U : F.c' ∈ U) {r : V} (hr : q r = 1) (hrU : ∀ u ∈ U, polar q u r = 0)
    (hnorm : ∀ v ∈ U, v ∈ F.Xp → ∀ hv : q v = 1, ∀ p ∈ P,
      (refl1 q v hv * refl1 q r hr) * p * (refl1 q v hv * refl1 q r hr)⁻¹ ∈ P)
    {v : V} (hvU : v ∈ U) (hvX : v ∈ F.Xp) (hv : q v = 1) {y : V} (hy : y ∈ F.Y P h.inU) :
    y + polar q y v • v ∈ F.Y P h.inU := by
  have hrX : r ∈ F.Xp := mem_Xp_of_perp_YU hrU haU hbU hcU hc'U
  obtain ⟨ha, hb, hc, hc'⟩ := refl1_fix hvX hv
  obtain ⟨ha', hb', hc'', hc'''⟩ := refl1_fix hrX hr
  have hg := mul_mem (refl1_mem hv) (refl1_mem hr)
  have hgy := h.apply_mem_Y hg (by rw [LinearEquiv.mul_apply, ha', ha])
    (by rw [LinearEquiv.mul_apply, hb', hb]) (by rw [LinearEquiv.mul_apply, hc'', hc])
    (by rw [LinearEquiv.mul_apply, hc''', hc']) (hnorm v hvU hvX hv) hy
  have hyU := h.mem_of_mem_Y_YU hPU haU hbU hcU hy
  have e : (refl1 q v hv * refl1 q r hr) y = y + polar q y v • v := by
    rw [LinearEquiv.mul_apply, refl1_apply hr, hrU y hyU, zero_smul, add_zero, refl1_apply]
  rwa [e] at hgy

theorem exists_polar_eq_one_YU {y : V} (hy : y ∈ F.Y P h.inU) (hy0 : y ≠ 0) :
    ∃ y' ∈ F.Y P h.inU, polar q y y' = 1 := by
  by_contra hcon
  push Not at hcon
  exact hy0 (h.eq_zero_of_polar_eq_zero hy fun y' hy' =>
    (zmod2_cases_YU _).resolve_right (hcon y' hy'))

theorem q_eq_one_of_mem_Y_YU (hPU : ∀ p ∈ P, ∀ u ∈ U, p u ∈ U) (haU : F.a ∈ U)
    (hbU : F.b ∈ U) (hcU : F.c ∈ U) (hc'U : F.c' ∈ U) {r : V} (hr : q r = 1) (hrU' : r ∈ U)
    (hrU : ∀ u ∈ U, polar q u r = 0)
    (hnorm : ∀ v ∈ U, v ∈ F.Xp → ∀ hv : q v = 1, ∀ p ∈ P,
      (refl1 q v hv * refl1 q r hr) * p * (refl1 q v hv * refl1 q r hr)⁻¹ ∈ P)
    {y : V} (hy : y ∈ F.Y P h.inU) (hy0 : y ≠ 0) : q y = 1 := by
  refine (zmod2_cases_YU (q y)).resolve_left fun h0 => ?_
  have hrX : r ∈ F.Xp := mem_Xp_of_perp_YU hrU haU hbU hcU hc'U
  have hyU := h.mem_of_mem_Y_YU hPU haU hbU hcU hy
  obtain ⟨y', hy', hyy'⟩ := h.exists_polar_eq_one_YU hy hy0
  have hy'U := h.mem_of_mem_Y_YU hPU haU hbU hcU hy'
  have hv : q (y + r) = 1 := by
    rw [QuadraticMap.map_add q, h0, hr, hrU y hyU, zero_add, add_zero]
  have h1 := h.add_mem_Y_YU hPU haU hbU hcU hc'U hr hrU hnorm (U.add_mem hyU hrU')
    (F.Xp.add_mem (h.mem_Xp_of_mem_Y_YU hy) hrX) hv hy'
  have hp : polar q y' (y + r) = 1 := by
    rw [polar_add_right, polar_comm, hyy', hrU y' hy'U, add_zero]
  rw [hp, one_smul] at h1
  have hrY : r ∈ F.Y P h.inU := by
    have h2 := (F.Y P h.inU).sub_mem ((F.Y P h.inU).sub_mem h1 hy') hy
    rwa [show y' + (y + r) - y' - y = r by abel] at h2
  have hr0 : r = 0 := h.eq_zero_of_polar_eq_zero hrY fun y'' hy'' => by
    rw [polar_comm]
    exact hrU y'' (h.mem_of_mem_Y_YU hPU haU hbU hcU hy'')
  rw [hr0, QuadraticMap.map_zero] at hr
  exact zero_ne_one hr

theorem false_of_odd_YU [FiniteDimensional (ZMod 2) V] (hq : q.polarBilin.Nondegenerate)
    [Finite P] (hcard : 2 < Nat.card P) (hPU : ∀ p ∈ P, ∀ u ∈ U, p u ∈ U) (haU : F.a ∈ U)
    (hbU : F.b ∈ U) (hcU : F.c ∈ U) (hc'U : F.c' ∈ U) {r : V} (hr : q r = 1) (hrU' : r ∈ U)
    (hrU : ∀ u ∈ U, polar q u r = 0)
    (hnorm : ∀ v ∈ U, v ∈ F.Xp → ∀ hv : q v = 1, ∀ p ∈ P,
      (refl1 q v hv * refl1 q r hr) * p * (refl1 q v hv * refl1 q r hr)⁻¹ ∈ P)
    (hdim : 9 ≤ finrank (ZMod 2) U) : False := by
  obtain ⟨p, hp, hp1, hpt⟩ := exists_ne_one_ne_t (F := F) hcard
  obtain ⟨y₁, hy₁, hy₁0⟩ := h.exists_ne_zero_mem_Y hp hp1 hpt
  obtain ⟨y₂, hy₂, hy₁₂⟩ := h.exists_polar_eq_one_YU hy₁ hy₁0
  have hq1 : ∀ {y : V}, y ∈ F.Y P h.inU → y ≠ 0 → q y = 1 := fun hy hy0 =>
    h.q_eq_one_of_mem_Y_YU hPU haU hbU hcU hc'U hr hrU' hrU hnorm hy hy0
  set S : Submodule (ZMod 2) V :=
    Submodule.span (ZMod 2) (Set.range ![F.a, F.b, F.c, F.c', y₁, y₂]) with hS_def
  set O := LinearMap.BilinForm.orthogonal q.polarBilin S with hO_def
  have hS : finrank (ZMod 2) S ≤ 6 := by
    have := finrank_range_le_card (R := ZMod 2) ![F.a, F.b, F.c, F.c', y₁, y₂]
    rwa [Fintype.card_fin] at this
  have hO : finrank (ZMod 2) O = finrank (ZMod 2) V - finrank (ZMod 2) S :=
    LinearMap.BilinForm.finrank_orthogonal hq S
  have hUV : finrank (ZMod 2) U ≤ finrank (ZMod 2) V := Submodule.finrank_le U
  have hsup := Submodule.finrank_sup_add_finrank_inf_eq U O
  have hsupV := Submodule.finrank_le (U ⊔ O)
  obtain ⟨w, hwT, hw0, hwq⟩ : ∃ w ∈ U ⊓ O, w ≠ 0 ∧ q w = 0 := by
    by_contra hcon
    push Not at hcon
    have h2 := finrank_le_two_of_anisotropic (U := U ⊓ O) fun u hu hu0 =>
      (zmod2_cases_YU (q u)).resolve_left (hcon u hu hu0)
    omega
  obtain ⟨hwU, hwO⟩ := Submodule.mem_inf.mp hwT
  rw [hO_def, OrthoF2.mem_orthogonal_iff_polar] at hwO
  have hwS : ∀ i, polar q w (![F.a, F.b, F.c, F.c', y₁, y₂] i) = 0 := fun i =>
    hwO _ (Submodule.subset_span ⟨i, rfl⟩)
  have hwa : polar q w F.a = 0 := hwS 0
  have hwb : polar q w F.b = 0 := hwS 1
  have hwc : polar q w F.c = 0 := hwS 2
  have hwc' : polar q w F.c' = 0 := hwS 3
  have hw1 : polar q w y₁ = 0 := hwS 4
  have hw2 : polar q w y₂ = 0 := hwS 5
  have hwX : w ∈ F.Xp := mem_Xp.mpr ⟨hwa, hwb, hwc, hwc'⟩
  have hy₁U := h.mem_of_mem_Y_YU hPU haU hbU hcU hy₁
  have hy₁X := h.mem_Xp_of_mem_Y_YU hy₁
  have hv : q (y₁ + w) = 1 := by
    rw [QuadraticMap.map_add q, hq1 hy₁ hy₁0, hwq, polar_comm, hw1]
    rfl
  have h1 := h.add_mem_Y_YU hPU haU hbU hcU hc'U hr hrU hnorm (U.add_mem hy₁U hwU)
    (F.Xp.add_mem hy₁X hwX) hv hy₂
  have hp' : polar q y₂ (y₁ + w) = 1 := by
    rw [polar_add_right, polar_comm, hy₁₂, polar_comm, hw2]
    rfl
  rw [hp', one_smul] at h1
  have hwY : w ∈ F.Y P h.inU := by
    have h2 := (F.Y P h.inU).sub_mem ((F.Y P h.inU).sub_mem h1 hy₂) hy₁
    rwa [show y₂ + (y₁ + w) - y₂ - y₁ = w by abel] at h2
  have h3 := hq1 hwY hw0
  rw [hwq] at h3
  exact zero_ne_one h3

end RadHyp

end Frame

end AS35YR

end CFSG.LargeExtraspecial
