module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB82A10TCtx
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB82A10E1Out

public section

namespace CFSG.ComponentClassification.GSThmB.A10T

open CFSG Subgroup Equiv Equiv.Perm CFSG.ComponentClassification.UnbalancedLayer
open CFSG.ComponentClassification.GSThmB.Catalog82A10 CFSG.ComponentClassification.GSThmB.P29.A10
open CFSG.ComponentClassification.GSThmB.Eight2 CFSG.ComponentClassification.GSThmB.A10Side

variable {X : Type} [Group X] [Finite X]

private def dU (y : DihedralGroup 4) : Perm (Fin 10) := phiFun ((1, y), parD y)

private abbrev rD : Perm (Fin 10) := dU (DihedralGroup.r 1)

private abbrev sD : Perm (Fin 10) := dU (DihedralGroup.sr 0)

private theorem mem_D0_iff (g : Perm (Fin 10)) : g ∈ D0 ↔ ∃ y, dU y = g := by
  constructor
  · intro hg
    obtain ⟨hgP, hgA⟩ := mem_inf.mp hg
    obtain ⟨w, rfl⟩ := mem_P.mp hgP
    obtain ⟨hA, hS⟩ := mem_altOn.mp hgA
    obtain ⟨h1, h2⟩ := (altOn_iff w).mp ⟨mem_alternatingGroup.mp hA, hS⟩
    refine ⟨w.1.2, ?_⟩
    rw [dU, ← h1, h2]
  · rintro ⟨y, rfl⟩
    obtain ⟨hA, hS⟩ := (altOn_iff ((1, y), parD y)).mpr ⟨rfl, rfl⟩
    exact mem_inf.mpr ⟨mem_P.mpr ⟨_, rfl⟩, mem_altOn.mpr ⟨mem_alternatingGroup.mpr hA, hS⟩⟩

private theorem exists_inner : ∀ y₁ y₂ : DihedralGroup 4, dU y₁ * dU y₁ ≠ 1 →
    dU y₂ * dU y₂ = 1 → ¬ (dU y₂ 8 = 8 ∧ dU y₂ 9 = 9) →
    ∃ y₃, dU y₃ * rD * (dU y₃)⁻¹ = dU y₁ ∧ dU y₃ * sD * (dU y₃)⁻¹ = dU y₂ := by
  decide +kernel

private theorem eq_of_card_le_four {G : Type*} [Group G] [Finite G] {R : Subgroup G}
    (hR : Nat.card R ≤ 4) {p q g : G} (hp : p ∈ R) (hq : q ∈ R) (hg : g ∈ R) (hp1 : p ≠ 1)
    (hq1 : q ≠ 1) (hpq1 : p * q ≠ 1) (hpq : p ≠ q) (hpqp : p * q ≠ p) (hpqq : p * q ≠ q) :
    g = 1 ∨ g = p ∨ g = q ∨ g = p * q := by
  classical
  by_contra hne
  simp only [not_or] at hne
  obtain ⟨h1, h2, h3, h4⟩ := hne
  have hsub : ((({1, p, q, p * q, g} : Finset G)) : Set G) ⊆ (R : Set G) := by
    intro u hu
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl
    exacts [one_mem R, hp, hq, mul_mem hp hq, hg]
  have n1 : (1 : G) ∉ ({p, q, p * q, g} : Finset G) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨hp1.symm, hq1.symm, hpq1.symm, Ne.symm h1⟩
  have n2 : p ∉ ({q, p * q, g} : Finset G) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨hpq, hpqp.symm, Ne.symm h2⟩
  have n3 : q ∉ ({p * q, g} : Finset G) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨hpqq.symm, Ne.symm h3⟩
  have n4 : p * q ∉ ({g} : Finset G) := by
    simp only [Finset.mem_singleton]
    exact Ne.symm h4
  have h5 : ({1, p, q, p * q, g} : Finset G).card = 5 := by
    rw [Finset.card_insert_of_notMem n1, Finset.card_insert_of_notMem n2,
      Finset.card_insert_of_notMem n3, Finset.card_insert_of_notMem n4, Finset.card_singleton]
  have h6 := Nat.card_mono (Set.toFinite (R : Set G)) hsub
  simp only [Finset.coe_sort_coe, Nat.card_eq_finsetCard, h5, SetLike.coe_sort_coe] at h6
  omega

private theorem eq_pow_mul_pow : ∀ y : DihedralGroup 4, ∃ i : Fin 4, ∃ j : Fin 2,
    dU y = rD ^ (i : ℕ) * sD ^ (j : ℕ) := by
  decide +kernel

private theorem sD_eq : sD = swap 4 5 * swap 8 9 := by decide

private theorem rD_mul_self : rD * rD ≠ 1 := by decide

private theorem sD_mul_self : sD * sD = 1 := by decide

namespace Ctx

variable (c : Ctx X)

theorem D_le_secSub : c.s.h.D ≤ c.s.h.secSub c.s.y := c.s.D_le_secSub

theorem map_D : (c.s.h.D.subgroupOf (c.s.h.secSub c.s.y)).map c.φ = D0 := by
  have h : altOn fixTwo ≤ c.ι.range := fun g hg => c.alt_le_range (mem_altOn.mp hg).1
  rw [show c.φ = c.ι.comp (c.s.h.subQ c.s.y) from rfl, ← Subgroup.map_map, c.s.map_D_eq,
    Subgroup.map_inf_eq _ _ _ c.ι_injective, c.map_S, c.map_J, inf_assoc, inf_eq_right.mpr h]
  rfl

theorem φ_comm_sigmaTwo {g : X} (hga : g ∈ centralizer ({c.s.h.a} : Set X))
    (hgH : g ∈ c.s.h.secSub c.s.y) : c.φ ⟨g, hgH⟩ * sigmaTwo = sigmaTwo * c.φ ⟨g, hgH⟩ := by
  rw [← c.φ_a, ← map_mul, ← map_mul]
  exact congrArg c.φ (Subtype.ext (mem_centralizer_singleton_iff.mp hga))

private theorem φ_mul' {u₁ u₂ : X} (h₁ : u₁ ∈ c.s.h.secSub c.s.y)
    (h₂ : u₂ ∈ c.s.h.secSub c.s.y) (h : u₁ * u₂ ∈ c.s.h.secSub c.s.y) :
    c.φ ⟨u₁ * u₂, h⟩ = c.φ ⟨u₁, h₁⟩ * c.φ ⟨u₂, h₂⟩ :=
  map_mul c.φ ⟨u₁, h₁⟩ ⟨u₂, h₂⟩

private theorem φ_inv' {u : X} (h₁ : u ∈ c.s.h.secSub c.s.y) (h : u⁻¹ ∈ c.s.h.secSub c.s.y) :
    c.φ ⟨u⁻¹, h⟩ = (c.φ ⟨u, h₁⟩)⁻¹ :=
  map_inv c.φ ⟨u, h₁⟩

private theorem φ_pow' {u : X} (h₁ : u ∈ c.s.h.secSub c.s.y) (n : ℕ)
    (h : u ^ n ∈ c.s.h.secSub c.s.y) : c.φ ⟨u ^ n, h⟩ = c.φ ⟨u, h₁⟩ ^ n :=
  map_pow c.φ ⟨u, h₁⟩ n

private theorem φ_congr {u v : X} (hu : u ∈ c.s.h.secSub c.s.y) (hv : v ∈ c.s.h.secSub c.s.y)
    (h : u = v) : c.φ ⟨u, hu⟩ = c.φ ⟨v, hv⟩ := by
  subst h
  rfl

private theorem φ_injOn_D {u₁ u₂ : X} (h₁ : u₁ ∈ c.s.h.D) (h₂ : u₂ ∈ c.s.h.D)
    (h : c.φ ⟨u₁, c.D_le_secSub h₁⟩ = c.φ ⟨u₂, c.D_le_secSub h₂⟩) : u₁ = u₂ := by
  have hu : u₁ * u₂⁻¹ ∈ c.s.h.D := mul_mem h₁ (inv_mem h₂)
  obtain ⟨k, hk⟩ := c.s.h.isPGroup_S ⟨_, c.s.h.D_le_S hu⟩
  have hk' : ((⟨u₁ * u₂⁻¹, c.D_le_secSub hu⟩ : ↥(c.s.h.secSub c.s.y)) : X) ^ 2 ^ k = 1 := by
    have := congrArg Subtype.val hk
    simpa using this
  have h1 : c.φ ⟨u₁ * u₂⁻¹, c.D_le_secSub hu⟩ = 1 := by
    rw [c.φ_mul' (c.D_le_secSub h₁) (c.D_le_secSub (inv_mem h₂)),
      c.φ_inv' (c.D_le_secSub h₂), h, mul_inv_cancel]
  have h2 := c.s.D_inf_B0 ▸ mem_inf.mpr ⟨hu, c.mem_B0_of_φ_eq_one hk' h1⟩
  rw [mem_bot, mul_inv_eq_one] at h2
  exact h2

theorem exists_w0 :
    ∃ w₀ ∈ c.s.h.D, ∃ hw : w₀ ∈ c.s.h.secSub c.s.y, c.φ ⟨w₀, hw⟩ = swap 4 5 * swap 8 9 ∧
      c.s.h.x * w₀ * c.s.h.x⁻¹ ∈ c.s.h.D ∧
      ∃ hv : c.s.h.x * w₀ * c.s.h.x⁻¹ ∈ c.s.h.secSub c.s.y,
        c.φ ⟨_, hv⟩ 8 = 8 ∧ c.φ ⟨_, hv⟩ 9 = 9 := by
  have hHD := c.D_le_secSub
  have hφD : ∀ u (hu : u ∈ c.s.h.D), ∃ y, dU y = c.φ ⟨u, hHD hu⟩ := by
    intro u hu
    rw [← mem_D0_iff, ← c.map_D]
    exact mem_map_of_mem _ (mem_subgroupOf.mpr hu)
  have hDφ : ∀ y, ∃ u, ∃ hu : u ∈ c.s.h.D, c.φ ⟨u, hHD hu⟩ = dU y := by
    intro y
    have hy : dU y ∈ D0 := (mem_D0_iff _).mpr ⟨y, rfl⟩
    rw [← c.map_D] at hy
    obtain ⟨⟨u, huH⟩, hu, hφu⟩ := mem_map.mp hy
    exact ⟨u, mem_subgroupOf.mp hu, hφu⟩
  have hxS : c.s.h.x ∈ c.s.h.S := c.s.h.x_mem
  obtain ⟨w₀, hw₀D, hw₀⟩ := hDφ (DihedralGroup.sr 0)
  obtain ⟨r, hrD, hr⟩ := hDφ (DihedralGroup.r 1)
  have hvD : c.s.h.x * w₀ * c.s.h.x⁻¹ ∈ c.s.h.D := c.s.h.sec8_conj_mem_D hxS hw₀D
  refine ⟨w₀, hw₀D, hHD hw₀D, hw₀.trans sD_eq, hvD, hHD hvD, ?_⟩
  by_contra hcon
  have hrxD : c.s.h.x * r * c.s.h.x⁻¹ ∈ c.s.h.D := c.s.h.sec8_conj_mem_D hxS hrD
  obtain ⟨y₂, hy₂⟩ := hφD _ hvD
  obtain ⟨y₁, hy₁⟩ := hφD _ hrxD
  have hw₀2 : w₀ * w₀ = 1 := by
    refine c.φ_injOn_D (mul_mem hw₀D hw₀D) (one_mem _) ?_
    rw [c.φ_mul' (hHD hw₀D) (hHD hw₀D), hw₀, sD_mul_self]
    exact (map_one c.φ).symm
  have hv2 : dU y₂ * dU y₂ = 1 := by
    have h1 : c.s.h.x * w₀ * c.s.h.x⁻¹ * (c.s.h.x * w₀ * c.s.h.x⁻¹) = 1 := by
      rw [show c.s.h.x * w₀ * c.s.h.x⁻¹ * (c.s.h.x * w₀ * c.s.h.x⁻¹) =
        c.s.h.x * (w₀ * w₀) * c.s.h.x⁻¹ by group, hw₀2, mul_one, mul_inv_cancel]
    rw [hy₂, ← c.φ_mul' (hHD hvD) (hHD hvD) (hHD (mul_mem hvD hvD))]
    exact (c.φ_congr _ (one_mem _) h1).trans (map_one c.φ)
  have hr1 : dU y₁ * dU y₁ ≠ 1 := by
    intro h
    have h1 : c.s.h.x * r * c.s.h.x⁻¹ * (c.s.h.x * r * c.s.h.x⁻¹) = 1 := by
      refine c.φ_injOn_D (mul_mem hrxD hrxD) (one_mem _) ?_
      rw [c.φ_mul' (hHD hrxD) (hHD hrxD), ← hy₁, h]
      exact (map_one c.φ).symm
    have h2 : r * r = 1 := by
      rw [show c.s.h.x * r * c.s.h.x⁻¹ * (c.s.h.x * r * c.s.h.x⁻¹) =
        c.s.h.x * (r * r) * c.s.h.x⁻¹ by group, conj_eq_one_iff] at h1
      exact h1
    apply rD_mul_self
    change dU (DihedralGroup.r 1) * dU (DihedralGroup.r 1) = 1
    rw [← hr, ← c.φ_mul' (hHD hrD) (hHD hrD) (hHD (mul_mem hrD hrD))]
    exact (c.φ_congr _ (one_mem _) h2).trans (map_one c.φ)
  obtain ⟨y₃, hc₁, hc₂⟩ := exists_inner y₁ y₂ hr1 hv2 (by rw [hy₂]; exact hcon)
  obtain ⟨d, hdD, hd⟩ := hDφ y₃
  have hdx : ∀ u (hu : u ∈ c.s.h.D),
      c.φ ⟨c.s.h.x * u * c.s.h.x⁻¹, hHD (c.s.h.sec8_conj_mem_D hxS hu)⟩ =
        dU y₃ * c.φ ⟨u, hHD hu⟩ * (dU y₃)⁻¹ → c.s.h.x * u * c.s.h.x⁻¹ = d * u * d⁻¹ := by
    intro u hu h
    have hdu : d * u ∈ c.s.h.D := mul_mem hdD hu
    refine c.φ_injOn_D (c.s.h.sec8_conj_mem_D hxS hu) (mul_mem hdu (inv_mem hdD)) ?_
    rw [h, c.φ_mul' (hHD hdu) (hHD (inv_mem hdD)), c.φ_mul' (hHD hdD) (hHD hu),
      c.φ_inv' (hHD hdD), hd]
  have hxw : c.s.h.x * w₀ * c.s.h.x⁻¹ = d * w₀ * d⁻¹ := hdx w₀ hw₀D (by rw [← hy₂, hw₀, hc₂])
  have hxr : c.s.h.x * r * c.s.h.x⁻¹ = d * r * d⁻¹ := hdx r hrD (by rw [← hy₁, hr, hc₁])
  set κ := d⁻¹ * c.s.h.x with hκ
  have hκw : Commute w₀ κ := by
    change w₀ * (d⁻¹ * c.s.h.x) = d⁻¹ * c.s.h.x * w₀
    calc w₀ * (d⁻¹ * c.s.h.x) = d⁻¹ * (d * w₀ * d⁻¹) * c.s.h.x := by group
      _ = d⁻¹ * (c.s.h.x * w₀ * c.s.h.x⁻¹) * c.s.h.x := by rw [hxw]
      _ = d⁻¹ * c.s.h.x * w₀ := by group
  have hκr : Commute r κ := by
    change r * (d⁻¹ * c.s.h.x) = d⁻¹ * c.s.h.x * r
    calc r * (d⁻¹ * c.s.h.x) = d⁻¹ * (d * r * d⁻¹) * c.s.h.x := by group
      _ = d⁻¹ * (c.s.h.x * r * c.s.h.x⁻¹) * c.s.h.x := by rw [hxr]
      _ = d⁻¹ * c.s.h.x * r := by group
  have hκD : ∀ u ∈ c.s.h.D, u * κ = κ * u := by
    intro u hu
    obtain ⟨y, hy⟩ := hφD u hu
    obtain ⟨i, j, hij⟩ := eq_pow_mul_pow y
    have hu' : u = r ^ (i : ℕ) * w₀ ^ (j : ℕ) := by
      refine c.φ_injOn_D hu (mul_mem (pow_mem hrD _) (pow_mem hw₀D _)) ?_
      rw [← hy, hij, c.φ_mul' (hHD (pow_mem hrD _)) (hHD (pow_mem hw₀D _)),
        c.φ_pow' (hHD hrD), c.φ_pow' (hHD hw₀D), hr, hw₀]
    rw [hu']
    exact (hκr.pow_left _).mul_left (hκw.pow_left _)
  set W := c.s.h.S ⊓ centralizer (c.s.h.D : Set X)
  have hWN : W ≤ normalizer (c.s.h.J : Set X) := fun g hg =>
    A10E1.mem_normalizer_of_mem_S c.s (mem_inf.mp hg).1
  have hR2 : IsPGroup 2 (Seven.rhoImg c.s.h.J W) := by
    have hW2 : IsPGroup 2 W := c.s.h.isPGroup_S.to_le inf_le_left
    exact (hW2.of_equiv (subgroupOfEquivOfLe hWN).symm).map _
  have hRC : Seven.rhoImg c.s.h.J W ≤
      centralizer (innOf (Seven.Dbar c.s.h) : Set (MulAut (Seven.Jbar c.s.h))) := by
    intro σ hσ
    obtain ⟨k, hkW, hkN, rfl⟩ := Seven.exists_of_mem_rhoImg hσ
    rw [mem_centralizer_iff]
    rintro τ ⟨t, ht, rfl⟩
    obtain ⟨u, huD, hu⟩ := A10E1.exists_rhoE_of_mem_Dbar c.s ht
    rw [← hu]
    exact A10E1.rhoE_comm c.s (A10E1.mem_normalizer_of_mem_S c.s (c.s.h.D_le_S huD)) hkN
      (mem_centralizer_iff.mp (mem_inf.mp hkW).2 u huD)
  have hcard := c.Z.hC4 _ hR2 hRC
  obtain ⟨f, hfDt, hfP⟩ := A10E1.exists_mem_Dt_not_mem_P c.s c.hA
  have hzS : c.Z.z ∈ c.s.h.S := c.s.h.D_le_S c.Z.hzD
  have hfS : f ∈ c.s.h.S := c.s.Dt_le_S hfDt
  have hzW : c.Z.z ∈ W :=
    mem_inf.mpr ⟨hzS, mem_centralizer_iff.mpr fun u hu => c.Z.hzS u (c.s.h.D_le_S hu)⟩
  have hfW : f ∈ W :=
    mem_inf.mpr ⟨hfS, mem_centralizer_iff.mpr fun u hu => c.s.D_comm_Dt hu hfDt⟩
  have hdS : d ∈ c.s.h.S := c.s.h.D_le_S hdD
  have hκW : κ ∈ W := mem_inf.mpr ⟨mul_mem (inv_mem hdS) hxS, mem_centralizer_iff.mpr hκD⟩
  have hzH := c.z_mem_secSub
  have hfH : f ∈ c.s.h.secSub c.s.y := c.s.Dt_le_secSub hfDt
  have hzfP : c.Z.z * f ∉ c.s.h.P := by
    intro hP
    have h1 := c.φ_fix_of_mem_P (p := ⟨c.Z.z * f, mul_mem hzH hfH⟩) hP 4 (by decide)
    have hfJ : f ∈ conjugate (c.s.h.secJ0 c.s.y) c.s.t := by
      rw [mem_conjugate_iff] at hfDt ⊢
      exact c.s.D_le_J0 hfDt
    have h2 : c.φ ⟨f, hfH⟩ ∈ altOn fixZ := by
      rw [← c.map_Jstar0]
      exact mem_map_of_mem _ (mem_subgroupOf.mpr hfJ)
    have h3 : c.φ ⟨f, hfH⟩ 4 = 4 := by
      by_contra hne
      exact absurd ((mem_altOn.mp h2).2 (Perm.mem_support.mpr hne)) (by decide)
    rw [c.φ_mul' hzH hfH, Perm.mul_apply, h3, c.φ_z] at h1
    exact absurd h1 (by decide)
  have hNz : c.Z.z ∈ normalizer (c.s.h.J : Set X) := A10E1.mem_normalizer_of_mem_S c.s hzS
  have hNf : f ∈ normalizer (c.s.h.J : Set X) := A10E1.mem_normalizer_of_mem_S c.s hfS
  have hρz : Seven.rhoE c.s.h.J c.Z.z ≠ 1 := fun h =>
    c.Z.hzP (A10E1.mem_P_of_rhoE_eq_one c.s hzS h)
  have hρf : Seven.rhoE c.s.h.J f ≠ 1 := fun h => hfP (A10E1.mem_P_of_rhoE_eq_one c.s hfS h)
  have hρzf : Seven.rhoE c.s.h.J c.Z.z * Seven.rhoE c.s.h.J f ≠ 1 := by
    rw [← Seven.rhoE_mul hNz hNf]
    exact fun h => hzfP (A10E1.mem_P_of_rhoE_eq_one c.s (mul_mem hzS hfS) h)
  have hρzf' : Seven.rhoE c.s.h.J c.Z.z ≠ Seven.rhoE c.s.h.J f := by
    intro h
    apply hρzf
    rw [← h, ← Seven.rhoE_mul hNz hNz, c.Z.hzz, Seven.rhoE_one]
  have hρzfz : Seven.rhoE c.s.h.J c.Z.z * Seven.rhoE c.s.h.J f ≠ Seven.rhoE c.s.h.J c.Z.z :=
    fun h => hρf (mul_eq_left.mp h)
  have hρzff : Seven.rhoE c.s.h.J c.Z.z * Seven.rhoE c.s.h.J f ≠ Seven.rhoE c.s.h.J f :=
    fun h => hρz (mul_eq_right.mp h)
  obtain ⟨k, hkS, hk0, hκk⟩ : ∃ k ∈ c.s.h.S, k ∈ c.s.h.secG0 c.s.y ∧
      Seven.rhoE c.s.h.J κ = Seven.rhoE c.s.h.J k := by
    have hz0 : c.Z.z ∈ c.s.h.secG0 c.s.y := c.s.D_le_G0 c.Z.hzD
    have hf0 : f ∈ c.s.h.secG0 c.s.y := c.s.Dt_le_G0 hfDt
    rcases eq_of_card_le_four hcard (Seven.rhoE_mem_rhoImg hWN hzW)
      (Seven.rhoE_mem_rhoImg hWN hfW) (Seven.rhoE_mem_rhoImg hWN hκW) hρz hρf hρzf hρzf'
      hρzfz hρzff with h | h | h | h
    · exact ⟨1, one_mem _, one_mem _, h.trans (Seven.rhoE_one _).symm⟩
    · exact ⟨c.Z.z, hzS, hz0, h⟩
    · exact ⟨f, hfS, hf0, h⟩
    · exact ⟨c.Z.z * f, mul_mem hzS hfS, mul_mem hz0 hf0,
        h.trans (Seven.rhoE_mul hNz hNf).symm⟩
  obtain ⟨e, he⟩ := c.s.exists_isSymSixType c.hA
  have hdk_a : d * k ∈ centralizer ({c.s.h.a} : Set X) :=
    (mem_inf.mp (c.s.h.S_le (mul_mem hdS hkS))).1
  have hdk0 : d * k ∈ c.s.h.secG0 c.s.y := mul_mem (c.s.D_le_G0 hdD) hk0
  have hxa : c.s.h.x ∈ centralizer ({c.s.h.a} : Set X) := (mem_inf.mp (c.s.h.S_le hxS)).1
  have hNd : d ∈ normalizer (c.s.h.J : Set X) := A10E1.mem_normalizer_of_mem_S c.s hdS
  have hNκ : κ ∈ normalizer (c.s.h.J : Set X) :=
    A10E1.mem_normalizer_of_mem_S c.s (mem_inf.mp hκW).1
  have hNk : k ∈ normalizer (c.s.h.J : Set X) := A10E1.mem_normalizer_of_mem_S c.s hkS
  have hρx : Eight.oddBarAction c.s.h.J ⟨c.s.h.x, c.s.J_normal hxa⟩ =
      Eight.oddBarAction c.s.h.J ⟨d * k, c.s.J_normal hdk_a⟩ := by
    rw [← Seven.rhoE_of_mem, ← Seven.rhoE_of_mem]
    calc Seven.rhoE c.s.h.J c.s.h.x = Seven.rhoE c.s.h.J (d * κ) := by
          rw [hκ, mul_inv_cancel_left]
      _ = Seven.rhoE c.s.h.J d * Seven.rhoE c.s.h.J κ := Seven.rhoE_mul hNd hNκ
      _ = Seven.rhoE c.s.h.J d * Seven.rhoE c.s.h.J k := by rw [hκk]
      _ = Seven.rhoE c.s.h.J (d * k) := (Seven.rhoE_mul hNd hNk).symm
  have hsym := he (d * k) hdk_a hdk0
  rw [← hρx] at hsym
  exact not_isSymSixType_of_unbalancing c.s.unbalTriple e _ (fun j => rfl) hsym

end Ctx

end CFSG.ComponentClassification.GSThmB.A10T
