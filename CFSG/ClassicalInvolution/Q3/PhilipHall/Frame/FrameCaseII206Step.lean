module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameCaseII206Dec
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf8Alpha

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf

open CFSG.ClassicalInvolution.Q3.PhilipHall.InductionBridge (FrameCore)

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Asc77.T3CII CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight CFSG.ClassicalInvolution.Q3.Q3T6D
  CFSG.ClassicalInvolution.Balance.Bootstrap
open Out
open scoped commutatorElement


variable {G : Type} [Group G] [Finite G] [FrameCore G]
  {K K' J : Subgroup G} {S : Sylow 2 G} {R R' W V : Subgroup G} {z t : G}

theorem mem_closure_pair_iff_inZ {y : G} (hz2 : z * z = 1) (ht2 : t * t = 1)
    (hzt : z * t = t * z) : y ∈ Subgroup.closure ({t, z} : Set G) ↔ InZ z t y := by
  constructor
  · intro hy
    rcases mem_closure_pair_cases ht2 hz2 hzt.symm hy with h | h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inr (h.trans hzt.symm)))
  · rintro (rfl | rfl | rfl | rfl)
    · exact Subgroup.one_mem _
    · exact Subgroup.subset_closure (by simp)
    · exact Subgroup.subset_closure (by simp)
    · exact Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
        (Subgroup.subset_closure (by simp))

section Step

variable (d : Std20Frame K K' J S R R' W V z t)
include d

theorem Std20Frame.exists_hex_rho : ∃ ρ : G, ρ * z * ρ⁻¹ = z * t ∧ ρ * t * ρ⁻¹ = z := by
  obtain ⟨u, r, v, t₀, T, hh⟩ := d.late_exists_hex
  refine ⟨t₀ * r, ?_, ?_⟩
  · calc (t₀ * r) * z * (t₀ * r)⁻¹ = t₀ * (r * z * r⁻¹) * t₀⁻¹ := by group
      _ = t₀ * z * t₀⁻¹ := by rw [hh.hrz]
      _ = z * t := hh.htz
  · calc (t₀ * r) * t * (t₀ * r)⁻¹ = t₀ * (r * t * r⁻¹) * t₀⁻¹ := by group
      _ = t₀ * (t * z) * t₀⁻¹ := by rw [hh.hrt]
      _ = (t₀ * t * t₀⁻¹) * (t₀ * z * t₀⁻¹) := by group
      _ = t * (z * t) := by rw [hh.ht₀t, hh.htz]
      _ = z := by rw [d.late_zt_comm, ← mul_assoc, d.viol.hzJ.sq, one_mul]

theorem Std20Frame.mem_S_of_inZ {y : G} (hy : InZ z t y) : y ∈ (S : Subgroup G) := by
  rcases hy with rfl | rfl | rfl | rfl
  · exact Subgroup.one_mem _
  · exact d.z_mem_S
  · exact d.t_mem_S
  · exact Subgroup.mul_mem _ d.z_mem_S d.t_mem_S

theorem Std20Frame.exists_mul_oddCore_of_mem_M {c : G}
    (hc : c ∈ oddCoreOf (sec20X (CoreAssembly.conjClass K) z K K') ⊔ (K ⊔ K')) :
    ∃ r ∈ R ⊔ R', ∃ o ∈ oddCoreOf (sec20X (CoreAssembly.conjClass K) z K K'), c = r * o := by
  set X := sec20X (CoreAssembly.conjClass K) z K K' with hX
  have hXN := sec20X_le_normalizers_frame d
  have hXO : ∀ y ∈ X, ∀ o ∈ oddCoreOf X, y * o * y⁻¹ ∈ oddCoreOf X := fun y hy o ho =>
    mem_normalizer_oddCoreOf_of_mem_normalizer (Subgroup.le_normalizer hy) ho
  have hKX : K ≤ X := le_sec20X_left
  have hK'X : K' ≤ X := le_sec20X_right
  have hOK : oddCoreOf K ≤ oddCoreOf X :=
    le_oddCoreOf_of_normalizes ((oddCoreOf_le_self K).trans hKX)
      (fun y hy => mem_normalizer_oddCore_of_mem_normalizer (hXN hy).1) (oddCoreOf_odd_natCard K)
  have hOK' : oddCoreOf K' ≤ oddCoreOf X :=
    le_oddCoreOf_of_normalizes ((oddCoreOf_le_self K').trans hK'X)
      (fun y hy => mem_normalizer_oddCore_of_mem_normalizer (hXN hy).2) (oddCoreOf_odd_natCard K')
  have hKKN : K ⊔ K' ≤ Subgroup.normalizer ((oddCoreOf X : Subgroup G) : Set G) := fun y hy =>
    mem_normalizer_oddCore_of_mem_normalizer (Subgroup.le_normalizer ((sup_le hKX hK'X) hy))
  have hc' : c ∈ ((oddCoreOf X ⊔ (K ⊔ K') : Subgroup G) : Set G) := hc
  rw [Subgroup.coe_mul_of_right_le_normalizer_left _ _ hKKN] at hc'
  obtain ⟨o, ho, k, hk, rfl⟩ := hc'
  have hk' : k ∈ ((K ⊔ K' : Subgroup G) : Set G) := hk
  rw [Subgroup.coe_mul_of_left_le_normalizer_right K K' d.late_K_le] at hk'
  obtain ⟨k₁, hk₁, k₂, hk₂, rfl⟩ := hk'
  obtain ⟨e'⟩ := d.kbar_equiv_q8'
  obtain ⟨r₁, hr₁, o₁, ho₁, rfl⟩ := TwinExact.mem_mul_oddCore_of_sylow d.twoGroup d.hR k₁ hk₁
  obtain ⟨r₂, hr₂, o₂, ho₂, rfl⟩ :=
    TwinExact.mem_mul_oddCore_of_sylow (isPGroup_kbar_of_equiv e') d.hR' k₂ hk₂
  have hr₁X : r₁ ∈ X := hKX (d.hR.1 hr₁)
  have hr₂X : r₂ ∈ X := hK'X (d.hR'.1 hr₂)
  refine ⟨r₁ * r₂, Subgroup.mul_mem _ (Subgroup.mem_sup_left hr₁) (Subgroup.mem_sup_right hr₂),
    (r₁ * r₂)⁻¹ * o * (r₁ * r₂) * (r₂⁻¹ * o₁ * r₂ * o₂), ?_, by group⟩
  refine (oddCoreOf X).mul_mem ?_ ((oddCoreOf X).mul_mem ?_ (hOK' ho₂))
  · have := hXO _ (X.inv_mem (X.mul_mem hr₁X hr₂X)) o ho
    rwa [inv_inv] at this
  · have := hXO _ (X.inv_mem hr₂X) o₁ (hOK ho₁)
    rwa [inv_inv] at this

theorem Std20Frame.comm_t_of_not_mem_M (c8 : Concl20_8 S K' R) (c3 : Concl20_3 K K' V z)
    {s g : G} (hsS : s ∈ (S : Subgroup G)) (hs2 : s * s = 1) (hg : g * z * g⁻¹ = s)
    (hsM : s ∉ oddCoreOf (sec20X (CoreAssembly.conjClass K) z K K') ⊔ (K ⊔ K')) :
    s * t = t * s := by
  have hsX := d.P1 c8 hsS hg
  obtain ⟨hout, hout'⟩ := d.not_innerOn_of_not_mem c3 hsX hsM
  have hsN := (sec20X_le_normalizers_frame d) hsX
  obtain ⟨e⟩ := kbar_equiv_q8 d
  obtain ⟨e'⟩ := d.kbar_equiv_q8'
  obtain ⟨x, hx, x', hx', hx2, hx'2, hxx'⟩ := d.exists_four_gens_eq_t
  have hz := not_mem_oddCoreOf_of_invol (L := K) d.viol.hzK.ne_one d.viol.hzK.sq
  have hz' := not_mem_oddCoreOf_of_invol (L := K') d.viol.hzK.ne_one d.viol.hzK.sq
  have hsW : s ∈ Subgroup.normalizer (W : Set G) := d.hWN hsS
  have hSN : s ∈ Subgroup.normalizer (((S : Subgroup G) : Subgroup G) : Set G) :=
    Subgroup.le_normalizer hsS
  have hsR : s ∈ Subgroup.normalizer (R : Set G) := by
    rw [d.late_R_eq]
    exact Subgroup.inf_normalizer_le_normalizer_inf ⟨hsN.1, hSN⟩
  have hsR' : s ∈ Subgroup.normalizer (R' : Set G) := by
    rw [d.late_R'_eq]
    exact Subgroup.inf_normalizer_le_normalizer_inf ⟨hsN.2, hSN⟩
  have hxR : x ∈ R := by
    rw [d.late_R_eq]
    exact ⟨hx.1, d.hWS hx.2⟩
  have hx'R' : x' ∈ R' := by
    rw [d.late_R'_eq]
    exact ⟨hx'.1, d.hWS hx'.2⟩
  have h1 := conj_eq_inv_of_not_innerOn e d.hR.2.1 d.hR.1 d.late_hWc hsN.1 hsR hsW hs2 hxR hx.2
    (by rw [hx2]; exact hz) hout
  have h2 := conj_eq_inv_of_not_innerOn e' d.hR'.2.1 d.hR'.1 d.late_hWc hsN.2 hsR' hsW hs2 hx'R'
    hx'.2 (by rw [hx'2]; exact hz') hout'
  have hcomm : x' * x = x * x' := d.late_hWc x' hx'.2 x hx.2
  have h3 : s * t * s⁻¹ = t := by
    rw [← hxx']
    calc s * (x * x') * s⁻¹ = (s * x * s⁻¹) * (s * x' * s⁻¹) := by group
      _ = (x * x')⁻¹ := by rw [h1, h2, ← mul_inv_rev, hcomm]
      _ = x * x' := by rw [hxx']; exact inv_eq_of_mul_eq_one_right d.viol.hzJ.sq
  calc s * t = (s * t * s⁻¹) * s := by group
    _ = t * s := by rw [h3]

theorem Std20Frame.mem_normalizer_conj (c8 : Concl20_8 S K' R) {h u g : G}
    (hg : g * z * g⁻¹ = u) (hsu : (h⁻¹ * z * h) * u = u * (h⁻¹ * z * h)) :
    u ∈ Subgroup.normalizer ((conjSub h⁻¹ K : Subgroup G) : Set G) := by
  have hC : h * u * h⁻¹ ∈ Subgroup.centralizer ({z} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc h * u * h⁻¹ * z = h * (u * (h⁻¹ * z * h)) * h⁻¹ := by group
      _ = h * ((h⁻¹ * z * h) * u) * h⁻¹ := by rw [hsu]
      _ = z * (h * u * h⁻¹) := by group
  have hX := d.mem_X_of_conj c8 hC (g := h * g) (by rw [← hg]; group)
  have hN : h * u * h⁻¹ ∈ Subgroup.normalizer (K : Set G) := ((sec20X_le_normalizers_frame d) hX).1
  rw [mem_normalizer_iff_conjSub_eq] at hN ⊢
  rw [← conjSub_mul, show u * h⁻¹ = h⁻¹ * (h * u * h⁻¹) by group, conjSub_mul, hN]

theorem Std20Frame.not_innerOn_conj (c8 : Concl20_8 S K' R) (c3 : Concl20_3 K K' V z)
    {h g : G} (hsZ : ¬ InZ z t (h⁻¹ * z * h))
    (hcomm : ∀ y, InZ z t y → (h⁻¹ * z * h) * y = y * (h⁻¹ * z * h))
    (hu : InZ z t (g * z * g⁻¹))
    (hM : g⁻¹ * (h⁻¹ * z * h) * g ∉
      oddCoreOf (sec20X (CoreAssembly.conjClass K) z K K') ⊔ (K ⊔ K')) :
    ¬ InnerOn (conjSub h⁻¹ K) (g * z * g⁻¹) := by
  have hsu := hcomm _ hu
  have hC : g⁻¹ * (h⁻¹ * z * h) * g ∈ Subgroup.centralizer ({z} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc g⁻¹ * (h⁻¹ * z * h) * g * z = g⁻¹ * ((h⁻¹ * z * h) * (g * z * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * z * g⁻¹) * (h⁻¹ * z * h)) * g := by rw [hsu]
      _ = z * (g⁻¹ * (h⁻¹ * z * h) * g) := by group
  have hX := d.mem_X_of_conj c8 hC (g := g⁻¹ * h⁻¹) (by group)
  have hout := (d.not_innerOn_of_not_mem c3 hX hM).1
  have hsA : ¬ InnerOn (conjSub g K) (h⁻¹ * z * h) := fun h' => hout (innerOn_swap' h')
  obtain ⟨e⟩ := kbar_equiv_q8 d
  obtain ⟨eA⟩ := nonempty_kbar_conj_equiv g e
  obtain ⟨eB⟩ := nonempty_kbar_conj_equiv h⁻¹ e
  have hsB : IsUniqueInvolution (conjSub h⁻¹ K) (h⁻¹ * z * h) := by
    have := d.viol.hzK.conj h⁻¹
    rwa [inv_inv] at this
  have hus : g * z * g⁻¹ ≠ h⁻¹ * z * h := fun h' => hsZ (h' ▸ hu)
  exact not_innerOn_of_not_innerOn d.late_hΩ d.card_RSet
    (d.hyp.conjInvariant g K d.late_mem_K) (d.hyp.conjInvariant h⁻¹ K d.late_mem_K)
    (d.viol.hzK.conj g) hsB hus hsu.symm hsA (d.mem_normalizer_conj c8 rfl hsu) eA eB

end Step

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf
