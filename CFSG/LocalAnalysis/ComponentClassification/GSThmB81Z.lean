module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB81U2

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr

structure In81 : Prop where
  rk : CFL2Rank
  sy : CFL2Sylow
  c : CFL2C
  j : CFL2J
  b1 : ConjFixStatement
  b6 : SylowKernelStatement
  cf23 : CFProp23Fusion
  cf24 : CFProp24c
  cfc : CFProp23Center
  cf1 : CFSec8Simple
  cf2 : CFSec8InnerCentralizer

namespace Hyp59

variable {H : Type} [Group H] [Finite H] {h : Hyp59 H}

abbrev ZF32 (h : Hyp59 H) : Subgroup H := h.F32 ⊓ centralizer (h.F32 : Set H)

theorem conj_mem_ZF32 {n u : H} (hn : n ∈ normalizer (h.F32 : Set H)) (hu : u ∈ h.ZF32) :
    n⁻¹ * u * n ∈ h.ZF32 := by
  obtain ⟨huF, huC⟩ := mem_inf.mp hu
  refine mem_inf.mpr ⟨?_, mem_centralizer_iff.mpr fun f hf => ?_⟩
  · have := (mem_normalizer_iff.mp (inv_mem hn) u).mp huF
    rwa [inv_inv] at this
  · have hf' : n * f * n⁻¹ ∈ h.F32 := (mem_normalizer_iff.mp hn f).mp hf
    have h1 := mem_centralizer_iff.mp huC _ hf'
    calc f * (n⁻¹ * u * n) = n⁻¹ * ((n * f * n⁻¹) * u) * n := by group
      _ = n⁻¹ * (u * (n * f * n⁻¹)) * n := by rw [h1]
      _ = n⁻¹ * u * n * f := by group

namespace L81Hyp

variable {H₁ : h.L81Hyp}

namespace Data

variable {d : Data H₁}

theorem comm_b_of_mem_M3 {k : H} (hk : k ∈ h.M3) : k * d.b = d.b * k :=
  comm_of_mem_normalizer_zpowers d.b_ord (d.B_eq ▸ h.toHyp52.M3_le_normalizer hk)

theorem comm_z_of_mem_S {s : H} (hs : s ∈ h.S) : s * d.z = d.z * s :=
  mem_centralizer_iff.mp d.z_S s hs

theorem x_inv_b_x : h.x⁻¹ * d.b * h.x = h.a * d.b := by
  calc h.x⁻¹ * d.b * h.x = h.x⁻¹ * (h.a * (h.a * d.b)) * h.x := by
        rw [show h.a * (h.a * d.b) = d.b by rw [← mul_assoc, Six.a_mul_a_self h.toHyp52, one_mul]]
    _ = h.x⁻¹ * (h.a * (h.x * d.b * h.x⁻¹)) * h.x := by rw [d.x_b_x_inv]
    _ = (h.x⁻¹ * h.a * h.x) * d.b := by group
    _ = h.a * d.b := by rw [x_conj_a]

theorem x_inv_z_x : h.x⁻¹ * d.z * h.x = d.z := by
  rw [mul_assoc, ← d.comm_z_of_mem_S h.x_mem, inv_mul_cancel_left]

theorem g_inv_b_g : d.g⁻¹ * d.b * d.g = d.b := by
  rw [mul_assoc, ← d.comm_b_of_mem_M3 d.g_M, inv_mul_cancel_left]

theorem conj_b : (h.x * d.g)⁻¹ * d.b * (h.x * d.g) = h.a * d.sigma := by
  rw [show (h.x * d.g)⁻¹ * d.b * (h.x * d.g) = d.g⁻¹ * (h.x⁻¹ * d.b * h.x) * d.g by group,
    x_inv_b_x, show d.g⁻¹ * (h.a * d.b) * d.g = (d.g⁻¹ * h.a * d.g) * (d.g⁻¹ * d.b * d.g) by
      group, d.a_g, g_inv_b_g, sigma, mul_assoc]

theorem k_sigma {k : H} (hk : k ∈ h.M3) (hkz : k⁻¹ * d.z * k = d.tau) :
    k * d.sigma * k⁻¹ = d.b * d.z := by
  have h1 : k * d.tau * k⁻¹ = d.z := by rw [← hkz]; group
  have h2 : k * d.b * k⁻¹ = d.b := by rw [d.comm_b_of_mem_M3 hk, mul_inv_cancel_right]
  rw [sigma, show k * (d.tau * d.b) * k⁻¹ = (k * d.tau * k⁻¹) * (k * d.b * k⁻¹) by group, h1, h2,
    ← d.comm_z_of_mem_S d.b_mem_S]

theorem exists_conj_sigma (F : d.Facts) :
    ∃ c : H, c⁻¹ * d.sigma * c = h.a * d.z * d.sigma := by
  obtain ⟨k, hk, hkz⟩ := F.z_tau
  have hzb := d.comm_z_of_mem_S d.b_mem_S
  have hzt := d.comm_z_of_mem_S d.tau_mem_S
  refine ⟨k⁻¹ * h.x * d.g, ?_⟩
  calc (k⁻¹ * h.x * d.g)⁻¹ * d.sigma * (k⁻¹ * h.x * d.g)
      = d.g⁻¹ * (h.x⁻¹ * (k * d.sigma * k⁻¹) * h.x) * d.g := by group
    _ = d.g⁻¹ * (h.x⁻¹ * (d.b * d.z) * h.x) * d.g := by rw [d.k_sigma hk hkz]
    _ = d.g⁻¹ * ((h.x⁻¹ * d.b * h.x) * (h.x⁻¹ * d.z * h.x)) * d.g := by group
    _ = d.g⁻¹ * (h.a * d.b * d.z) * d.g := by rw [x_inv_b_x, x_inv_z_x]
    _ = (d.g⁻¹ * h.a * d.g) * (d.g⁻¹ * d.b * d.g) * (d.g⁻¹ * d.z * d.g) := by group
    _ = h.a * d.tau * d.b * d.z := by rw [d.a_g, g_inv_b_g, F.z_g]
    _ = h.a * d.tau * (d.b * d.z) := by group
    _ = h.a * d.tau * (d.z * d.b) := by rw [hzb]
    _ = h.a * (d.tau * d.z) * d.b := by group
    _ = h.a * (d.z * d.tau) * d.b := by rw [hzt]
    _ = h.a * d.z * d.sigma := by
        show h.a * (d.z * d.tau) * d.b = h.a * d.z * (d.tau * d.b)
        group

theorem sigma_not_mem_DP (hCF1 : CFSec8Simple) (hCF2 : CFSec8InnerCentralizer) (F : d.Facts) :
    d.sigma ∉ h.D ⊔ h.P := by
  intro hσ
  apply d.tau_not_mem_DP hCF1 hCF2 F
  have : d.tau = d.sigma * d.b := by
    show d.tau = d.tau * d.b * d.b
    rw [mul_assoc, d.b_mul_self, mul_one]
  rw [this]
  exact mul_mem hσ (mem_sup_right d.b_mem_P)

section ZF

variable (I : In81) (F : d.Facts)
include I F

theorem a_mem_F : h.a ∈ h.F32 :=
  d.sigma_sup_T_le_F I.sy I.cf1 I.cf2 F (mem_sup_right (d.T_eq ▸ mem_sup_left (mem_zpowers _)))

theorem sigma_mem_F : d.sigma ∈ h.F32 :=
  d.sigma_sup_T_le_F I.sy I.cf1 I.cf2 F (mem_sup_left (mem_zpowers _))

theorem z_mem_ZF : d.z ∈ h.ZF32 :=
  mem_inf.mpr ⟨d.D_le_F I.sy I.cf1 I.cf2 F d.z_D, mem_centralizer_iff.mpr fun _ hu =>
    d.comm_z_of_mem_S (h.F32_le_S hu)⟩

theorem a_mem_ZF : h.a ∈ h.ZF32 :=
  mem_inf.mpr ⟨a_mem_F I F, mem_centralizer_iff.mpr fun _ hu => h.toHyp52.comm_a (h.F32_le_S hu)⟩

theorem sigma_mem_ZF : d.sigma ∈ h.ZF32 :=
  mem_inf.mpr ⟨sigma_mem_F I F, mem_centralizer_iff.mpr fun _ hu =>
    mem_centralizer_singleton_iff.mp (d.F32_le_centralizer_sigma I.rk I.j I.c I.b1 I.b6 I.cf23
      I.cf24 I.cfc I.cf1 I.cf2 F hu)⟩

theorem ZF_eq : h.ZF32 = zpowers d.z ⊔ zpowers h.a ⊔ zpowers d.sigma := by
  refine le_antisymm (fun w hw => d.center_F_le I.rk I.j I.c I.sy I.b1 I.b6 I.cf23 I.cf24 I.cfc
    I.cf1 I.cf2 F (mem_inf.mp hw).1 fun u hu => ?_) ?_
  · exact (mem_centralizer_iff.mp (mem_inf.mp hw).2 u hu).symm
  · exact sup_le (sup_le (zpowers_le.mpr (z_mem_ZF I F)) (zpowers_le.mpr (a_mem_ZF I F)))
      (zpowers_le.mpr (sigma_mem_ZF I F))

end ZF

theorem mem_ZF_cases {u : H} (hu : u ∈ zpowers d.z ⊔ zpowers h.a ⊔ zpowers d.sigma) :
    ∃ e₀ ∈ ({1, d.z} : Set H), ∃ e₁ ∈ ({1, h.a} : Set H), ∃ e₂ ∈ ({1, d.sigma} : Set H),
      u = e₀ * e₁ * e₂ := by
  have hza : ∀ x ∈ zpowers d.z, ∀ y ∈ zpowers h.a, x * y = y * x := by
    intro x hx y hy
    rcases eq_one_or_of_mem_zpowers_of_mul_self d.z_mul_self hx with rfl | rfl
    · rw [one_mul, mul_one]
    · rcases eq_one_or_of_mem_zpowers_of_mul_self (Six.a_mul_a_self h.toHyp52) hy with rfl | rfl
      · rw [one_mul, mul_one]
      · exact d.z_comm_a
  have hσS : d.sigma ∈ h.S := d.sigma_mem_S
  have hs : ∀ x ∈ zpowers d.z ⊔ zpowers h.a, ∀ y ∈ zpowers d.sigma, x * y = y * x := by
    intro x hx y hy
    rcases eq_one_or_of_mem_zpowers_of_mul_self d.sigma_mul_self hy with rfl | rfl
    · rw [one_mul, mul_one]
    · obtain ⟨x₀, hx₀, x₁, hx₁, rfl⟩ := Eight.exists_mul_of_mem_sup₂ hza hx
      rcases eq_one_or_of_mem_zpowers_of_mul_self d.z_mul_self hx₀ with rfl | rfl <;>
      rcases eq_one_or_of_mem_zpowers_of_mul_self (Six.a_mul_a_self h.toHyp52) hx₁ with
        rfl | rfl
      · simp
      · rw [one_mul, h.toHyp52.comm_a hσS]
      · rw [mul_one, d.comm_z_of_mem_S hσS]
      · rw [mul_assoc, ← h.toHyp52.comm_a hσS, ← mul_assoc, ← d.comm_z_of_mem_S hσS, mul_assoc]
  obtain ⟨w, hw, e₂, he₂, rfl⟩ := Eight.exists_mul_of_mem_sup₂ hs hu
  obtain ⟨e₀, he₀, e₁, he₁, rfl⟩ := Eight.exists_mul_of_mem_sup₂ hza hw
  exact ⟨e₀, eq_one_or_of_mem_zpowers_of_mul_self d.z_mul_self he₀, e₁,
    eq_one_or_of_mem_zpowers_of_mul_self (Six.a_mul_a_self h.toHyp52) he₁, e₂,
    eq_one_or_of_mem_zpowers_of_mul_self d.sigma_mul_self he₂, rfl⟩

section Fusion

variable {v : H} (hv : d.IsV v) (I : In81) (F : d.Facts)
include hv I F

omit F in
theorem weaklyClosed_F (g : H) (hg : conjugate h.F32 g ≤ h.U81 v) :
    conjugate h.F32 g = h.F32 := by
  rw [← JeN_U_eq hv I.rk] at hg ⊢
  exact Eight.conjugate_JeN_eq hg

theorem exists_normalizer_conj {w c : H} (hw : w ∈ h.ZF32) (hwc : c⁻¹ * w * c ∈ h.ZF32) :
    ∃ n ∈ normalizer (h.F32 : Set H), n⁻¹ * w * n = c⁻¹ * w * c :=
  Seven.exists_normalizer_conj_of_weaklyClosed
    (isSylow_U hv I.rk I.sy I.b1 I.b6 I.cf23 I.cf24 I.cfc I.cf1 I.cf2 I.c F)
    (h.F32_le_S.trans le_sup_left) (weaklyClosed_F hv I)
    (fun _ hu => mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp (mem_inf.mp hw).2 _ hu))
    (fun _ hu => mem_centralizer_singleton_iff.mpr
      (mem_centralizer_iff.mp (mem_inf.mp hwc).2 _ hu))

theorem conj_z_cases {n : H} (hn : n ∈ normalizer (h.F32 : Set H)) :
    n⁻¹ * d.z * n = h.a ∨ n⁻¹ * d.z * n = d.z := by
  have hvn : v * n ∈ normalizer (h.F32 : Set H) :=
    mul_mem (h.normalizer_S_le_normalizer_F32 hv.mem_N) hn
  have := conj_a_cases I.sy I.b1 I.b6 I.cf23 I.cf24 I.cfc I.cf1 I.cf2 I.c F hvn
  rwa [show (v * n)⁻¹ * h.a * (v * n) = n⁻¹ * (v⁻¹ * h.a * v) * n by group, hv.conj_a] at this

theorem conj_az {n : H} (hn : n ∈ normalizer (h.F32 : Set H)) :
    n⁻¹ * (h.a * d.z) * n = h.a * d.z := by
  have h1 := conj_a_cases I.sy I.b1 I.b6 I.cf23 I.cf24 I.cfc I.cf1 I.cf2 I.c F hn
  have h2 := conj_z_cases hv I F hn
  have hne : n⁻¹ * h.a * n ≠ n⁻¹ * d.z * n := fun he => d.z_ne_a (by
    calc d.z = n * (n⁻¹ * d.z * n) * n⁻¹ := by group
      _ = n * (n⁻¹ * h.a * n) * n⁻¹ := by rw [he]
      _ = h.a := by group)
  rw [show n⁻¹ * (h.a * d.z) * n = (n⁻¹ * h.a * n) * (n⁻¹ * d.z * n) by group]
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
  · exact absurd (h1.trans h2.symm) hne
  · rw [h1, h2]
  · rw [h1, h2]; exact d.z_comm_a
  · exact absurd (h1.trans h2.symm) hne

theorem conj_a_of_mem_ZF {c : H} (hc : c⁻¹ * h.a * c ∈ h.ZF32) :
    c⁻¹ * h.a * c = h.a ∨ c⁻¹ * h.a * c = d.z := by
  obtain ⟨n, hn, hnc⟩ := exists_normalizer_conj hv I F (a_mem_ZF I F) hc
  rw [← hnc]
  exact conj_a_cases I.sy I.b1 I.b6 I.cf23 I.cf24 I.cfc I.cf1 I.cf2 I.c F hn

theorem conj_az_of_mem_ZF {c : H} (hc : c⁻¹ * (h.a * d.z) * c ∈ h.ZF32) :
    c⁻¹ * (h.a * d.z) * c = h.a * d.z := by
  obtain ⟨n, hn, hnc⟩ :=
    exists_normalizer_conj hv I F (mul_mem (a_mem_ZF I F) (z_mem_ZF I F)) hc
  rw [← hnc]
  exact conj_az hv I F hn

end Fusion

end Data

end L81Hyp

end Hyp59

end CFSG.ComponentClassification.GSThmB
