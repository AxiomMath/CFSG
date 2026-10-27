module

public import CFSG.ClassicalInvolution.AschTight.Sec6Gen64N

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.Sec6Gen

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight

local notation "𝕏(" K ", " J ")" =>
  (J ⊓ Subgroup.normalizer (SetLike.coe K)) ⊔ (K ⊓ Subgroup.normalizer (SetLike.coe J))

theorem dihedral_step_t {Q : Type*} [Group Q] {a b : Q} (ha : a * a = 1) (hb : b * b = 1)
    {g : Q} {k : ℤ} (hg : g = (a * b) ^ (3 * k) ∨ g = a * (a * b) ^ (3 * k))
    (hc : a * (g * (a * b)⁻¹ * b * (a * b) * g⁻¹) = g * (a * b)⁻¹ * b * (a * b) * g⁻¹ * a) :
    ∃ l : ℤ, Odd l ∧ (a * b) ^ (6 * l) = 1 := by
  set ρ := a * b with hρ
  have ha' : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
  have key : ∀ i : ℤ, ρ ^ i * a = a * ρ ^ (-i) := dihedral_zpow_mul ha hb
  have hb' : b = a * ρ := by rw [hρ, ← mul_assoc, ha, one_mul]
  have hs1 : ρ⁻¹ * b * ρ = a * ρ ^ (3 : ℤ) := by
    have h1 := key (-1)
    rw [neg_neg, zpow_one, zpow_neg_one] at h1
    rw [hb']
    calc ρ⁻¹ * (a * ρ) * ρ = (ρ⁻¹ * a) * ρ * ρ := by group
      _ = a * ρ * ρ * ρ := by rw [h1]
      _ = a * ρ ^ (3 : ℤ) := by
        rw [show (3 : ℤ) = 1 + 1 + 1 by norm_num, zpow_add, zpow_add, zpow_one]
        simp only [mul_assoc]
  obtain ⟨l, hl, hs⟩ : ∃ l : ℤ, Odd l ∧ g * ρ⁻¹ * b * ρ * g⁻¹ = a * ρ ^ (3 * l) := by
    have e : g * ρ⁻¹ * b * ρ * g⁻¹ = g * (ρ⁻¹ * b * ρ) * g⁻¹ := by group
    rw [e, hs1]
    rcases hg with rfl | rfl
    · refine ⟨1 - 2 * k, ⟨-k, by ring⟩, ?_⟩
      calc ρ ^ (3 * k) * (a * ρ ^ (3 : ℤ)) * (ρ ^ (3 * k))⁻¹ =
            (ρ ^ (3 * k) * a) * ρ ^ (3 : ℤ) * (ρ ^ (3 * k))⁻¹ := by group
        _ = a * ρ ^ (-(3 * k)) * ρ ^ (3 : ℤ) * (ρ ^ (3 * k))⁻¹ := by rw [key]
        _ = a * ρ ^ (3 * (1 - 2 * k)) := by group
    · refine ⟨2 * k - 1, ⟨k - 1, by ring⟩, ?_⟩
      calc a * ρ ^ (3 * k) * (a * ρ ^ (3 : ℤ)) * (a * ρ ^ (3 * k))⁻¹ =
            a * (ρ ^ (3 * k) * a) * ρ ^ (3 : ℤ) * (ρ ^ (3 * k))⁻¹ * a⁻¹ := by group
        _ = a * (a * ρ ^ (-(3 * k))) * ρ ^ (3 : ℤ) * (ρ ^ (3 * k))⁻¹ * a⁻¹ := by rw [key]
        _ = (a * a) * (ρ ^ (3 - 6 * k) * a) := by rw [ha']; group
        _ = a * ρ ^ (-(3 - 6 * k)) := by rw [ha, one_mul, key]
        _ = a * ρ ^ (3 * (2 * k - 1)) := by rw [show -(3 - 6 * k) = 3 * (2 * k - 1) by ring]
  have h2 : ρ ^ (3 * l) = ρ ^ (-(3 * l)) := by
    have hc' : a * (a * ρ ^ (3 * l)) = a * ρ ^ (3 * l) * a := by rw [← hs]; exact hc
    calc ρ ^ (3 * l) = a * (a * ρ ^ (3 * l)) := by rw [← mul_assoc, ha, one_mul]
      _ = a * ρ ^ (3 * l) * a := hc'
      _ = a * (a * ρ ^ (-(3 * l))) := by rw [mul_assoc, key]
      _ = ρ ^ (-(3 * l)) := by rw [← mul_assoc, ha, one_mul]
  refine ⟨l, hl, ?_⟩
  calc ρ ^ (6 * l) = ρ ^ (3 * l) * ρ ^ (3 * l) := by rw [← zpow_add]; ring_nf
    _ = ρ ^ (3 * l) * ρ ^ (-(3 * l)) := congrArg (ρ ^ (3 * l) * ·) h2
    _ = 1 := by rw [← zpow_add, add_neg_cancel, zpow_zero]

theorem le_centralizer_of_isUniqueInvolution {G : Type} [Group G] {M : Subgroup G} {z : G}
    (hM : IsUniqueInvolution M z) : M ≤ Subgroup.centralizer ({z} : Set G) := fun _ hw =>
  Subgroup.mem_centralizer_singleton_iff.mpr (hM.commute_of_mem hw).symm

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {K J R T : Subgroup G}
  {z j u v : G}

namespace Cfg64D

variable {N₀K N₀J : Subgroup G} {r t : G} (d : Cfg64D Ω K J z j u v R T N₀K N₀J r t)
  [((𝕏(K, J)).subgroupOf (pairNormalizers K J z j)).Normal]
include d

omit [((𝕏(K, J)).subgroupOf (pairNormalizers K J z j)).Normal] in
theorem conj_rho_inv_j : (r * t)⁻¹ * j * (r * t)⁻¹⁻¹ = z := by
  rw [← d.c.conj_rho_z d.hr d.hru d.ht d.htv]
  group

omit [((𝕏(K, J)).subgroupOf (pairNormalizers K J z j)).Normal] in
theorem isUniqueInvolution_J' : IsUniqueInvolution (conjSub (r * t)⁻¹ J) z := by
  have := d.c.hj.conj (r * t)⁻¹
  rwa [d.conj_rho_inv_j] at this

omit [((𝕏(K, J)).subgroupOf (pairNormalizers K J z j)).Normal] in
theorem conjSub_T_le_Y : conjSub (r * t)⁻¹ T ≤ pairNormalizers K J z j := by
  intro w hw
  rw [mem_conjSub_iff] at hw
  have hρiY : (r * t)⁻¹ ∈ pairNormalizers K J z j := Subgroup.inv_mem _ d.rho_mem_Y
  have := Subgroup.mul_mem _ (Subgroup.mul_mem _ hρiY (d.c.T_le_Y hw)) (Subgroup.inv_mem _ hρiY)
  have e : (r * t)⁻¹ * ((r * t)⁻¹⁻¹ * w * (r * t)⁻¹) * (r * t)⁻¹⁻¹ = w := by group
  rwa [e] at this

theorem exists_rho_six (hA : ∀ y ∈ pairNormalizers K J z j, conjSub y K ≠ J) :
    ∃ l : ℤ, Odd l ∧ bar 𝕏(K, J) d.rho_mem_Y ^ (6 * l) = 1 := by
  have hΩ := d.c.hΩ
  have hρiY : (r * t)⁻¹ ∈ pairNormalizers K J z j := Subgroup.inv_mem _ d.rho_mem_Y
  set H := pairNormalizers K J z j ⊓ Subgroup.centralizer ({z} : Set G) with hH
  have hRH : R ≤ H :=
    le_inf d.c.R_le_Y (d.c.hR.1.trans (le_centralizer_of_isUniqueInvolution d.c.hz))
  have hR'H : conjSub (r * t)⁻¹ T ≤ H := le_inf d.conjSub_T_le_Y
    ((conjSub_mono d.c.hT.1).trans (le_centralizer_of_isUniqueInvolution d.isUniqueInvolution_J'))
  obtain ⟨P, hP, hRP⟩ := IsSylow2In.exists_ge d.c.hR.2.1 hRH
  obtain ⟨P', hP', hR'P'⟩ := IsSylow2In.exists_ge (isPGroup_conjSub _ d.c.hT.2.1) hR'H
  obtain ⟨g, hgH, hgP⟩ := exists_conjSub_eq_of_isSylow2In hP' hP
  have hgY : g ∈ pairNormalizers K J z j := hgH.1
  have hgz : g * z * g⁻¹ = z := by
    rw [Subgroup.mem_centralizer_singleton_iff.mp hgH.2]
    group
  have hL''Ω : conjSub (g * (r * t)⁻¹) J ∈ Ω := hΩ.conjInvariant _ J d.c.hJ
  have hL''z : IsUniqueInvolution (conjSub (g * (r * t)⁻¹) J) z := by
    have := d.c.hj.conj (g * (r * t)⁻¹)
    have e : g * (r * t)⁻¹ * j * (g * (r * t)⁻¹)⁻¹ = z := by
      calc g * (r * t)⁻¹ * j * (g * (r * t)⁻¹)⁻¹ =
            g * ((r * t)⁻¹ * j * (r * t)⁻¹⁻¹) * g⁻¹ := by group
        _ = z := by rw [d.conj_rho_inv_j, hgz]
    rwa [e] at this
  have hKL : K ≠ conjSub (g * (r * t)⁻¹) J := by
    intro h
    apply hA ((g * (r * t)⁻¹)⁻¹) (Subgroup.inv_mem _ (Subgroup.mul_mem _ hgY hρiY))
    rw [h, conjSub_inv_conjSub]
  have hR''L : conjSub g (conjSub (r * t)⁻¹ T) ≤ conjSub (g * (r * t)⁻¹) J := by
    rw [conjSub_mul]
    exact conjSub_mono (conjSub_mono d.c.hT.1)
  have hR''P : conjSub g (conjSub (r * t)⁻¹ T) ≤ P := hgP ▸ conjSub_mono hR'P'
  have hcomm : Commutes R (conjSub g (conjSub (r * t)⁻¹ T)) :=
    commutes_of_twin_of_isPGroup hΩ d.c.hK hL''Ω hKL d.c.hz hL''z d.c.hR.1 hR''L
      (hP.2.1.to_le (sup_le hRP hR''P))
  have ht'' : g * (r * t)⁻¹ * t * (g * (r * t)⁻¹)⁻¹ ∈ conjSub g (conjSub (r * t)⁻¹ T) := by
    have := conj_mem_conjSub (n := g) (conj_mem_conjSub (n := (r * t)⁻¹) d.ht)
    have e : g * ((r * t)⁻¹ * t * (r * t)⁻¹⁻¹) * g⁻¹ =
        g * (r * t)⁻¹ * t * (g * (r * t)⁻¹)⁻¹ := by group
    rwa [e] at this
  have hrt'' := hcomm r d.hr _ ht''
  have hsY : g * (r * t)⁻¹ * t * (g * (r * t)⁻¹)⁻¹ ∈ pairNormalizers K J z j :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hgY hρiY) d.t_mem_Y)
      (Subgroup.inv_mem _ (Subgroup.mul_mem _ hgY hρiY))
  have h1 := (bar_eq_bar_iff 𝕏(K, J) (Subgroup.mul_mem _ d.r_mem_Y hsY)
    (Subgroup.mul_mem _ hsY d.r_mem_Y)).mpr
      (by rw [hrt'', inv_mul_cancel]; exact Subgroup.one_mem _)
  obtain ⟨k, hk⟩ := d.exists_of_conj_z hgY hgz
  rw [d.bar_rho] at hk ⊢
  refine dihedral_step_t d.bar_r_sq d.bar_t_sq hk ?_
  have e1 : bar 𝕏(K, J) hgY * (bar 𝕏(K, J) d.r_mem_Y * bar 𝕏(K, J) d.t_mem_Y)⁻¹ *
      bar 𝕏(K, J) d.t_mem_Y * (bar 𝕏(K, J) d.r_mem_Y * bar 𝕏(K, J) d.t_mem_Y) *
      (bar 𝕏(K, J) hgY)⁻¹ = bar 𝕏(K, J) hsY := by
    rw [show bar 𝕏(K, J) hsY = bar 𝕏(K, J) hgY *
      (bar 𝕏(K, J) d.r_mem_Y * bar 𝕏(K, J) d.t_mem_Y)⁻¹ * bar 𝕏(K, J) d.t_mem_Y *
      (bar 𝕏(K, J) hgY * (bar 𝕏(K, J) d.r_mem_Y * bar 𝕏(K, J) d.t_mem_Y)⁻¹)⁻¹ from rfl]
    group
  rw [e1]
  exact h1

theorem orderOf_rho_dvd_six (hA : ∀ y ∈ pairNormalizers K J z j, conjSub y K ≠ J) :
    orderOf (bar 𝕏(K, J) d.rho_mem_Y) ∣ 6 := by
  obtain ⟨a, ha⟩ := d.orderOf_rho_eq
  obtain ⟨l, hl, h6⟩ := d.exists_rho_six hA
  have h1 : ((orderOf (bar 𝕏(K, J) d.rho_mem_Y) : ℕ) : ℤ) ∣ 6 * l :=
    orderOf_dvd_iff_zpow_eq_one.mpr h6
  rw [ha] at h1 ⊢
  obtain ⟨c, hc⟩ := h1
  push_cast at hc
  have h2 : 2 * l = 2 ^ a * c := by linarith
  rcases a with _ | _ | a
  · norm_num
  · norm_num
  · exfalso
    have h4 : (2 : ℤ) ^ (a + 2) = 4 * 2 ^ a := by rw [pow_add]; ring
    rw [h4] at h2
    obtain ⟨m, hm⟩ := hl
    have h5 : (2 : ℤ) * (2 * m + 1) = 4 * (2 ^ a * c) := by rw [← hm, h2]; ring
    generalize 2 ^ a * c = x at h5
    omega

end Cfg64D

end CFSG.ClassicalInvolution.Disconnected.AschTight.Sec6Gen
