module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzB0B
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzL35d

public section

namespace CFSG.OddStandard.SmallF3.FritzII

open Subgroup CFSG.OddStandard.SmallF3.HarrisU33
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau : G}

private lemma fzbs_mem_normalizer_of_conj_mem' {H : Subgroup G} {g : G}
    (h : ∀ y ∈ H, g * y * g⁻¹ ∈ H) : g ∈ Subgroup.normalizer (H : Set G) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  refine Subgroup.eq_of_le_of_card_ge ?_ ?_
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
    show g * y * g⁻¹ ∈ H
    exact h y hy
  · exact le_of_eq (Subgroup.card_map_of_injective (f := (MulAut.conj g).toMonoidHom)
      (MulAut.conj g).injective).symm

private lemma fzbs_rho_zpow_fix_eq_one (h : Ctx t L S x₁ x₂ lam rho tau) {i : ℤ} {z : G}
    (hz : z ∈ fourGrp x₁ x₂) (hz1 : z ≠ 1)
    (hfix : rho ^ i * z * (rho ^ i)⁻¹ = z) : rho ^ i = 1 := by
  obtain ⟨-, -, -, hno⟩ := fzl_rho_Z h
  have hmod : rho ^ i = rho ^ (i % 3) := by
    have h1 : rho ^ (i % 3) = rho ^ i := by
      simpa [h.ord_rho] using zpow_mod_orderOf rho i
    exact h1.symm
  rw [hmod] at hfix
  have hcases : i % 3 = 0 ∨ i % 3 = 1 ∨ i % 3 = 2 := by
    have h0 : 0 ≤ i % 3 := Int.emod_nonneg i (by norm_num)
    have h3 : i % 3 < 3 := Int.emod_lt_of_pos i (by norm_num)
    omega
  rcases hcases with hk | hk | hk
  · rw [hmod, hk]; simp
  · rw [hk] at hfix
    exfalso
    exact hno z hz hz1 (by simpa using hfix)
  · rw [hk] at hfix
    exfalso
    have h3n : rho ^ (3 : ℕ) = 1 := by simpa [h.ord_rho] using pow_orderOf_eq_one rho
    have h3z : rho ^ (3 : ℤ) = 1 := by simpa using h3n
    have h2 : rho ^ (2 : ℤ) = rho⁻¹ := by
      have hthis : rho ^ (2 : ℤ) * rho = 1 := by
        calc rho ^ (2 : ℤ) * rho = rho ^ ((2 : ℤ) + 1) := mul_zpow_self rho 2
          _ = rho ^ (3 : ℤ) := by norm_num
          _ = 1 := h3z
      exact eq_inv_of_mul_eq_one_left hthis
    have hfix2 : rho⁻¹ * z * rho = z := by
      rw [h2] at hfix
      simpa using hfix
    have h1 : z * rho = rho * z := by
      calc z * rho = rho * (rho⁻¹ * z * rho) := by group
        _ = rho * z := by rw [hfix2]
    exact hno z hz hz1 (by
      calc rho * z * rho⁻¹ = (z * rho) * rho⁻¹ := by rw [← h1]
        _ = z := by group)

private lemma fzbs_d_fix_eq_one (h : Ctx t L S x₁ x₂ lam rho tau) {d : G}
    (hd : d ∈ closure ({rho, lam} : Set G))
    (hdz : ∀ z ∈ fourGrp x₁ x₂, d * z * d⁻¹ = z) : d = 1 := by
  obtain ⟨-, -, hlam2, hlamx1, -, hlamz3⟩ := fzl_lam_Z h
  obtain ⟨hlamrho, -, hlam1⟩ := fzl_lam_rho h
  have hordlam : orderOf lam = 2 := orderOf_eq_prime hlam2 hlam1
  have hlam_norm : lam ∈ Subgroup.normalizer ((Subgroup.zpowers rho : Subgroup G) : Set G) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq, MonoidHom.map_zpowers]
    change Subgroup.zpowers (lam * rho * lam⁻¹) = Subgroup.zpowers rho
    rw [hlamrho, Subgroup.zpowers_inv]
  have hD : closure ({rho, lam} : Set G) = Subgroup.zpowers rho ⊔ Subgroup.zpowers lam := by
    have hset : ({rho, lam} : Set G) = {rho} ∪ {lam} := by ext x; simp [or_comm]
    rw [hset, Subgroup.closure_union, ← Subgroup.zpowers_eq_closure rho,
      ← Subgroup.zpowers_eq_closure lam]
  rw [hD] at hd
  have hdmem : d ∈ ((Subgroup.zpowers rho : Set G) *
      (Subgroup.zpowers lam : Set G) : Set G) := by
    rw [← Subgroup.coe_mul_of_right_le_normalizer_left (Subgroup.zpowers rho)
      (Subgroup.zpowers lam) (Subgroup.zpowers_le.mpr hlam_norm)]
    exact hd
  obtain ⟨a, ha, b, hb, hab⟩ := hdmem
  obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp ha
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hb
  rw [← hi, ← hj] at hab
  subst d
  have hlam_j : lam ^ (j % 2) = lam ^ j := by
    simpa [hordlam] using zpow_mod_orderOf lam j
  have hx1z : x₁ ^ 2 ∈ fourGrp x₁ x₂ := Subgroup.subset_closure (by simp)
  have hx1nz : x₁ ^ 2 ≠ 1 := (fzl_z1_ne_z2 h).2.1
  have hz3 : (x₁ * x₂) ^ 2 ∈ fourGrp x₁ x₂ := Subgroup.subset_closure (by simp)
  have hz3nz : (x₁ * x₂) ^ 2 ≠ 1 := by
    intro h1
    obtain ⟨hxy, -, -, hprod⟩ := fzl_z1_ne_z2 h
    have hx1sq : x₁ ^ 2 * x₁ ^ 2 = 1 := by
      have h2 : (x₁ ^ 2) ^ 2 = 1 :=
        fzl_Z_sq_eq_one h (z := x₁ ^ 2) (Subgroup.subset_closure (by simp))
      calc x₁ ^ 2 * x₁ ^ 2 = (x₁ ^ 2) ^ 2 := (pow_two (x₁ ^ 2)).symm
        _ = 1 := h2
    have h2 : x₁ ^ 2 * x₂ ^ 2 = 1 := by rw [← hprod]; exact h1
    have heq : x₁ ^ 2 * x₂ ^ 2 = x₁ ^ 2 * x₁ ^ 2 := by rw [h2, hx1sq]
    exact hxy (mul_left_cancel heq).symm
  rcases Int.emod_two_eq_zero_or_one j with hj0 | hj1
  · have hlamj : lam ^ j = 1 := by rw [← hlam_j, hj0]; simp
    have hfix1 : rho ^ i * x₁ ^ 2 * (rho ^ i)⁻¹ = x₁ ^ 2 := by
      have h1 := hdz (x₁ ^ 2) hx1z
      rw [hlamj] at h1
      simpa using h1
    have hri : rho ^ i = 1 := fzbs_rho_zpow_fix_eq_one h hx1z hx1nz hfix1
    simp [hri, hlamj]
  · have hlamj : lam ^ j = lam := by rw [← hlam_j, hj1]; simp
    exfalso
    have hfix3 : rho ^ i * (x₁ * x₂) ^ 2 * (rho ^ i)⁻¹ = (x₁ * x₂) ^ 2 := by
      have h1 := hdz ((x₁ * x₂) ^ 2) hz3
      rw [hlamj] at h1
      rw [show (rho ^ i * lam) * (x₁ * x₂) ^ 2 * (rho ^ i * lam)⁻¹
            = rho ^ i * (lam * (x₁ * x₂) ^ 2 * lam⁻¹) * (rho ^ i)⁻¹ by group,
          hlamz3] at h1
      exact h1
    have hri : rho ^ i = 1 := fzbs_rho_zpow_fix_eq_one h hz3 hz3nz hfix3
    have hcontra : lam * x₁ ^ 2 * lam⁻¹ = x₁ ^ 2 := by
      have h1 := hdz (x₁ ^ 2) hx1z
      rw [hri, hlamj] at h1
      simpa using h1
    exact (fzl_z1_ne_z2 h).1 (hcontra.symm.trans hlamx1)

theorem fzbs_ker_le (h : Ctx t L S x₁ x₂ lam rho tau) {n : G} (hn : n ∈ fzN2 t x₁ x₂)
    (htn : n * t * n⁻¹ = t) (hz : ∀ z ∈ fourGrp x₁ x₂, n * z * n⁻¹ = z) :
    n ∈ ctxW t x₁ x₂ ⊔ zpowers tau := by
  have hnH : n ∈ invCent t := by
    rw [S4A.mem_invCent_iff]
    calc n * t = (n * t * n⁻¹) * n := by group
      _ = t * n := by rw [htn]
  have hAL : baseGrp x₁ x₂ ≤ L := S4A.pt_base_le_L h.toCtx0
  have hWL : ctxW t x₁ x₂ ⊓ L = baseGrp x₁ x₂ := by
    apply le_antisymm
    · intro x hx
      obtain ⟨hxW, hxL⟩ := Subgroup.mem_inf.mp hx
      obtain ⟨p, hp, a, ha, hxpa⟩ :=
        (mem_sup_iff_of_commute (S4A.pt_comm_base h.toCtx0)).mp hxW
      have haL : a ∈ L := hAL ha
      have hpL : p ∈ L := by
        have hp_eq : p = x * a⁻¹ := by rw [hxpa]; group
        rw [hp_eq]
        exact Subgroup.mul_mem L hxL (Subgroup.inv_mem L haL)
      have hpbot : p ∈ twoCore t ⊓ L := ⟨hp, hpL⟩
      rw [h.hyp.twoCore_inf, Subgroup.mem_bot] at hpbot
      rw [hxpa, hpbot, one_mul]
      exact ha
    · exact le_inf le_sup_right hAL
  have hconjL : ∀ x ∈ L, n * x * n⁻¹ ∈ L := by
    intro x hx
    have hxH : x ∈ invCent t := S4A.L_le_invCent h.hyp hx
    have hmem : (⟨n, hnH⟩ : ↥(invCent t)) * (⟨x, hxH⟩ : ↥(invCent t)) *
        (⟨n, hnH⟩ : ↥(invCent t))⁻¹ ∈ L.subgroupOf (invCent t) :=
      h.hyp.normal.conj_mem ⟨x, hxH⟩ (Subgroup.mem_subgroupOf.mpr hx) ⟨n, hnH⟩
    simpa using (Subgroup.mem_subgroupOf.mp hmem)
  have hnNormA : n ∈ Subgroup.normalizer ((baseGrp x₁ x₂ : Subgroup G) : Set G) := by
    refine fzbs_mem_normalizer_of_conj_mem' ?_
    intro a ha
    have h1 : n * a * n⁻¹ ∈ ctxW t x₁ x₂ :=
      (Subgroup.mem_normalizer_iff.mp hn a).mp (Subgroup.mem_sup_right ha)
    have h2 : n * a * n⁻¹ ∈ L := hconjL a (hAL ha)
    rw [← hWL]
    exact Subgroup.mem_inf.mpr ⟨h1, h2⟩
  have hnormA : n ∈ invCent t ⊓
      Subgroup.normalizer ((baseGrp x₁ x₂ : Subgroup G) : Set G) :=
    Subgroup.mem_inf.mpr ⟨hnH, hnNormA⟩
  rw [h.norm_baseGrp] at hnormA
  have hset : ({rho, lam, tau} : Set G) = {tau} ∪ ({rho, lam} : Set G) := by
    ext x; simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_union]; tauto
  rw [hset, Subgroup.closure_union, ← Subgroup.zpowers_eq_closure tau, ← sup_assoc] at hnormA
  have hrho_tau : rho * tau * rho⁻¹ = tau := by
    calc rho * tau * rho⁻¹ = (tau * rho) * rho⁻¹ := by rw [← h.tau_rho]
      _ = tau := by group
  have hlam_tau : lam * tau * lam⁻¹ = tau := by
    calc lam * tau * lam⁻¹ = (tau * lam) * lam⁻¹ := by rw [← h.tau_lam]
      _ = tau := by group
  have hDnorm : closure ({rho, lam} : Set G) ≤
      Subgroup.normalizer (((ctxW t x₁ x₂ ⊔ zpowers tau : Subgroup G) : Set G)) := by
    refine (Subgroup.closure_le (K := Subgroup.normalizer
      (((ctxW t x₁ x₂ ⊔ zpowers tau : Subgroup G) : Set G)))).mpr ?_
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with hg | hg
    · rw [hg]
      refine (Subgroup.mem_normalizer_iff_map_conj_eq
        (H := (ctxW t x₁ x₂ ⊔ zpowers tau : Subgroup G))).mpr ?_
      rw [Subgroup.map_sup, (Subgroup.mem_normalizer_iff_map_conj_eq.mp (fzl_rho_Z h).1),
        MonoidHom.map_zpowers]
      change ctxW t x₁ x₂ ⊔ Subgroup.zpowers (rho * tau * rho⁻¹)
        = ctxW t x₁ x₂ ⊔ Subgroup.zpowers tau
      rw [hrho_tau]
    · rw [hg]
      refine (Subgroup.mem_normalizer_iff_map_conj_eq
        (H := (ctxW t x₁ x₂ ⊔ zpowers tau : Subgroup G))).mpr ?_
      rw [Subgroup.map_sup, (Subgroup.mem_normalizer_iff_map_conj_eq.mp (fzl_lam_Z h).1),
        MonoidHom.map_zpowers]
      change ctxW t x₁ x₂ ⊔ Subgroup.zpowers (lam * tau * lam⁻¹)
        = ctxW t x₁ x₂ ⊔ Subgroup.zpowers tau
      rw [hlam_tau]
  have hnormA2 : n ∈ ((ctxW t x₁ x₂ ⊔ zpowers tau : Subgroup G) : Set G) *
      (closure ({rho, lam} : Set G) : Set G) := by
    rw [← Subgroup.coe_mul_of_right_le_normalizer_left (ctxW t x₁ x₂ ⊔ zpowers tau)
      (closure ({rho, lam} : Set G)) hDnorm]
    exact hnormA
  obtain ⟨m, hm, d, hd, hmd⟩ := hnormA2
  have hmZ : ∀ z ∈ fourGrp x₁ x₂, m * z * m⁻¹ = z := (fzbs_Wtau_act h hm).2.2.1
  have hfixd : ∀ z ∈ fourGrp x₁ x₂, d * z * d⁻¹ = z := by
    intro z hzZ
    have hd_eq : d = m⁻¹ * n := by rw [← hmd]; group
    rw [hd_eq]
    calc (m⁻¹ * n) * z * (m⁻¹ * n)⁻¹ = m⁻¹ * (n * z * n⁻¹) * m := by group
      _ = m⁻¹ * z * m := by rw [hz z hzZ]
      _ = z := by
        have h1 : m * z = z * m := by
          calc m * z = (m * z * m⁻¹) * m := by group
            _ = z * m := by rw [hmZ z hzZ]
        calc m⁻¹ * z * m = m⁻¹ * (z * m) := by group
          _ = m⁻¹ * (m * z) := by rw [← h1]
          _ = z := by group
  have hd1 : d = 1 := fzbs_d_fix_eq_one h hd hfixd
  rw [← hmd, hd1]
  simpa using hm

end CFSG.OddStandard.SmallF3.FritzII
