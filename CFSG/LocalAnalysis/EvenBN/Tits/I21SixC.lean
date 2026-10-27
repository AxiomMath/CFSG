module

public import CFSG.LocalAnalysis.EvenBN.Tits.I21SixB

public section

namespace CFSG.LocalAnalysis.EvenBN.Tits

open Subgroup CFSG.Open CFSG.LocalAnalysis.EvenBN.Tits.SecTwoHyp

variable {G : Type} [Group G] [Finite G] {t u : G} {P V : Subgroup G} {v u₀ y₀ : G}

namespace GoodCore

variable {C : SixAY t u P V v u₀ y₀} {x : G} {n : ℕ} (hG : GoodCore C x n)

include hG

theorem refl_of_tConj {s : G} (hs : TConj t s) (hsQ : s ∈ closure ({t, x} : Set G)) :
    ∃ k : ℤ, s = t * x ^ k := by
  have h := C.secTwo
  have hs2 : s ^ 2 = 1 := by
    obtain ⟨g, rfl⟩ := hs
    rw [conj_pow, h.t_sq]; group
  rcases hG.dih.mem_closure_iff.mp hsQ with ⟨k, hk⟩ | ⟨k, hk⟩
  · exfalso
    have h2 : (x ^ k) ^ 2 = 1 := by rw [← hk]; exact hs2
    rcases I21.eq_one_or_eq_z_of_sq_eq_one hG.ord (by have := hG.three_le; omega) k h2 with
      h1 | h1
    · apply h.t_ne_one
      obtain ⟨g, hg⟩ := hs
      have h3 : g * t * g⁻¹ = 1 := by rw [hg, hk, h1]
      calc t = g⁻¹ * (g * t * g⁻¹) * g := by group
        _ = 1 := by rw [h3]; group
    · obtain ⟨g, hg⟩ := hs
      exact C.z_not_tConj ⟨g, by rw [hg, hk, h1, hG.zx_eq]⟩
  · exact ⟨k, hk⟩

theorem eq_one_or_z_of_central {g : G} (hg : g ∈ closure ({t, x} : Set G))
    (hc : ∀ q ∈ closure ({t, x} : Set G), g * q = q * g) : g = 1 ∨ g = u ^ 2 := by
  have htQ : t ∈ closure ({t, x} : Set G) := subset_closure (by simp)
  have hxQ : x ∈ closure ({t, x} : Set G) := subset_closure (by simp)
  have hn3 : 4 ≤ 2 ^ (n - 1) := by
    have := hG.three_le
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (n - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  rcases hG.dih.mem_closure_iff.mp hg with ⟨j, rfl⟩ | ⟨j, rfl⟩
  · have hcomm : t * x ^ j = x ^ j * t := (hc t htQ).symm
    have h2 := (hG.dih.commute_zpow_iff j).mp hcomm
    rcases I21.eq_one_or_eq_z_of_sq_eq_one hG.ord (by have := hG.three_le; omega) j h2 with
      h1 | h1
    · exact Or.inl h1
    · exact Or.inr (by rw [h1, hG.zx_eq])
  · exfalso
    have hcx : (t * x ^ j) * x = x * (t * x ^ j) := hc x hxQ
    have h1 : x ^ (j + 1) = x ^ (j - 1) := by
      have e1 : (t * x ^ j) * x = t * x ^ (j + 1) := by rw [mul_assoc, ← zpow_add_one]
      have e2 : x * (t * x ^ j) = t * x ^ (-1 + j) := by
        rw [← mul_assoc]
        have := hG.dih.zpow_mul_t 1
        rw [zpow_one] at this
        rw [this, mul_assoc, ← zpow_add]
      rw [e1, e2] at hcx
      have := mul_left_cancel hcx
      rw [this]; ring_nf
    have h2 : x ^ 2 = 1 := by
      have : x ^ (j + 1) * (x ^ (j - 1))⁻¹ = 1 := by rw [h1, mul_inv_cancel]
      rw [← zpow_neg, ← zpow_add] at this
      have h3 : (j + 1 + -(j - 1)) = 2 := by ring
      rw [h3] at this
      simpa using this
    have := orderOf_dvd_of_pow_eq_one h2
    rw [hG.ord] at this
    have := Nat.le_of_dvd (by norm_num) this
    omega

theorem exists_mul_of_conj_parity {p p' : G} (hp : p ∈ P) (hp' : p' ∈ P) {k k' : ℤ}
    (hk : p * t * p⁻¹ = t * x ^ k) (hk' : p' * t * p'⁻¹ = t * x ^ k') (hpar : Even (k - k')) :
    ∃ (j : ℤ) (r : G), r ∈ secTwoR t u ∧ p' = x ^ j * p * r := by
  have h := C.secTwo
  obtain ⟨j, hj⟩ := hpar
  refine ⟨j, (x ^ j * p)⁻¹ * p', ?_, by group⟩
  have hxP : x ^ j ∈ P := zpow_mem hG.x_mem j
  have hqpt : (x ^ j * p) * t * (x ^ j * p)⁻¹ = t * x ^ k' := by
    calc (x ^ j * p) * t * (x ^ j * p)⁻¹ = x ^ j * (p * t * p⁻¹) * (x ^ j)⁻¹ := by group
      _ = x ^ j * (t * x ^ k) * (x ^ j)⁻¹ := by rw [hk]
      _ = (x ^ j * t * (x ^ j)⁻¹) * x ^ k := by group
      _ = t * x ^ (-(2 * j)) * x ^ k := by rw [hG.dih.conj_t_x_zpow j]
      _ = t * x ^ k' := by
        rw [mul_assoc, ← zpow_add]
        congr 2
        omega
  have e : p' * t * p'⁻¹ = (x ^ j * p) * t * (x ^ j * p)⁻¹ := by rw [hk', hqpt]
  have hrP : (x ^ j * p)⁻¹ * p' ∈ P := mul_mem (inv_mem (mul_mem hxP hp)) hp'
  have hr : ((x ^ j * p)⁻¹ * p') * t = t * ((x ^ j * p)⁻¹ * p') := by
    calc (x ^ j * p)⁻¹ * p' * t = (x ^ j * p)⁻¹ * (p' * t * p'⁻¹) * p' := by group
      _ = (x ^ j * p)⁻¹ * ((x ^ j * p) * t * (x ^ j * p)⁻¹) * p' := by rw [e]
      _ = t * ((x ^ j * p)⁻¹ * p') := by group
  exact h.mem_R_of_commute C.pgroup C.R_le hrP hr

end GoodCore

namespace Good

variable {C : SixAY t u P V v u₀ y₀} {x : G} {n : ℕ} (hG : Good C x n)

include hG

theorem relIndex_T (hQ : ∀ m ∈ P, m ∈ normalizer (closure ({t, x} : Set G) : Set G))
    (hcl : ∀ s : G, s ∈ P → TConj t s → s ∈ closure ({t, x} : Set G)) :
    (closure ({t, x, u₀} : Set G)).relIndex P ∣ 2 := by
  have h := C.secTwo
  set T : Subgroup G := closure ({t, x, u₀} : Set G) with hT
  have htT : t ∈ T := subset_closure (by simp)
  have hxT : x ∈ T := subset_closure (by simp)
  have hu₀T : u₀ ∈ T := subset_closure (by simp)
  have hRT : secTwoR t u ≤ T := by
    rw [secTwoR, closure_le]
    intro g hg
    rcases hg with h1 | h1
    · rw [h1]; exact htT
    · rw [h1]
      rcases C.hu₀ with h2 | h2
      · rw [← h2]; exact hu₀T
      · have : u = t * u₀ := by rw [h2, ← mul_assoc, h.t_mul_t, one_mul]
        rw [this]; exact mul_mem htT hu₀T
  have hxjT : ∀ j : ℤ, x ^ j ∈ T := fun j => zpow_mem hxT j
  have hrefl : ∀ p ∈ P, ∃ k : ℤ, p * t * p⁻¹ = t * x ^ k := by
    intro p hp
    have htP : t ∈ P := C.R_le SecTwoHyp.t_mem_R
    exact hG.toGoodCore.refl_of_tConj ⟨p, rfl⟩
      (hcl _ (mul_mem (mul_mem hp htP) (inv_mem hp)) ⟨p, rfl⟩)
  have heven : ∀ p ∈ P, ∀ k : ℤ, p * t * p⁻¹ = t * x ^ k → Even k → p ∈ T := by
    intro p hp k hk hev
    have h1 : (1 : G) * t * (1 : G)⁻¹ = t * x ^ (0 : ℤ) := by group
    obtain ⟨j, r, hr, hpr⟩ := hG.toGoodCore.exists_mul_of_conj_parity (one_mem P) hp h1 hk
      (by simpa using hev.neg)
    rw [hpr]
    exact mul_mem (mul_mem (hxjT j) (one_mem T)) (hRT hr)
  suffices hmain : ∃ a ∈ P, ∀ b ∈ P, a * b ∈ T ∨ b ∈ T by
    obtain ⟨a, haP, ha⟩ := hmain
    rw [Subgroup.relIndex, Subgroup.index_dvd_two_iff]
    refine ⟨⟨a⁻¹, inv_mem haP⟩, fun b => ?_⟩
    simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul]
    rcases ha (b : G)⁻¹ (inv_mem b.2) with h1 | h1
    · left
      have := inv_mem h1
      simpa [mul_assoc] using this
    · right
      have := inv_mem h1
      simpa using this
  by_cases hall : ∀ b ∈ P, b ∈ T
  · exact ⟨1, one_mem P, fun b hb => Or.inr (hall b hb)⟩
  push Not at hall
  obtain ⟨p₁, hp₁P, hp₁T⟩ := hall
  obtain ⟨k₁, hk₁⟩ := hrefl p₁ hp₁P
  have hk₁odd : Odd k₁ := by
    by_contra hna
    rw [Int.not_odd_iff_even] at hna
    exact hp₁T (heven p₁ hp₁P k₁ hk₁ hna)
  refine ⟨p₁⁻¹, inv_mem hp₁P, fun b hb => ?_⟩
  obtain ⟨kb, hkb⟩ := hrefl b hb
  rcases Int.even_or_odd kb with hev | hod
  · exact Or.inr (heven b hb kb hkb hev)
  · left
    obtain ⟨j, r, hr, hbr⟩ := hG.toGoodCore.exists_mul_of_conj_parity hp₁P hb hk₁ hkb
      (by
        obtain ⟨a, ha⟩ := hk₁odd
        obtain ⟨c, hc⟩ := hod
        exact ⟨a - c, by omega⟩)
    rw [hbr]
    have hq : p₁⁻¹ * x ^ j * p₁ ∈ closure ({t, x} : Set G) := by
      have := (mem_normalizer_iff.mp (hQ p₁⁻¹ (inv_mem hp₁P)) (x ^ j)).mp
        (zpow_mem (subset_closure (by simp) : x ∈ closure ({t, x} : Set G)) j)
      simpa using this
    have hqT : p₁⁻¹ * x ^ j * p₁ ∈ T := by
      have hle : closure ({t, x} : Set G) ≤ T := by
        apply Subgroup.closure_mono
        intro g hg
        rcases hg with h1 | h1
        · exact Or.inl h1
        · exact Or.inr (Or.inl h1)
      exact hle hq
    have e : p₁⁻¹ * (x ^ j * p₁ * r) = (p₁⁻¹ * x ^ j * p₁) * r := by group
    rw [e]
    exact mul_mem hqT (hRT hr)

end Good

theorem exists_shape (C : SixAY t u P V v u₀ y₀)
    (hquot : (∀ p ∈ P, ∀ w ∈ zpowers u₀, p * w * p⁻¹ ∈ zpowers u₀) →
      ∃ (_ : ((zpowers u₀).subgroupOf P).Normal),
        (∃ m : ℕ, 1 ≤ m ∧
          Nonempty ((P ⧸ (zpowers u₀).subgroupOf P) ≃* DihedralGroup (2 ^ m))) ∨
          ∃ k : ℕ, 4 ≤ k ∧
            Nonempty ((P ⧸ (zpowers u₀).subgroupOf P) ≃* SemidihedralGroup k)) :
    ∃ (T : Subgroup G) (n : ℕ) (x : G), TwoGroupShape P t (u ^ 2) n x u₀ T := by
  obtain ⟨x, n, hG, hcl⟩ := exists_closed_good C
  obtain ⟨hQ, hPP, hcls⟩ := hG.close hcl
  have h := C.secTwo
  have htP : t ∈ P := C.R_le SecTwoHyp.t_mem_R
  have htQ : t ∈ closure ({t, x} : Set G) := subset_closure (by simp)
  have hxQ : x ∈ closure ({t, x} : Set G) := subset_closure (by simp)
  have hU : ∀ p ∈ P, ∀ w ∈ zpowers u₀, p * w * p⁻¹ ∈ zpowers u₀ := by
    intro p hp w hw
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hw
    have := hG.conj_u₀_mem (hPP p hp)
    rw [← conj_zpow]
    exact zpow_mem this k
  have hzQ : u ^ 2 ∈ closure ({t, x} : Set G) := by
    rw [← hG.zx_eq]; exact pow_mem hxQ _
  have hzU : u ^ 2 ∈ zpowers u₀ := by
    rw [← C.u₀_sq]; exact pow_mem (mem_zpowers u₀) 2
  have hTP : closure ({t, x, u₀} : Set G) ≤ P := by
    rw [closure_le]
    intro g hg
    rcases hg with h1 | h1 | h1
    · rw [h1]; exact htP
    · rw [h1]; exact hG.x_mem
    · rw [h1]; exact C.u₀_mem_P
  refine ⟨closure ({t, x, u₀} : Set G), n, x, ?_⟩
  exact
    { three_le := hG.three_le
      ord_x := hG.ord
      inv_x := hG.dih.tx
      z_eq := hG.zx_eq
      ord_u := C.u₀_order
      sq_u := C.u₀_sq
      comm_ut := C.t_u₀.symm
      comm_ux := hG.u₀_x
      inf_eq := by
        apply le_antisymm
        · intro g hg
          obtain ⟨k, hk⟩ := mem_zpowers_iff.mp hg.1
          have hc : ∀ q ∈ closure ({t, x} : Set G), g * q = q * g := by
            intro q hq
            rw [← hk]
            exact (Commute.zpow_left (show Commute u₀ q from hG.u₀_comm hq) k).eq
          rcases hG.eq_one_or_z_of_central hg.2 hc with h1 | h1
          · rw [h1]; exact one_mem _
          · rw [h1]; exact mem_zpowers _
        · exact le_inf ((zpowers_le).mpr hzU) ((zpowers_le).mpr hzQ)
      T_eq := rfl
      T_le := hTP
      T_idx := hG.relIndex_T hQ hcls
      R_le := by
        intro g hg
        have hgR : g ∈ secTwoR t u := by
          rw [← h.inf_centralizer_eq C.pgroup C.R_le]
          exact ⟨hg.2, hg.1⟩
        have hRT : secTwoR t u ≤ closure ({t, x, u₀} : Set G) := by
          rw [secTwoR, closure_le]
          intro a ha
          rcases ha with h1 | h1
          · rw [h1]; exact subset_closure (by simp)
          · rw [h1]
            rcases C.hu₀ with h2 | h2
            · rw [← h2]; exact subset_closure (by simp)
            · have hu : u = t * u₀ := by rw [h2, ← mul_assoc, h.t_mul_t, one_mul]
              rw [hu]
              exact mul_mem (subset_closure (by simp)) (subset_closure (by simp))
        exact hRT hgR
      U_norm := hU
      U_central := by
        intro g hg
        have hle : closure ({t, x, u₀} : Set G) ≤ centralizer ({u₀} : Set G) := by
          rw [closure_le]
          intro a ha
          rcases ha with h1 | h1 | h1
          · rw [h1, SetLike.mem_coe, mem_centralizer_singleton_iff]; exact C.t_u₀
          · rw [h1, SetLike.mem_coe, mem_centralizer_singleton_iff]; exact hG.u₀_x.symm
          · rw [h1, SetLike.mem_coe, mem_centralizer_singleton_iff]
        exact mem_centralizer_singleton_iff.mp (hle hg)
      class_le_D := fun g hg => hcls _ hg ⟨g, rfl⟩
      D_eq := by
        apply le_antisymm
        · rw [closure_le]
          intro s hs
          exact hcls s hs.1 hs.2
        · calc closure ({t, x} : Set G)
              = closure {s : G | TConj t s ∧ s ∈ closure ({t, x} : Set G)} := hG.gen
            _ ≤ closure {s : G | s ∈ P ∧ ∃ g : G, g * t * g⁻¹ = s} := by
              apply Subgroup.closure_mono
              intro s hs
              exact ⟨hG.toGoodCore.Q_le_P hs.2, hs.1⟩
      quot := hquot hU }

end CFSG.LocalAnalysis.EvenBN.Tits
