module

public import CFSG.GF2Type.CenterFour.Setting

public section

namespace CFSG.GF2Type.CenterFour

open Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {z : G} {n : ℕ}

theorem Config.center_le_core (hC : Config z n) : centerAt z ≤ coreAt z :=
  Subgroup.map_subtype_le _

theorem Config.mem_core (hC : Config z n) : z ∈ coreAt z :=
  Config.center_le_core hC hC.mem_center

theorem Config.core_le_centralizer (hC : Config z n) :
    coreAt z ≤ centralizer ({z} : Set G) :=
  Subgroup.map_subtype_le _

theorem Config.conj_mem_core (hC : Config z n) {h : G} (hh : h ∈ centralizer ({z} : Set G))
    {q : G} (hq : q ∈ coreAt z) : h * q * h⁻¹ ∈ coreAt z := by
  obtain ⟨q', hq', rfl⟩ := Subgroup.mem_map.mp hq
  exact Subgroup.mem_map.mpr
    ⟨(⟨h, hh⟩ : ↥(centralizer ({z} : Set G))) * q' * (⟨h, hh⟩ : ↥(centralizer ({z} : Set G)))⁻¹,
      Subgroup.Normal.conj_mem inferInstance q' hq' _, by simp⟩

theorem Config.core_le_centralizer_center (hC : Config z n) :
    coreAt z ≤ centralizer (centerAt z : Set G) := by
  intro q hq
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  have hy' : y ∈ centerAt z := hy
  obtain ⟨c, hc, rfl⟩ := Subgroup.mem_map.mp hy'
  have hcq := congrArg (coreAt z).subtype (Subgroup.mem_center_iff.mp hc ⟨q, hq⟩)
  rw [map_mul, map_mul] at hcq
  exact hcq.symm

theorem Config.eq_sq_of_orderOf_eq_two {k : G} (hZk : centerAt z = zpowers k)
    (hk4 : orderOf k = 4) {x : G} (hx : x ∈ centerAt z) (hx2 : orderOf x = 2) :
    x = k ^ 2 := by
  rw [hZk] at hx
  obtain ⟨m, hm⟩ := (Submonoid.mem_powers_iff _ _).1 (mem_powers_iff_mem_zpowers.2 hx)
  have hr : k ^ (m % 4) = x := by
    have := pow_mod_orderOf k m
    rw [hk4, hm] at this
    exact this
  obtain ⟨r, hr4, rfl⟩ : ∃ r < 4, k ^ r = x := ⟨m % 4, Nat.mod_lt _ (by norm_num), hr⟩
  interval_cases r
  · simp at hx2
  · rw [pow_one, hk4] at hx2
    norm_num at hx2
  · rfl
  · rw [orderOf_pow' (x := k) (n := 3) (by norm_num), hk4] at hx2
    norm_num at hx2

theorem Config.exists_gen_aux (hC : Config z n) :
    ∃ k : G, centerAt z = zpowers k ∧ orderOf k = 4 := by
  haveI := hC.center_cyclic
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := ↥(centerAt z))
  have hk : (g : G) ∈ centerAt z := g.2
  refine ⟨(g : G), ?_, ?_⟩
  · apply le_antisymm
    · intro y hy
      obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp (hg ⟨y, hy⟩)
      have hy' : (g : G) ^ m = y := by
        have := congrArg Subtype.val hm
        simpa using this
      rw [← hy']
      exact Subgroup.zpow_mem_zpowers _ m
    · exact Subgroup.zpowers_le.mpr hk
  · rw [Subgroup.orderOf_coe, orderOf_eq_card_of_forall_mem_zpowers hg, hC.card_center]

theorem Config.exists_generator (hC : Config z n) :
    ∃ k : G, centerAt z = zpowers k ∧ orderOf k = 4 ∧ k ^ 2 = z := by
  obtain ⟨k, hZk, hk4⟩ := hC.exists_gen_aux
  exact ⟨k, hZk, hk4, (Config.eq_sq_of_orderOf_eq_two hZk hk4 hC.mem_center hC.orderOf_eq).symm⟩

theorem Config.eq_of_mem_center (hC : Config z n) {y : G} (hy : y ∈ centerAt z)
    (hy2 : orderOf y = 2) : y = z := by
  obtain ⟨k, hZk, hk4⟩ := hC.exists_gen_aux
  rw [Config.eq_sq_of_orderOf_eq_two hZk hk4 hy hy2,
    Config.eq_sq_of_orderOf_eq_two hZk hk4 hC.mem_center hC.orderOf_eq]

theorem Config.inv_of_not_mem_centralizer (hC : Config z n) {h : G}
    (hh : h ∈ centralizer ({z} : Set G)) (hK : h ∉ centralizer (centerAt z : Set G)) {y : G}
    (hy : y ∈ centerAt z) : h * y * h⁻¹ = y⁻¹ := by
  obtain ⟨k, hZk, hk4, hk2⟩ := hC.exists_generator
  have hconj : ∀ x ∈ centerAt z, h * x * h⁻¹ ∈ centerAt z := by
    have hNh : h ∈ normalizer (centerAt z : Set G) := by
      rw [hC.normalizer_center]
      exact hh
    exact fun x hx => (Subgroup.mem_normalizer_iff.mp hNh x).mp hx
  have hordk : orderOf (h * k * h⁻¹) = 4 := by
    have := orderOf_injective (MulAut.conj h).toMonoidHom (MulAut.conj h).injective k
    rw [hk4] at this
    simpa [MulAut.conj_apply] using this
  have hmemk : h * k * h⁻¹ ∈ centerAt z := by
    apply hconj k
    rw [hZk]
    exact Subgroup.mem_zpowers k
  rw [hZk] at hmemk
  obtain ⟨m, hm⟩ := (Submonoid.mem_powers_iff _ _).1 (mem_powers_iff_mem_zpowers.2 hmemk)
  obtain ⟨r, hr4, hkr⟩ : ∃ r < 4, k ^ r = h * k * h⁻¹ :=
    ⟨m % 4, Nat.mod_lt _ (by norm_num), by
      have := pow_mod_orderOf k m
      rw [hk4, hm] at this
      exact this⟩
  have hk3 : k ^ 3 = k⁻¹ := by
    have hk4' : k ^ 4 = 1 := by
      rw [← hk4]
      exact pow_orderOf_eq_one k
    exact eq_inv_of_mul_eq_one_left (by rw [← pow_succ]; exact hk4')
  have hconjk : h * k * h⁻¹ = k⁻¹ := by
    interval_cases r
    · rw [← hkr] at hordk
      simp at hordk
    · exfalso
      apply hK
      have hcomm : Commute h k := by
        show h * k = k * h
        calc h * k = (h * k * h⁻¹) * h := by group
          _ = k ^ 1 * h := by rw [hkr]
          _ = k * h := by rw [pow_one]
      rw [Subgroup.mem_centralizer_iff]
      intro y hy'
      have hy'' : y ∈ centerAt z := hy'
      rw [hZk] at hy''
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy''
      exact ((hcomm.zpow_right j).eq).symm
    · rw [← hkr, hk2, hC.orderOf_eq] at hordk
      norm_num at hordk
    · rw [← hkr]
      exact hk3
  rw [hZk] at hy
  obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
  rw [← conj_zpow, hconjk, inv_zpow]

theorem Config.mul_mem_centralizer (hC : Config z n) {h₁ h₂ : G}
    (hh₁ : h₁ ∈ centralizer ({z} : Set G)) (hh₂ : h₂ ∈ centralizer ({z} : Set G))
    (hK₁ : h₁ ∉ centralizer (centerAt z : Set G)) (hK₂ : h₂ ∉ centralizer (centerAt z : Set G)) :
    h₁ * h₂ ∈ centralizer (centerAt z : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  have hy0 : y ∈ centerAt z := hy
  have h2 := hC.inv_of_not_mem_centralizer hh₂ hK₂ hy0
  have h3 := hC.inv_of_not_mem_centralizer hh₁ hK₁ (inv_mem hy0)
  rw [inv_inv] at h3
  have e2 : h₂ * y = y⁻¹ * h₂ := by
    calc h₂ * y = (h₂ * y * h₂⁻¹) * h₂ := by group
      _ = y⁻¹ * h₂ := by rw [h2]
  have e3 : h₁ * y⁻¹ = y * h₁ := by
    calc h₁ * y⁻¹ = (h₁ * y⁻¹ * h₁⁻¹) * h₁ := by group
      _ = y * h₁ := by rw [h3]
  calc y * (h₁ * h₂) = (y * h₁) * h₂ := by group
    _ = (h₁ * y⁻¹) * h₂ := by rw [e3]
    _ = h₁ * (y⁻¹ * h₂) := by group
    _ = h₁ * (h₂ * y) := by rw [e2]
    _ = h₁ * h₂ * y := by group

end CFSG.GF2Type.CenterFour
