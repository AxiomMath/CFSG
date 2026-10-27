module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M23Std.X1Setup

public section

namespace CFSG.EvenSporadicStandard.M23Std

open Subgroup

variable {G : Type} [Group G] {L : Subgroup G} {z t : G} {F L1 N : Subgroup G}

omit [Group G] in
theorem exists_sq_pow_of_odd {M : Type*} [Group M] {n : M} (hn : Odd (orderOf n)) :
    ∃ j : ℕ, (n ^ j) * (n ^ j) = n := by
  obtain ⟨k, hk⟩ := hn
  refine ⟨k + 1, ?_⟩
  rw [← pow_add, show k + 1 + (k + 1) = orderOf n + 1 by omega, pow_succ, pow_orderOf_eq_one,
    one_mul]

namespace Setup

variable (S : Setup L z t F L1 N)

include S

theorem exists_conj_decomp {x : G} (hx : z * (x * z * x⁻¹) ∈ centralizer (L1 : Set G)) :
    ∃ k ∈ Ksub z F, ∃ m ∈ N, x * z * x⁻¹ = m⁻¹ * (k * z * k⁻¹) * m := by
  have hz2 : z * z = 1 := S.one.z_mul_self
  have hzi : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz2
  have hzX : z ∈ normalizer (L1 : Set G) := S.K_le_X S.z_mem_K
  set z' : G := x * z * x⁻¹ with hz'
  have hz'2 : z' * z' = 1 := by
    rw [hz']
    calc x * z * x⁻¹ * (x * z * x⁻¹) = x * (z * z) * x⁻¹ := by group
      _ = 1 := by rw [hz2]; group
  have hz'eq : z' = z * (z * z') := by rw [← mul_assoc, hz2, one_mul]
  have hc₀ : z * z' ∈ N ⊔ L1 := by rw [S.N_sup]; exact hx
  have hLN : ∀ l ∈ L1, ∀ y ∈ N, l * y * l⁻¹ ∈ N := fun l hl y hy =>
    S.N_norm l (mem_centralizer_iff.2 fun w hw => S.L1_comm w hw l hl) y hy
  obtain ⟨n, hn, l, hl, hc₀eq⟩ := exists_mul_of_normalizes hLN hc₀
  have hzc : z * (z * z') * z⁻¹ = (z * z')⁻¹ := by
    have h1 : z' * z' = 1 := hz'2
    rw [hz'eq] at h1
    rw [eq_inv_iff_mul_eq_one]
    calc z * (z * z') * z⁻¹ * (z * z') = z * (z * z') * z * (z * z') := by rw [hzi]
      _ = z * (z * z') * (z * (z * z')) := by group
      _ = 1 := h1
  have hnl : n * l = l * n := S.N_comm n hn l hl
  have hzn : z * n * z⁻¹ ∈ N := S.conj_N hzX hn
  have hzl : z * l * z⁻¹ ∈ L1 := (S.z_norm l).1 hl
  have hab : (z * n * z⁻¹) * (z * l * z⁻¹) = n⁻¹ * l⁻¹ := by
    have e1 : (z * n * z⁻¹) * (z * l * z⁻¹) = z * (n * l) * z⁻¹ := by group
    rw [e1, ← hc₀eq, hzc, hc₀eq, hnl, mul_inv_rev]
  have hNa : z * n * z⁻¹ = n⁻¹ ∧ z * l * z⁻¹ = l⁻¹ := by
    have h1 : n * (z * n * z⁻¹) = l⁻¹ * (z * l * z⁻¹)⁻¹ := by
      calc n * (z * n * z⁻¹)
          = n * ((z * n * z⁻¹) * (z * l * z⁻¹)) * (z * l * z⁻¹)⁻¹ := by group
        _ = n * (n⁻¹ * l⁻¹) * (z * l * z⁻¹)⁻¹ := by rw [hab]
        _ = l⁻¹ * (z * l * z⁻¹)⁻¹ := by group
    have hNmem : n * (z * n * z⁻¹) ∈ N := Subgroup.mul_mem _ hn hzn
    have hLmem : l⁻¹ * (z * l * z⁻¹)⁻¹ ∈ L1 :=
      Subgroup.mul_mem _ (Subgroup.inv_mem _ hl) (Subgroup.inv_mem _ hzl)
    have h2 : n * (z * n * z⁻¹) = 1 :=
      Subgroup.disjoint_def.1 S.N_disj hNmem (h1 ▸ hLmem)
    have ha : z * n * z⁻¹ = n⁻¹ := eq_inv_of_mul_eq_one_right h2
    refine ⟨ha, ?_⟩
    rw [ha] at hab
    exact mul_left_cancel hab
  obtain ⟨hzn', hzl'⟩ := hNa
  have hli : l⁻¹ = l := inv_eq_of_mul_eq_one_right (S.L1_sq l hl)
  have hzlcomm : z * l = l * z := by
    rw [hli] at hzl'
    exact mul_inv_eq_iff_eq_mul.1 hzl'
  have hlF : l ∈ F := S.L1_cz l hl hzlcomm
  obtain ⟨k, hk, hkl⟩ := S.phi_onto l hlF
  have hkz : k * z * k⁻¹ = z * l := by
    have h1 : z * (k * z * k⁻¹) = l := hkl
    calc k * z * k⁻¹ = z * (z * (k * z * k⁻¹)) := by rw [← mul_assoc, hz2, one_mul]
      _ = z * l := by rw [h1]
  have hodd : Odd (orderOf n) := by
    rcases Nat.even_or_odd (orderOf n) with he | ho
    · exact absurd (dvd_trans (even_iff_two_dvd.1 he) (Subgroup.orderOf_dvd_natCard N hn)) S.N_odd
    · exact ho
  obtain ⟨j, hj⟩ := exists_sq_pow_of_odd hodd
  have hmN : n ^ j ∈ N := Subgroup.pow_mem _ hn j
  have hzm : z * n ^ j = (n ^ j)⁻¹ * z := by
    have : z * n ^ j * z⁻¹ = (n ^ j)⁻¹ := by
      rw [← conj_pow, hzn', inv_pow]
    rw [← this]
    group
  refine ⟨k, hk, n ^ j, hmN, ?_⟩
  have hlm : l * n ^ j = n ^ j * l := (S.N_comm _ hmN l hl).symm
  have hn_eq : n = n ^ j * n ^ j := hj.symm
  calc x * z * x⁻¹ = z * (z * z') := hz'eq
    _ = z * (n * l) := by rw [hc₀eq]
    _ = z * (n ^ j * n ^ j * l) := by rw [← hn_eq]
    _ = (z * n ^ j) * (n ^ j * l) := by group
    _ = ((n ^ j)⁻¹ * z) * (n ^ j * l) := by rw [hzm]
    _ = (n ^ j)⁻¹ * ((z * n ^ j) * l) := by group
    _ = (n ^ j)⁻¹ * ((z * l) * n ^ j) := by
        rw [show z * n ^ j * l = z * (n ^ j * l) by group, ← hlm]; group
    _ = (n ^ j)⁻¹ * (k * z * k⁻¹) * n ^ j := by rw [hkz]; group

theorem exists_mem_centralizer_of_conj_mem {x : G} (hxX : x ∈ normalizer (L1 : Set G))
    (hx : z * (x * z * x⁻¹) ∈ centralizer (L1 : Set G)) :
    ∃ k ∈ Ksub z F, ∃ m ∈ N, ∃ u ∈ normalizer (L1 : Set G) ⊓ centralizer ({z} : Set G),
      x = m⁻¹ * k * u := by
  obtain ⟨k, hk, m, hm, hconj⟩ := S.exists_conj_decomp hx
  refine ⟨k, hk, m, hm, k⁻¹ * m * x, ?_, by group⟩
  refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
  · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ (S.K_le_X hk))
      (S.N_le_X hm)) hxX
  · rw [mem_centralizer_singleton_iff]
    have : x * z = m⁻¹ * (k * z * k⁻¹) * m * x := by
      calc x * z = (x * z * x⁻¹) * x := by group
        _ = m⁻¹ * (k * z * k⁻¹) * m * x := by rw [hconj]
    calc k⁻¹ * m * x * z = k⁻¹ * m * (x * z) := by group
      _ = k⁻¹ * m * (m⁻¹ * (k * z * k⁻¹) * m * x) := by rw [this]
      _ = z * (k⁻¹ * m * x) := by group

end Setup

end CFSG.EvenSporadicStandard.M23Std
