module

public import CFSG.GH74.Uniqueness.Section14Defs

public section

namespace CFSG.GH74.Uniqueness

open Subgroup

namespace Sec147

variable {X : Type} [Group X] {Z : Set X} {M : Subgroup X} {t : X} {n r : ℕ}
  {L K J Mo P U T S2 : Subgroup X}

section Facts

variable (F : Facts14 Z M t n r L K J Mo P U T S2)
include F

theorem P_le_T : P ≤ T := by
  rw [F.T_eq]
  exact le_sup_left

theorem U_le_T : U ≤ T := by
  rw [F.T_eq]
  exact le_sup_right

theorem Mo_le_T : Mo ≤ T := F.Mo_le_P.trans (P_le_T F)

theorem Mo_le_S2 : Mo ≤ S2 := (Mo_le_T F).trans F.T_le_S2

theorem Mo_sup_U_le_T : Mo ⊔ U ≤ T := sup_le (Mo_le_T F) (U_le_T F)

theorem T_le_normalizer_L : T ≤ normalizer (L : Set X) := F.T_sylow.le

theorem S2_le_normalizer_T : S2 ≤ normalizer (T : Set X) := F.S2_sylow.le

theorem K_le_L : K ≤ L := by
  rw [F.K_eq]
  exact inf_le_right

theorem K_le_D : K ≤ dGrp M t := by
  rw [F.K_eq]
  exact inf_le_left

theorem comm_L_J {l j : X} (hl : l ∈ L) (hj : j ∈ J) : l * j = j * l := by
  have h : j ∈ centralizer (L : Set X) := by
    rw [← F.J_eq]
    exact hj
  exact mem_centralizer_iff.mp h l hl

theorem comm_P_U {x u : X} (hx : x ∈ P) (hu : u ∈ U) : x * u = u * x :=
  comm_L_J F (F.P_le_L hx) (F.U_le_J hu)

theorem comm_Mo_U {m u : X} (hm : m ∈ Mo) (hu : u ∈ U) : m * u = u * m :=
  comm_P_U F (F.Mo_le_P hm) hu

theorem comm_K_U {k u : X} (hk : k ∈ K) (hu : u ∈ U) : k * u = u * k :=
  comm_L_J F (K_le_L F hk) (F.U_le_J hu)

theorem comm_K_J {k j : X} (hk : k ∈ K) (hj : j ∈ J) : k * j = j * k :=
  comm_L_J F (K_le_L F hk) hj

theorem eq_one_of_mem_P_of_mem_U {x : X} (hxP : x ∈ P) (hxU : x ∈ U) : x = 1 := by
  have h : x ∈ L ⊓ J := mem_inf.mpr ⟨F.P_le_L hxP, F.U_le_J hxU⟩
  rw [F.L_inf_J] at h
  exact mem_bot.mp h

theorem eq_one_of_mem_Mo_of_mem_U {x : X} (hxM : x ∈ Mo) (hxU : x ∈ U) : x = 1 :=
  eq_one_of_mem_P_of_mem_U F (F.Mo_le_P hxM) hxU

theorem P_inf_U : P ⊓ U = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  exact mem_bot.mpr (eq_one_of_mem_P_of_mem_U F (mem_inf.mp hx).1 (mem_inf.mp hx).2)

theorem Mo_inf_U : Mo ⊓ U = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  exact mem_bot.mpr (eq_one_of_mem_Mo_of_mem_U F (mem_inf.mp hx).1 (mem_inf.mp hx).2)

theorem U_le_normalizer_P : U ≤ normalizer (P : Set X) := fun _ hu =>
  centralizer_le_normalizer _ (mem_centralizer_iff.mpr fun _ hx => comm_P_U F hx hu)

theorem U_le_normalizer_Mo : U ≤ normalizer (Mo : Set X) := fun _ hu =>
  centralizer_le_normalizer _ (mem_centralizer_iff.mpr fun _ hm => comm_Mo_U F hm hu)

theorem exists_mul_of_mem_T {x : X} (hx : x ∈ T) : ∃ p ∈ P, ∃ u ∈ U, x = p * u := by
  rw [F.T_eq, ← SetLike.mem_coe,
    coe_mul_of_right_le_normalizer_left P U (U_le_normalizer_P F)] at hx
  obtain ⟨p, hp, u, hu, rfl⟩ := hx
  exact ⟨p, hp, u, hu, rfl⟩

theorem mul_mem_T {p u : X} (hp : p ∈ P) (hu : u ∈ U) : p * u ∈ T :=
  mul_mem (P_le_T F hp) (U_le_T F hu)

theorem decomp_unique {p p' u u' : X} (hp : p ∈ P) (hp' : p' ∈ P) (hu : u ∈ U) (hu' : u' ∈ U)
    (h : p * u = p' * u') : p = p' ∧ u = u' := by
  have h1 : p'⁻¹ * p = u' * u⁻¹ := by
    calc p'⁻¹ * p = p'⁻¹ * (p * u) * u⁻¹ := by group
      _ = p'⁻¹ * (p' * u') * u⁻¹ := by rw [h]
      _ = u' * u⁻¹ := by group
  have h2 : p'⁻¹ * p = 1 := by
    refine eq_one_of_mem_P_of_mem_U F (mul_mem (inv_mem hp') hp) ?_
    rw [h1]
    exact mul_mem hu' (inv_mem hu)
  have h3 : p = p' := by
    have := congrArg (p' * ·) h2
    simpa using this
  subst h3
  exact ⟨rfl, mul_left_cancel h⟩

theorem exists_mul_of_mem_Mo_sup_U {x : X} (hx : x ∈ Mo ⊔ U) : ∃ m ∈ Mo, ∃ u ∈ U, x = m * u := by
  rw [← SetLike.mem_coe,
    coe_mul_of_right_le_normalizer_left Mo U (U_le_normalizer_Mo F)] at hx
  obtain ⟨m, hm, u, hu, rfl⟩ := hx
  exact ⟨m, hm, u, hu, rfl⟩

theorem mul_mul_self_PU {p u : X} (hp : p ∈ P) (hu : u ∈ U) : p * u * (p * u) = p * p := by
  calc p * u * (p * u) = p * (u * p) * u := by group
    _ = p * (p * u) * u := by rw [← comm_P_U F hp hu]
    _ = p * p * (u * u) := by group
    _ = p * p := by rw [F.U_sq u hu, mul_one]

theorem mul_self_mem_Mo_of_mem_T {x : X} (hx : x ∈ T) : x * x ∈ Mo := by
  obtain ⟨p, hp, u, hu, rfl⟩ := exists_mul_of_mem_T F hx
  rw [mul_mul_self_PU F hp hu]
  exact F.P_sq p hp

theorem mul_self_eq_one_of_mem_Mo_sup_U {z : X} (hz : z ∈ Mo ⊔ U) : z * z = 1 := by
  obtain ⟨m, hm, u, hu, rfl⟩ := exists_mul_of_mem_Mo_sup_U F hz
  calc m * u * (m * u) = m * (u * m) * u := by group
    _ = m * (m * u) * u := by rw [← comm_Mo_U F hm hu]
    _ = (m * m) * (u * u) := by group
    _ = 1 := by rw [F.Mo_sq m hm, F.U_sq u hu, mul_one]

theorem mem_Mo_sup_U_of_mul_self_eq_one {x : X} (hx : x ∈ T) (h : x * x = 1) : x ∈ Mo ⊔ U := by
  obtain ⟨p, hp, u, hu, rfl⟩ := exists_mul_of_mem_T F hx
  rw [mul_mul_self_PU F hp hu] at h
  have hpM : p ∈ Mo := by
    by_contra hpM
    exact F.P_sq_ne p hp hpM h
  exact mul_mem (mem_sup_left hpM) (mem_sup_right hu)

theorem comm_T_Mo {x m : X} (hx : x ∈ T) (hm : m ∈ Mo) : x * m = m * x := by
  obtain ⟨p, hp, u, hu, rfl⟩ := exists_mul_of_mem_T F hx
  calc p * u * m = p * (u * m) := by rw [mul_assoc]
    _ = p * (m * u) := by rw [← comm_Mo_U F hm hu]
    _ = (p * m) * u := by rw [mul_assoc]
    _ = (m * p) * u := by rw [F.Mo_central p hp m hm]
    _ = m * (p * u) := by rw [mul_assoc]

theorem mem_Mo_sup_U_of_central {x : X} (hx : x ∈ T) (hc : ∀ y ∈ T, x * y = y * x) :
    x ∈ Mo ⊔ U := by
  obtain ⟨p, hp, u, hu, rfl⟩ := exists_mul_of_mem_T F hx
  have hpc : ∀ y ∈ P, p * y = y * p := by
    intro y hy
    have h := hc y (P_le_T F hy)
    have h' : p * y * u = y * p * u := by
      calc p * y * u = p * (y * u) := by rw [mul_assoc]
        _ = p * (u * y) := by rw [comm_P_U F hy hu]
        _ = p * u * y := by rw [mul_assoc]
        _ = y * (p * u) := h
        _ = y * p * u := by rw [mul_assoc]
    exact mul_right_cancel h'
  exact mul_mem (mem_sup_left (F.center_P p hp hpc)) (mem_sup_right hu)

theorem K_le_normalizer_P : K ≤ normalizer (P : Set X) := (K_le_D F).trans F.D_norm_P

theorem K_le_normalizer_U : K ≤ normalizer (U : Set X) := fun _ hk =>
  centralizer_le_normalizer _ (mem_centralizer_iff.mpr fun _ hu => (comm_K_U F hk hu).symm)

theorem K_le_normalizer_T : K ≤ normalizer (T : Set X) := by
  intro k hk
  rw [F.T_eq]
  exact inf_normalizer_le_normalizer_sup P U
    (mem_inf.mpr ⟨K_le_normalizer_P F hk, K_le_normalizer_U F hk⟩)

theorem mem_normalizer_T_of_mem_J {j : X} (hj : j ∈ J) (hjU : j ∈ normalizer (U : Set X)) :
    j ∈ normalizer (T : Set X) := by
  rw [F.T_eq]
  refine inf_normalizer_le_normalizer_sup P U (mem_inf.mpr ⟨?_, hjU⟩)
  exact centralizer_le_normalizer _
    (mem_centralizer_iff.mpr fun _ hx => comm_L_J F (F.P_le_L hx) hj)

theorem isPGroup_S2 : IsPGroup 2 S2 := F.S2_sylow.isPGroup

variable [Finite X]

theorem not_dvd_card_S2 {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) : ¬ p ∣ Nat.card S2 := by
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (isPGroup_S2 F)
  rw [hk]
  intro h
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h))

theorem S2_inf_normalizer_L : S2 ⊓ normalizer (L : Set X) = T :=
  F.T_sylow.eq_of_le (le_inf F.T_le_S2 (T_le_normalizer_L F)) inf_le_right
    (isPGroup_S2 F).to_inf_left

theorem mem_T_of_mem_S2_of_mem_normalizer_L {x : X} (hx : x ∈ S2)
    (hxN : x ∈ normalizer (L : Set X)) : x ∈ T := by
  rw [← S2_inf_normalizer_L F]
  exact mem_inf.mpr ⟨hx, hxN⟩

end Facts

section Concl

variable (h146 : Concl146 M t n K Mo U T S2)
include h146

theorem comm_S2_Mo {x m : X} (hx : x ∈ S2) (hm : m ∈ Mo) : x * m = m * x :=
  ((mem_centralizer_iff.mp (h146.S2_le_C0 hx)) m hm).symm

end Concl

end Sec147

end CFSG.GH74.Uniqueness
