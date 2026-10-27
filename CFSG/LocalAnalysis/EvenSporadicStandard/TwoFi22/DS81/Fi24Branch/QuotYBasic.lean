module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.CSetup

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch

open Subgroup

variable {C : Type} [Group C] [Finite C] {c : CInv C} {t : C} {R J K O Y : Subgroup C}

private theorem mul_inv_mem_of_relIndex_two {G : Type} [Group G] {O R : Subgroup G}
    (hidx : O.relIndex R = 2) {a b : G} (ha : a ∈ R) (hb : b ∈ R)
    (h : a ∈ O ↔ b ∈ O) : a * b⁻¹ ∈ O := by
  have hidx' : (O.subgroupOf R).index = 2 := hidx
  have key := Subgroup.mul_mem_iff_of_index_two (H := O.subgroupOf R) hidx'
      (a := (⟨a, ha⟩ : ↥R)) (b := (⟨b⁻¹, R.inv_mem hb⟩ : ↥R))
  change (⟨a, ha⟩ : ↥R) * ⟨b⁻¹, R.inv_mem hb⟩ ∈ O.subgroupOf R
  rw [key]
  simpa only [Subgroup.mem_subgroupOf, Subgroup.inv_mem_iff] using h

theorem O_le_R (hK : KDataC c t R J K O Y) : O ≤ R := by
  rw [← hK.O_eq]
  exact inf_le_left

theorem bar_Y_normalizes_R (hJ : JData c t R J) (hK : KDataC c t R J K O Y) :
    ∀ y ∈ c.bar Y, ∀ r ∈ c.bar R, y * r * y⁻¹ ∈ c.bar R := by
  rintro y hy r hr
  rcases Subgroup.mem_map.mp hy with ⟨y', hy'Y, rfl⟩
  rcases Subgroup.mem_map.mp hr with ⟨r', hr'R, rfl⟩
  refine Subgroup.mem_map.mpr ⟨y' * r' * y'⁻¹, ?_, ?_⟩
  · exact hJ.R_normal y' (hK.K_le_J (hK.Y_le hy'Y)) r' hr'R
  · simp

theorem comm_Y_R_mem_O (hR : RData c R) (hJ : JData c t R J) (hK : KDataC c t R J K O Y) :
    ∀ y ∈ Y, ∀ r ∈ R, y * r * y⁻¹ * r⁻¹ ∈ O := by
  intro y hy r hr
  have hyK : y ∈ K := hK.Y_le hy
  have hyJ : y ∈ J := hK.K_le_J hyK
  have hr''R : y * r * y⁻¹ ∈ R := hJ.R_normal y hyJ r hr
  have hmem : r ∈ O ↔ y * r * y⁻¹ ∈ O := by
    rw [← hK.O_eq]
    simp only [Subgroup.mem_inf]
    constructor
    · rintro ⟨-, hrK⟩
      exact ⟨hr''R, K.mul_mem (K.mul_mem hyK hrK) (K.inv_mem hyK)⟩
    · rintro ⟨-, hr''K⟩
      refine ⟨hr, ?_⟩
      have h : y⁻¹ * (y * r * y⁻¹) * y ∈ K :=
        K.mul_mem (K.mul_mem (K.inv_mem hyK) hr''K) hyK
      rwa [show y⁻¹ * (y * r * y⁻¹) * y = r by group] at h
  have hrel := Subgroup.relIndex_mul_card (H := O) (K := R)
  rw [inf_eq_left.mpr (O_le_R hK)] at hrel
  rw [hK.O_card, hR.card] at hrel
  have hidx : O.relIndex R = 2 := by
    rw [show (2 : ℕ) ^ 13 = 2 * 2 ^ 12 by ring] at hrel
    exact Nat.eq_of_mul_eq_mul_right (by norm_num) hrel
  exact mul_inv_mem_of_relIndex_two hidx hr''R hr hmem.symm

theorem bar_Y_comm_R_mem_bar_O (hR : RData c R) (hJ : JData c t R J)
    (hK : KDataC c t R J K O Y) :
    ∀ y ∈ c.bar Y, ∀ r ∈ c.bar R, y * r * y⁻¹ * r⁻¹ ∈ c.bar O := by
  rintro y hy r hr
  rcases Subgroup.mem_map.mp hy with ⟨y', hy'Y, rfl⟩
  rcases Subgroup.mem_map.mp hr with ⟨r', hr'R, rfl⟩
  refine Subgroup.mem_map.mpr ⟨y' * r' * y'⁻¹ * r'⁻¹,
    comm_Y_R_mem_O hR hJ hK y' hy'Y r' hr'R, ?_⟩
  simp

theorem bar_Y_normalizes_V (hK : KDataC c t R J K O Y) :
    ∀ y ∈ c.bar Y, ∀ v ∈ c.bar (closure {t, c.z}), y * v * y⁻¹ ∈ c.bar (closure {t, c.z}) := by
  rintro y hy v hv
  rcases Subgroup.mem_map.mp hy with ⟨y', hy'Y, rfl⟩
  rcases Subgroup.mem_map.mp hv with ⟨v', hv'V, rfl⟩
  have hy'K : y' ∈ K := hK.Y_le hy'Y
  have hyt : y' * t = t * y' := hK.K_cent y' hy'K
  have hyz : y' * c.z = c.z * y' := c.central y'
  have hcent : y' ∈ Subgroup.centralizer (closure ({t, c.z} : Set C)) := by
    rw [Subgroup.centralizer_closure, Subgroup.mem_centralizer_iff]
    intro h hh
    rcases hh with rfl | rfl
    · exact hyt.symm
    · exact hyz.symm
  have hv_comm : v' * y' = y' * v' := (Subgroup.mem_centralizer_iff.mp hcent) v' hv'V
  refine Subgroup.mem_map.mpr ⟨y' * v' * y'⁻¹, ?_, ?_⟩
  · have hconj : y' * v' * y'⁻¹ = v' := by
      rw [← hv_comm]
      group
    rw [hconj]
    exact hv'V
  · simp

theorem card_bar_V (hK : KDataC c t R J K O Y) :
    Nat.card ↥(c.bar (closure {t, c.z})) = 2 := by
  have hzV : zpowers c.z ≤ closure ({t, c.z} : Set C) := by
    rw [Subgroup.zpowers_le]
    exact Subgroup.subset_closure (by simp)
  have h := c.card_bar (S := closure {t, c.z}) hzV
  rw [hK.V_card] at h
  omega

theorem card_bar_O (hK : KDataC c t R J K O Y) : Nat.card ↥(c.bar O) = 2 ^ 11 := by
  have hzV : zpowers c.z ≤ closure ({t, c.z} : Set C) := by
    rw [Subgroup.zpowers_le]
    exact Subgroup.subset_closure (by simp)
  have hzO : zpowers c.z ≤ O := le_trans hzV hK.V_le
  have h := c.card_bar (S := O) hzO
  rw [hK.O_card] at h
  rw [show (2 : ℕ) ^ 12 = 2 * 2 ^ 11 by ring] at h
  exact (Nat.eq_of_mul_eq_mul_left (by norm_num) h).symm

theorem bar_V_le_bar_O (hK : KDataC c t R J K O Y) :
    c.bar (closure {t, c.z}) ≤ c.bar O :=
  c.bar_mono hK.V_le

theorem bar_O_le_bar_R (hK : KDataC c t R J K O Y) : c.bar O ≤ c.bar R :=
  c.bar_mono (O_le_R hK)

theorem bar_lattice (hK : KDataC c t R J K O Y) (U : Subgroup c.Qt)
    (hVU : c.bar (closure {t, c.z}) ≤ U) (hUO : U ≤ c.bar O)
    (hY : ∀ y ∈ c.bar Y, ∀ u ∈ U, y * u * y⁻¹ ∈ U) :
    Nat.card ↥U = 2 ∨ Nat.card ↥U = 2 ^ 2 ∨ Nat.card ↥U = 2 ^ 10 ∨ Nat.card ↥U = 2 ^ 11 := by
  have hzV : zpowers c.z ≤ closure ({t, c.z} : Set C) := by
    rw [Subgroup.zpowers_le]
    exact Subgroup.subset_closure (by simp)
  have hzO : zpowers c.z ≤ O := le_trans hzV hK.V_le
  have hVU' : closure {t, c.z} ≤ U.comap c.qmap := by
    intro x hx
    rw [Subgroup.mem_comap]
    exact hVU (Subgroup.mem_map.mpr ⟨x, hx, rfl⟩)
  have hUO' : U.comap c.qmap ≤ O := by
    intro x hx
    rw [Subgroup.mem_comap] at hx
    exact (c.qmap_mem_bar_iff hzO).mp (hUO hx)
  have hY' : ∀ y ∈ Y, ∀ u ∈ U.comap c.qmap, y * u * y⁻¹ ∈ U.comap c.qmap := by
    intro y hy u hu
    rw [Subgroup.mem_comap] at hu ⊢
    have hybar : c.qmap y ∈ c.bar Y := Subgroup.mem_map.mpr ⟨y, hy, rfl⟩
    have hcomm := hY (c.qmap y) hybar (c.qmap u) hu
    simpa only [map_mul, map_inv] using hcomm
  have hlat := hK.lattice (U.comap c.qmap) hVU' hUO' hY'
  rw [c.card_comap U] at hlat
  rcases hlat with h | h | h | h
  · left
    rw [show (2 : ℕ) ^ 2 = 2 * 2 by ring] at h
    exact Nat.eq_of_mul_eq_mul_left (by norm_num) h
  · right; left
    rw [show (2 : ℕ) ^ 3 = 2 * 2 ^ 2 by ring] at h
    exact Nat.eq_of_mul_eq_mul_left (by norm_num) h
  · right; right; left
    rw [show (2 : ℕ) ^ 11 = 2 * 2 ^ 10 by ring] at h
    exact Nat.eq_of_mul_eq_mul_left (by norm_num) h
  · right; right; right
    rw [show (2 : ℕ) ^ 12 = 2 * 2 ^ 11 by ring] at h
    exact Nat.eq_of_mul_eq_mul_left (by norm_num) h

end CFSG.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch
