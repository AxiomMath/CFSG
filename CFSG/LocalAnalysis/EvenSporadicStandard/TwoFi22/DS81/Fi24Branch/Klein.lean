module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.StdBasic

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch

open Subgroup

variable {G : Type} [Group G]

structure KleinPair (t z : G) : Prop where
  t_sq : t ^ 2 = 1
  z_sq : z ^ 2 = 1
  comm : t * z = z * t
  t_ne : t ≠ 1
  z_ne : z ≠ 1
  tz_ne : t ≠ z

theorem mem_Vtz_iff {t z : G} (h : KleinPair t z) {x : G} :
    x ∈ Vtz t z ↔ x = 1 ∨ x = t ∨ x = z ∨ x = t * z := by
  constructor
  · intro hx
    induction hx using Subgroup.closure_induction with
    | mem x hx =>
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr (Or.inl rfl))
    | one => exact Or.inl rfl
    | mul x y _ _ ihx ihy =>
      have htt : t * t = 1 := by rw [← pow_two, h.t_sq]
      have hzz : z * z = 1 := by rw [← pow_two, h.z_sq]
      have hzt : z * t = t * z := h.comm.symm
      have ht_tz : t * (t * z) = z := by rw [← mul_assoc, htt, one_mul]
      have hz_tz : z * (t * z) = t := by rw [← mul_assoc, hzt, mul_assoc, hzz, mul_one]
      have htz_t : (t * z) * t = z := by rw [mul_assoc, hzt, ← mul_assoc, htt, one_mul]
      have htz_z : (t * z) * z = t := by rw [mul_assoc, hzz, mul_one]
      have htz_tz : (t * z) * (t * z) = 1 := by rw [← mul_assoc, htz_t, hzz]
      rcases ihx with rfl | rfl | rfl | rfl <;>
        rcases ihy with rfl | rfl | rfl | rfl <;>
        simp [htt, hzz, hzt, ht_tz, hz_tz, htz_t, htz_z, htz_tz]
    | inv x _ ihx =>
      have htt : t * t = 1 := by rw [← pow_two, h.t_sq]
      have hzz : z * z = 1 := by rw [← pow_two, h.z_sq]
      have htz_tz : (t * z) * (t * z) = 1 := by
        have hzt : z * t = t * z := h.comm.symm
        have htz_t : (t * z) * t = z := by rw [mul_assoc, hzt, ← mul_assoc, htt, one_mul]
        rw [← mul_assoc, htz_t, hzz]
      rcases ihx with rfl | rfl | rfl | rfl
      · exact Or.inl inv_one
      · exact Or.inr (Or.inl (inv_eq_of_mul_eq_one_left htt))
      · exact Or.inr (Or.inr (Or.inl (inv_eq_of_mul_eq_one_left hzz)))
      · exact Or.inr (Or.inr (Or.inr (inv_eq_of_mul_eq_one_left htz_tz)))
  · rintro (rfl | rfl | rfl | rfl)
    · exact one_mem _
    · exact subset_closure (by simp)
    · exact subset_closure (by simp)
    · exact mul_mem (subset_closure (by simp)) (subset_closure (by simp))

theorem card_Vtz [Finite G] {t z : G} (h : KleinPair t z) : Nat.card ↥(Vtz t z) = 4 := by
  have hset : (Vtz t z : Set G) = ({1, t, z, t * z} : Set G) := by
    ext x
    change x ∈ Vtz t z ↔ x ∈ ({1, t, z, t * z} : Set G)
    rw [mem_Vtz_iff h]
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  have htt : t * t = 1 := by rw [← pow_two, h.t_sq]
  have hzz : z * z = 1 := by rw [← pow_two, h.z_sq]
  have hzt : z * t = t * z := h.comm.symm
  have htz_t : (t * z) * t = z := by rw [mul_assoc, hzt, ← mul_assoc, htt, one_mul]
  have htz1 : t * z ≠ 1 := by
    intro hc
    apply h.tz_ne
    calc t = t⁻¹ := (inv_eq_of_mul_eq_one_left htt).symm
      _ = z := inv_eq_of_mul_eq_one_right hc
  have htzt : t * z ≠ t := by
    intro hc
    exact h.z_ne (mul_left_cancel (show t * z = t * 1 by rw [mul_one]; exact hc))
  have hztz : z ≠ t * z := by
    intro hc
    exact h.t_ne (mul_right_cancel (show (1 : G) * z = t * z by rw [one_mul]; exact hc)).symm
  have h1mem : (1 : G) ∉ ({t, z, t * z} : Set G) := by
    rw [Set.mem_insert_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or, not_or]
    exact ⟨h.t_ne.symm, h.z_ne.symm, htz1.symm⟩
  have h2mem : t ∉ ({z, t * z} : Set G) := by
    rw [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨h.tz_ne, htzt.symm⟩
  have h3mem : z ∉ ({t * z} : Set G) := by
    rw [Set.mem_singleton_iff]
    exact hztz
  have hncard : ({1, t, z, t * z} : Set G).ncard = 4 := by
    rw [Set.ncard_insert_of_notMem h1mem, Set.ncard_insert_of_notMem h2mem,
      Set.ncard_insert_of_notMem h3mem, Set.ncard_singleton]
  calc Nat.card ↥(Vtz t z) = (Vtz t z : Set G).ncard := Nat.card_coe_set_eq _
    _ = ({1, t, z, t * z} : Set G).ncard := by rw [hset]
    _ = 4 := hncard

theorem t_mem_Vtz {t z : G} : t ∈ Vtz t z := subset_closure (by simp)

theorem z_mem_Vtz {t z : G} : z ∈ Vtz t z := subset_closure (by simp)

variable [Finite G] {L E : Subgroup G} {t z : G}

theorem Std.klein (h : Std G L E t) (hz : IsZ E t z) : KleinPair t z := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact h.m24.E_sq t h.t_mem_E
  · exact h.m24.E_sq z hz.1
  · exact h.E_comm t h.t_mem_E z hz.1
  · exact h.m24.t_ne_one
  · exact hz.2.1
  · intro htz
    exact hz.2.2.1 ⟨1, (normalizer (E : Set G)).one_mem, by rw [htz]; group⟩

end CFSG.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch
