module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10Sylow

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

variable {G : Type} [Group G]

theorem sec12J_V_le_sylow [Finite G] {V R0 : Subgroup G} (hV2 : IsPGroup 2 V)
    (hR0 : IsSylow2Of R0 (normalizer (V : Set G))) : V ≤ R0 := by
  have h1 : IsPGroup 2 ↥(R0 ⊔ V) := hR0.2.1.to_sup_of_normal_right' hV2 hR0.1
  have h2 : R0 ⊔ V ≤ normalizer (V : Set G) := sup_le hR0.1 Subgroup.le_normalizer
  have h3 := IsSylow2Of.eq_of_le hR0 h2 h1 le_sup_left
  rw [← h3]
  exact le_sup_right

theorem sec12J_mem_sup_of_comm {V O : Subgroup G} (hVO : ∀ v ∈ V, ∀ o ∈ O, v * o = o * v)
    {g : G} (hg : g ∈ V ⊔ O) : ∃ v ∈ V, ∃ o ∈ O, g = v * o := by
  let P : Subgroup G :=
    { carrier := {x | ∃ v ∈ V, ∃ o ∈ O, x = v * o}
      mul_mem' := by
        rintro _ _ ⟨v1, hv1, o1, ho1, rfl⟩ ⟨v2, hv2, o2, ho2, rfl⟩
        refine ⟨v1 * v2, V.mul_mem hv1 hv2, o1 * o2, O.mul_mem ho1 ho2, ?_⟩
        have h : o1 * v2 = v2 * o1 := (hVO v2 hv2 o1 ho1).symm
        calc v1 * o1 * (v2 * o2) = v1 * (o1 * v2) * o2 := by group
          _ = v1 * (v2 * o1) * o2 := by rw [h]
          _ = v1 * v2 * (o1 * o2) := by group
      one_mem' := ⟨1, V.one_mem, 1, O.one_mem, (mul_one 1).symm⟩
      inv_mem' := by
        rintro _ ⟨v, hv, o, ho, rfl⟩
        refine ⟨v⁻¹, V.inv_mem hv, o⁻¹, O.inv_mem ho, ?_⟩
        have hc : Commute v o := hVO v hv o ho
        rw [mul_inv_rev]
        exact hc.inv_inv.eq.symm }
  have hle : V ⊔ O ≤ P :=
    sup_le (fun v hv => ⟨v, hv, 1, O.one_mem, (mul_one v).symm⟩)
      (fun o ho => ⟨1, V.one_mem, o, ho, (one_mul o).symm⟩)
  exact hle hg

theorem sec12J_twoElem_mem {V O : Subgroup G} (hV2 : ∀ v ∈ V, v * v = 1)
    (hVO : ∀ v ∈ V, ∀ o ∈ O, v * o = o * v) (hO : ∀ o ∈ O, Odd (orderOf o)) {g : G}
    (hg : g ∈ V ⊔ O) (hg2 : ∃ m : ℕ, g ^ (2 ^ m) = 1) : g ∈ V := by
  obtain ⟨v, hv, o, ho, rfl⟩ := sec12J_mem_sup_of_comm hVO hg
  obtain ⟨m, hm⟩ := hg2
  have hc : Commute v o := hVO v hv o ho
  rcases Nat.eq_zero_or_pos m with rfl | hmpos
  · simp only [pow_zero, pow_one] at hm
    rw [hm]
    exact V.one_mem
  · have hv1 : v ^ (2 ^ m) = 1 := by
      obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
      have hv2 : v ^ 2 = 1 := by rw [pow_two]; exact hV2 v hv
      rw [pow_succ', pow_mul, hv2, one_pow]
    rw [hc.mul_pow, hv1, one_mul] at hm
    have ho1 : o = 1 := by
      have hdvd : orderOf o ∣ 2 ^ m := orderOf_dvd_of_pow_eq_one hm
      have hcop : Nat.Coprime (orderOf o) (2 ^ m) :=
        (Nat.coprime_two_right.mpr (hO o ho)).pow_right m
      exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop dvd_rfl hdvd)
    rw [ho1, mul_one]
    exact hv

end CFSG.OddStandard.SmallF3.Omega
