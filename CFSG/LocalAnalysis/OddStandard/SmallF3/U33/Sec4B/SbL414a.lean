module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbC414Grp

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup

variable {G : Type} [Group G] {t τ ω : G}

private def D8mem (t τ ω x : G) : Prop :=
  x = 1 ∨ x = τ ∨ x = t ∨ x = t * τ ∨ x = ω ∨ x = ω * τ ∨ x = t * ω ∨ x = t * ω * τ

private lemma mul_self_eq_one_of_sq {a : G} (h : a ^ 2 = 1) : a * a = 1 := by
  rwa [pow_two] at h

private lemma inv_eq_self_of_sq {a : G} (h : a ^ 2 = 1) : a⁻¹ = a :=
  inv_eq_of_mul_eq_one_left (mul_self_eq_one_of_sq h)

theorem om_tau_comm (ht2 : t ^ 2 = 1) (hω2 : ω ^ 2 = 1) (hτ2 : τ ^ 2 = 1) (htτ : t * τ = τ * t)
    (hω : ω * t * ω⁻¹ = t * τ) : ω * τ = τ * ω := by
  have ht2' : t * t = 1 := mul_self_eq_one_of_sq ht2
  have hω2' : ω * ω = 1 := mul_self_eq_one_of_sq hω2
  have hω_inv : ω⁻¹ = ω := inv_eq_self_of_sq hω2
  have hω' : ω * t * ω = t * τ := by simpa only [hω_inv] using hω
  have hτeq : τ = t * ω * t * ω := by
    calc τ = t * (t * τ) := by rw [← mul_assoc, ht2', one_mul]
      _ = t * (ω * t * ω) := by rw [hω'.symm]
      _ = t * ω * t * ω := by group
  have h1 : (t * τ) * t = τ := by rw [htτ, mul_assoc, ht2', mul_one]
  calc ω * τ = ω * (t * ω * t * ω) := by rw [hτeq]
    _ = (ω * t * ω) * t * ω := by group
    _ = (t * τ) * t * ω := by rw [hω']
    _ = τ * ω := by rw [h1]

theorem tau_mem_closure (ht2 : t ^ 2 = 1) (hω2 : ω ^ 2 = 1) (hτ2 : τ ^ 2 = 1)
    (htτ : t * τ = τ * t) (hω : ω * t * ω⁻¹ = t * τ) : τ ∈ closure ({t, ω} : Set G) := by
  have ht2' : t * t = 1 := mul_self_eq_one_of_sq ht2
  have hω_inv : ω⁻¹ = ω := inv_eq_self_of_sq hω2
  have hω' : ω * t * ω = t * τ := by simpa only [hω_inv] using hω
  have hτeq : τ = t * ω * t * ω := by
    calc τ = t * (t * τ) := by rw [← mul_assoc, ht2', one_mul]
      _ = t * (ω * t * ω) := by rw [hω'.symm]
      _ = t * ω * t * ω := by group
  rw [hτeq]
  exact (closure ({t, ω} : Set G)).mul_mem
    ((closure ({t, ω} : Set G)).mul_mem
      ((closure ({t, ω} : Set G)).mul_mem
        (Subgroup.subset_closure (by simp)) (Subgroup.subset_closure (by simp)))
      (Subgroup.subset_closure (by simp)))
    (Subgroup.subset_closure (by simp))

theorem mem_closure_t_om_iff (ht2 : t ^ 2 = 1) (hω2 : ω ^ 2 = 1) (hτ2 : τ ^ 2 = 1)
    (htτ : t * τ = τ * t) (hω : ω * t * ω⁻¹ = t * τ) (x : G) :
    x ∈ closure ({t, ω} : Set G) ↔
      x = 1 ∨ x = τ ∨ x = t ∨ x = t * τ ∨ x = ω ∨ x = ω * τ ∨ x = t * ω ∨ x = t * ω * τ := by
  have ht2' : t * t = 1 := mul_self_eq_one_of_sq ht2
  have hω2' : ω * ω = 1 := mul_self_eq_one_of_sq hω2
  have hτ2' : τ * τ = 1 := mul_self_eq_one_of_sq hτ2
  have hω_inv : ω⁻¹ = ω := inv_eq_self_of_sq hω2
  have ht_inv : t⁻¹ = t := inv_eq_self_of_sq ht2
  have hω' : ω * t * ω = t * τ := by simpa only [hω_inv] using hω
  have hωτ : ω * τ = τ * ω := om_tau_comm ht2 hω2 hτ2 htτ hω
  have hωt : ω * t = t * ω * τ := by
    calc ω * t = (ω * t * ω) * ω := by simp only [mul_assoc, hω2', mul_one]
      _ = (t * τ) * ω := by rw [hω']
      _ = t * ω * τ := by simp only [mul_assoc]; rw [hωτ]
  have httτ : t * (t * τ) = τ := by rw [← mul_assoc, ht2', one_mul]
  have httω : t * (t * ω) = ω := by rw [← mul_assoc, ht2', one_mul]
  have httωτ : t * (t * ω * τ) = ω * τ := by
    rw [← mul_assoc, ← mul_assoc, ht2', one_mul]
  have hωtτ : ω * (t * τ) = t * ω := by
    calc ω * (t * τ) = (ω * t) * τ := by rw [← mul_assoc]
      _ = (t * ω * τ) * τ := by rw [hωt]
      _ = t * ω := by rw [mul_assoc, hτ2', mul_one]
  have hωωτ : ω * (ω * τ) = τ := by rw [← mul_assoc, hω2', one_mul]
  have hωtω : ω * (t * ω) = t * τ := by rw [← mul_assoc, hω']
  have hωtωτ : ω * (t * ω * τ) = t := by
    calc ω * (t * ω * τ) = (ω * (t * ω)) * τ := by rw [← mul_assoc]
      _ = ((ω * t) * ω) * τ := by rw [← mul_assoc]
      _ = (t * τ) * τ := by rw [hω']
      _ = t := by rw [mul_assoc, hτ2', mul_one]
  have htQ : ∀ y, D8mem t τ ω y → D8mem t τ ω (t * y) := by
    intro y hy
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · simp [D8mem]
    · simp [D8mem]
    · rw [ht2']; simp [D8mem]
    · rw [httτ]; simp [D8mem]
    · simp [D8mem]
    · rw [← mul_assoc]; simp [D8mem]
    · rw [httω]; simp [D8mem]
    · rw [httωτ]; simp [D8mem]
  have hωQ : ∀ y, D8mem t τ ω y → D8mem t τ ω (ω * y) := by
    intro y hy
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · simp [D8mem]
    · simp [D8mem]
    · rw [hωt]; simp [D8mem]
    · rw [hωtτ]; simp [D8mem]
    · rw [hω2']; simp [D8mem]
    · rw [hωωτ]; simp [D8mem]
    · rw [hωtω]; simp [D8mem]
    · rw [hωtωτ]; simp [D8mem]
  change x ∈ closure ({t, ω} : Set G) ↔ D8mem t τ ω x
  constructor
  · intro hx
    refine Subgroup.closure_induction_left (p := fun x _ => D8mem t τ ω x) ?_ ?_ ?_ hx
    · exact Or.inl rfl
    · intro a ha y hy hyQ
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
      rcases ha with rfl | rfl
      · exact htQ y hyQ
      · exact hωQ y hyQ
    · intro a ha y hy hyQ
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
      rcases ha with rfl | rfl
      · rw [ht_inv]; exact htQ y hyQ
      · rw [hω_inv]; exact hωQ y hyQ
  · rintro (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
    · exact (closure ({t, ω} : Set G)).one_mem
    · exact tau_mem_closure ht2 hω2 hτ2 htτ hω
    · exact Subgroup.subset_closure (by simp)
    · exact (closure ({t, ω} : Set G)).mul_mem (Subgroup.subset_closure (by simp))
        (tau_mem_closure ht2 hω2 hτ2 htτ hω)
    · exact Subgroup.subset_closure (by simp)
    · exact (closure ({t, ω} : Set G)).mul_mem (Subgroup.subset_closure (by simp))
        (tau_mem_closure ht2 hω2 hτ2 htτ hω)
    · exact (closure ({t, ω} : Set G)).mul_mem (Subgroup.subset_closure (by simp))
        (Subgroup.subset_closure (by simp))
    · exact (closure ({t, ω} : Set G)).mul_mem
        ((closure ({t, ω} : Set G)).mul_mem (Subgroup.subset_closure (by simp))
          (Subgroup.subset_closure (by simp)))
        (tau_mem_closure ht2 hω2 hτ2 htτ hω)

theorem invol_closure_t_om (ht2 : t ^ 2 = 1) (hω2 : ω ^ 2 = 1) (hτ2 : τ ^ 2 = 1) (hτ1 : τ ≠ 1)
    (htτ : t * τ = τ * t) (hω : ω * t * ω⁻¹ = t * τ) {c : G}
    (hc : c ∈ closure ({t, ω} : Set G)) (hc2 : c ^ 2 = 1) (hc1 : c ≠ 1) :
    c = τ ∨ c = t ∨ c = t * τ ∨ c = ω ∨ c = ω * τ := by
  have ht2' : t * t = 1 := mul_self_eq_one_of_sq ht2
  have hτ2' : τ * τ = 1 := mul_self_eq_one_of_sq hτ2
  have hω_inv : ω⁻¹ = ω := inv_eq_self_of_sq hω2
  have hω' : ω * t * ω = t * τ := by simpa only [hω_inv] using hω
  have hωτ : ω * τ = τ * ω := om_tau_comm ht2 hω2 hτ2 htτ hω
  have hτeq : τ = t * ω * t * ω := by
    calc τ = t * (t * τ) := by rw [← mul_assoc, ht2', one_mul]
      _ = t * (ω * t * ω) := by rw [hω'.symm]
      _ = t * ω * t * ω := by group
  have hsq : (t * ω) ^ 2 = τ := by
    rw [pow_two]
    calc (t * ω) * (t * ω) = t * ω * t * ω := by simp only [mul_assoc]
      _ = τ := hτeq.symm
  have hcomm : Commute (t * ω) τ := Commute.mul_left htτ hωτ
  have hsq2 : (t * ω * τ) ^ 2 = τ := by
    rw [Commute.mul_pow hcomm, hsq, hτ2, mul_one]
  have hlist := (mem_closure_t_om_iff ht2 hω2 hτ2 htτ hω c).mp hc
  rcases hlist with h | h | h | h | h | h | h | h
  · exact absurd h hc1
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr h)))
  · exfalso
    rw [h] at hc2
    rw [hsq] at hc2
    exact hτ1 hc2
  · exfalso
    rw [h] at hc2
    rw [hsq2] at hc2
    exact hτ1 hc2

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
