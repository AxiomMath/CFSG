module

public import CFSG.CGT.Timmesfeld75.Sec3EightTransv
public import CFSG.CGT.Timmesfeld75.Sec4OneCommon

public section

namespace CFSG.CGT.Timmesfeld75

open CFSG.Open
open scoped commutatorElement

variable {G : Type} [Group G] {T T₁ S : Subgroup G} {a b : G}

structure Sec38Hyp (T T₁ S : Subgroup G) (a b : G) : Prop where
  sec : Sec3 T T₁
  two : IsPGroup 2 S
  hL₁S : normIn T₁ T ≤ S
  haS : a ∈ S
  ha : IsLElt T T₁ a
  hb : b ∈ normIn T₁ T
  hord : orderOf (a * b) = 4

namespace Sec38Hyp

variable (h : Sec38Hyp T T₁ S a b)

include h

theorem aa : a * a = 1 := h.ha.transv.2.1

theorem bb : b * b = 1 := elemAbelian_mul_self h.sec.cfg.wc₁.1 (mem_normIn.1 h.hb).1

theorem hbT₁ : b ∈ T₁ := (mem_normIn.1 h.hb).1

theorem ne_one_b : b ≠ 1 := by
  intro hb1
  have h4 : orderOf (a * b) = 4 := h.hord
  rw [hb1, mul_one] at h4
  have h2 : orderOf a ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact h.aa)
  rw [h4] at h2
  omega

theorem hbL : IsLElt T T₁ b := h.sec.isLElt_of_mem_normIn h.hb h.ne_one_b

theorem z_sq : (a * b * (a * b)) * (a * b * (a * b)) = 1 := by
  have h4 : (a * b) ^ 4 = 1 := by
    rw [← h.hord]
    exact pow_orderOf_eq_one _
  calc (a * b * (a * b)) * (a * b * (a * b)) = (a * b) ^ 4 := by
        rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add, pow_two]
    _ = 1 := h4

theorem z_ne_one : a * b * (a * b) ≠ 1 := by
  have h2 : (a * b) ^ 2 ≠ 1 :=
    pow_ne_one_of_lt_orderOf (by norm_num) (by rw [h.hord]; norm_num)
  rwa [pow_two] at h2

theorem z_eq : a * b * (a * b) = b * a * (b * a) := by
  have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_right h.aa
  have hbi : b⁻¹ = b := inv_eq_of_mul_eq_one_right h.bb
  calc a * b * (a * b) = (a * b * (a * b))⁻¹ := (inv_eq_of_mul_eq_one_right h.z_sq).symm
    _ = b * a * (b * a) := by simp [mul_inv_rev, hai, hbi, mul_assoc]

theorem z_comm_b : (a * b * (a * b)) * b = b * (a * b * (a * b)) := by
  have e1 : a * b * (a * b) * b = b * a * b * a * b := by
    calc a * b * (a * b) * b = b * a * (b * a) * b := by rw [h.z_eq]
      _ = b * a * b * a * b := by group
  have e2 : b * (a * b * (a * b)) = b * a * b * a * b := by group
  exact e1.trans e2.symm

theorem z_comm_T {t : G} (ht : t ∈ T) : (a * b * (a * b)) * t = t * (a * b * (a * b)) :=
  IsTransv.mul_mul_comm (isElemAbelian_of_le h.sec.cfg.wc.1 (normIn_le T T₁)) h.ha.transv
    h.hbL.transv ht

theorem z_mem_normalizer_T : a * b * (a * b) ∈ Subgroup.normalizer (T : Set G) := by
  have hz : a * b * (a * b) ∈ Subgroup.centralizer (T : Set G) :=
    Subgroup.mem_centralizer_iff.2 fun t ht => (h.z_comm_T ht).symm
  exact Subgroup.centralizer_le_normalizer (T : Set G) hz

theorem z_mem_normalizer_T₁ : a * b * (a * b) ∈ Subgroup.normalizer (T₁ : Set G) :=
  h.sec.cfg.wc₁.centralizer_le_normalizer h.hbT₁ h.ne_one_b
    (Subgroup.mem_centralizer_singleton_iff.2 h.z_comm_b)

theorem conj_a_ne [Finite G] : conjSubgroup a T₁ ≠ T₁ := by
  intro heq
  have haN : a ∈ Subgroup.normalizer (T₁ : Set G) := mem_normalizer_of_conjSubgroup_eq heq
  have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_right h.aa
  have hbi : b⁻¹ = b := inv_eq_of_mul_eq_one_right h.bb
  have hzT₁ : a * b * (a * b) ∈ T₁ := by
    have h1 : a * b * a⁻¹ ∈ T₁ := conj_mem_of_mem_normalizer haN h.hbT₁
    have h2 : a * b * a⁻¹ * b⁻¹ ∈ T₁ := T₁.mul_mem h1 (T₁.inv_mem h.hbT₁)
    have e : a * b * (a * b) = a * b * a⁻¹ * b⁻¹ := by rw [hai, hbi]; group
    rwa [e]
  exact h.sec.not_centralizes_of_mem_normIn (b := a * b * (a * b))
    (mem_normIn.2 ⟨hzT₁, h.z_mem_normalizer_T⟩) h.z_ne_one fun t ht => h.z_comm_T ht

theorem b_mul_a : b * a = a * (a * b * (a * b)) * b := by
  calc b * a = (a * a) * b * a * (b * b) := by rw [h.aa, h.bb]; group
    _ = a * (a * b * (a * b)) * b := by group

theorem b_mem_normIn_conj : b ∈ normIn T₁ (conjSubgroup a T₁) := by
  refine mem_normIn.2 ⟨h.hbT₁, mem_normalizer_iff_conjSubgroup_eq.2 ?_⟩
  have hb : conjSubgroup b T₁ = T₁ :=
    mem_normalizer_iff_conjSubgroup_eq.1 (Subgroup.le_normalizer h.hbT₁)
  have hz : conjSubgroup (a * b * (a * b)) T₁ = T₁ :=
    mem_normalizer_iff_conjSubgroup_eq.1 h.z_mem_normalizer_T₁
  rw [conjSubgroup_conjSubgroup, h.b_mul_a, mul_assoc, ← conjSubgroup_conjSubgroup,
    ← conjSubgroup_conjSubgroup, hb, hz]

theorem normIn_conj_ne_bot : normIn T₁ (conjSubgroup a T₁) ≠ ⊥ := fun h0 => by
  have := h.b_mem_normIn_conj
  rw [h0, Subgroup.mem_bot] at this
  exact h.ne_one_b this

end Sec38Hyp

end CFSG.CGT.Timmesfeld75
