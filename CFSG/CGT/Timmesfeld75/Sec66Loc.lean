module

public import CFSG.CGT.Timmesfeld75.Sec66Conj

public section

namespace CFSG.CGT.Timmesfeld75

open CFSG.Open

variable {G : Type} [Group G] {T T₁ : Subgroup G} {n m : ℕ}

theorem sec66_yprime {x y : G} (hxx : x * x = 1) (hyy : y * y = 1) (h4 : orderOf (x * y) = 4) :
    (x * y * x⁻¹) * (x * y * x⁻¹) = 1 ∧ y * (x * y * x⁻¹) = (x * y * x⁻¹) * y ∧
      (x * y) ^ 2 = y * (x * y * x⁻¹) := by
  have hxi : x⁻¹ = x := inv_eq_of_mul_eq_one_right hxx
  have hyi : y⁻¹ = y := inv_eq_of_mul_eq_one_right hyy
  have hy'y' : (x * y * x⁻¹) * (x * y * x⁻¹) = 1 := by
    calc (x * y * x⁻¹) * (x * y * x⁻¹) = x * (y * y) * x⁻¹ := by group
      _ = 1 := by rw [hyy]; group
  have hy'i : (x * y * x⁻¹)⁻¹ = x * y * x⁻¹ := inv_eq_of_mul_eq_one_right hy'y'
  have hsq : (x * y) ^ 2 = (x * y * x⁻¹) * y := by
    rw [pow_two, hxi]
    group
  have h44 : ((x * y * x⁻¹) * y) * ((x * y * x⁻¹) * y) = 1 := by
    have h := pow_orderOf_eq_one (x * y)
    rw [h4] at h
    have e : (x * y) ^ 4 = ((x * y) ^ 2) ^ 2 := by rw [← pow_mul]
    rw [e, hsq, pow_two] at h
    exact h
  have h3 : (x * y * x⁻¹) * y * (x * y * x⁻¹) = y := by
    calc (x * y * x⁻¹) * y * (x * y * x⁻¹)
        = (((x * y * x⁻¹) * y) * ((x * y * x⁻¹) * y)) * y⁻¹ := by group
      _ = y := by rw [h44, one_mul, hyi]
  have hcomm : y * (x * y * x⁻¹) = (x * y * x⁻¹) * y := by
    calc y * (x * y * x⁻¹) = ((x * y * x⁻¹) * y * (x * y * x⁻¹)) * (x * y * x⁻¹)⁻¹ := by
          rw [h3, hy'i]
      _ = (x * y * x⁻¹) * y := by group
  exact ⟨hy'y', hcomm, by rw [hsq, ← hcomm]⟩

theorem sec66_x_comm {x y : G} (hxx : x * x = 1) (hyy : y * y = 1) (h4 : orderOf (x * y) = 4) :
    x * (y * x * y⁻¹) = (y * x * y⁻¹) * x := by
  have hxi : x⁻¹ = x := inv_eq_of_mul_eq_one_right hxx
  have hyi : y⁻¹ = y := inv_eq_of_mul_eq_one_right hyy
  have hmm : (y * x * y⁻¹) * (y * x * y⁻¹) = 1 := by
    calc (y * x * y⁻¹) * (y * x * y⁻¹) = y * (x * x) * y⁻¹ := by group
      _ = 1 := by rw [hxx]; group
  have hmi : (y * x * y⁻¹)⁻¹ = y * x * y⁻¹ := inv_eq_of_mul_eq_one_right hmm
  have hsq : (x * y) ^ 2 = x * (y * x * y⁻¹) := by
    rw [pow_two, hyi]
    group
  have h44 : (x * (y * x * y⁻¹)) * (x * (y * x * y⁻¹)) = 1 := by
    have h := pow_orderOf_eq_one (x * y)
    rw [h4] at h
    have e : (x * y) ^ 4 = ((x * y) ^ 2) ^ 2 := by rw [← pow_mul]
    rw [e, hsq, pow_two] at h
    exact h
  have h1 : x * (y * x * y⁻¹) = (x * (y * x * y⁻¹))⁻¹ := (inv_eq_of_mul_eq_one_right h44).symm
  rw [h1, mul_inv_rev, hmi, hxi]

theorem card_normIn_le_of_conj_conj [Finite G] (hc : Sec6Ctx T T₁ n m) {a b : G}
    (hne : conjSubgroup a T ≠ conjSubgroup b T) :
    Nat.card ↥(normIn (conjSubgroup a T) (conjSubgroup b T)) ≤ Nat.card ↥(normIn T T₁) := by
  have hne' : conjSubgroup (a⁻¹ * b) T ≠ T := by
    intro h
    apply hne
    calc conjSubgroup a T = conjSubgroup a (conjSubgroup (a⁻¹ * b) T) := by rw [h]
      _ = conjSubgroup b T := by rw [conjSubgroup_conjSubgroup, mul_inv_cancel_left]
  have e : normIn (conjSubgroup a T) (conjSubgroup b T) =
      conjSubgroup a (normIn T (conjSubgroup (a⁻¹ * b) T)) := by
    rw [← normIn_conj, conjSubgroup_conjSubgroup, mul_inv_cancel_left]
  rw [e, card_conjSubgroup]
  exact hc.hy.pair.maximal (a⁻¹ * b) hne'

theorem comm_of_inf_eq_bot {A B : Subgroup G} (hAB : A ⊓ B = ⊥) {a b : G} (ha : a ∈ A)
    (hb : b ∈ B) (haB : a ∈ Subgroup.normalizer (B : Set G))
    (hbA : b ∈ Subgroup.normalizer (A : Set G)) : a * b = b * a := by
  have h1 : a * b * a⁻¹ * b⁻¹ ∈ B :=
    B.mul_mem (conj_mem_of_mem_normalizer haB hb) (B.inv_mem hb)
  have h2 : a * b * a⁻¹ * b⁻¹ ∈ A := by
    have e : a * b * a⁻¹ * b⁻¹ = a * (b * a⁻¹ * b⁻¹) := by group
    rw [e]
    exact A.mul_mem ha (conj_mem_of_mem_normalizer hbA (A.inv_mem ha))
  have h3 : a * b * a⁻¹ * b⁻¹ ∈ A ⊓ B := ⟨h2, h1⟩
  rw [hAB, Subgroup.mem_bot, mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at h3
  exact h3

theorem Sec6Ctx.card_ne_sixteen_three (hc : Sec6Ctx T T₁ 3 m) : Nat.card T ≠ 16 := by
  intro h
  have hm := hc.one_le_m
  rw [hc.hT] at h
  have h3 : m < 2 := by
    by_contra h3
    push Not at h3
    have h5 : 4 ≤ 2 ^ m := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) h3
    have := Nat.pow_le_pow_left h5 3
    omega
  interval_cases m
  norm_num at h

end CFSG.CGT.Timmesfeld75
