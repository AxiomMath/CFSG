module

public import CFSG.CGT.T75O.Assemble

public section

namespace CFSG.CGT.T75O

open CFSG.CGT.Timmesfeld75 CFSG.Open
open scoped commutatorElement

variable {G : Type} [Group G] {T T₁ : Subgroup G}

namespace Cfg56

variable (c : Cfg56 T T₁)
include c

theorem mem_secA_of_conj_mem {a x : G} (ha : a ∈ secA T T₁) (ha1 : a ≠ 1)
    (hx : x * a * x⁻¹ ∈ T) : x * a * x⁻¹ ∈ secA T T₁ := by
  have hxN : x ∈ Subgroup.normalizer (T : Set G) := by
    rw [mem_normalizer_iff_conjSubgroup_eq]
    by_contra hne
    have hbot := c.hy.pair.wc.inf_conj_eq_bot hne
    have h1 : x * a * x⁻¹ ∈ conjSubgroup x T := conj_mem_conjSubgroup x (secA_le_left ha)
    have h2 : x * a * x⁻¹ ∈ T ⊓ conjSubgroup x T := ⟨hx, h1⟩
    rw [hbot, Subgroup.mem_bot] at h2
    exact conj_ne_one' rfl ha1 h2
  have h3 := conj_mem_conjSubgroup x ha
  rwa [conjSubgroup_secA hxN] at h3

theorem false_of_le_secA (hTA : T ≤ secA T T₁) : False := by
  have := c.hy.finite
  obtain ⟨g, hg⟩ := c.exists_isUIdx
  obtain ⟨f, hf, -, hcard⟩ := c.card_secA_eq hg
  have hTL : T ≤ normIn T T₁ := hTA.trans secA_le_normIn
  have hle : Nat.card T ≤ Nat.card (normIn T T₁) := Subgroup.card_le_of_le hTL
  have hpos : 0 < Nat.card (normIn T T₁) := Nat.card_pos
  have h2 : 2 ≤ 2 ^ f := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) (Nat.one_le_iff_ne_zero.2 hf)
  rw [hcard] at hle
  nlinarith

theorem false_of_isConj_involutions
    (hcl : ∀ x y : G, x * x = 1 → x ≠ 1 → y * y = 1 → y ≠ 1 → IsConj x y) : False := by
  obtain ⟨a, ha, ha1⟩ := c.exists_mem_secA_ne_one
  apply c.false_of_le_secA
  intro t ht
  by_cases ht1 : t = 1
  · rw [ht1]
    exact one_mem _
  · obtain ⟨x, hx⟩ := isConj_iff.1
      (hcl a t (c.mul_self_T (secA_le_left ha)) ha1 (c.mul_self_T ht) ht1)
    rw [← hx]
    exact c.mem_secA_of_conj_mem ha ha1 (by rw [hx]; exact ht)

theorem exists_noncomm : ∃ i j : G, IsUIdx T T₁ i ∧ IsUIdx T T₁ j ∧
    ∃ a ∈ conjSubgroup i (secA T T₁), ∃ x ∈ conjSubgroup j (secA T T₁), a * x ≠ x * a := by
  by_contra hcon
  apply c.hnab
  refine secR₁_comm_of_gen_comm fun i j hi hj a ha x hx => ?_
  by_contra hne
  exact hcon ⟨i, j, hi, hj, a, ha, x, hx, hne⟩

theorem isConj_invol_of_mem_secA_conj {t : G} (ht : t ∈ secA T T₁) (ht1 : t ≠ 1) {k y : G}
    (hy : y ∈ conjSubgroup k (secA T T₁)) (hy1 : y ≠ 1) : IsConj t y ∧ y * y = 1 := by
  have hy₀ : k⁻¹ * y * k ∈ secA T T₁ := mem_conjSubgroup.1 hy
  have hy₀1 : k⁻¹ * y * k ≠ 1 := fun h => hy1 (by
    have : y = k * (k⁻¹ * y * k) * k⁻¹ := by group
    rw [this, h]
    group)
  have hconj : IsConj (k⁻¹ * y * k) y := isConj_iff.2 ⟨k, by group⟩
  refine ⟨(c.isConj_of_mem_secA ht ht1 hy₀ hy₀1).trans hconj, ?_⟩
  have h2 := c.mul_self_T (secA_le_left hy₀)
  calc y * y = k * ((k⁻¹ * y * k) * (k⁻¹ * y * k)) * k⁻¹ := by group
    _ = 1 := by rw [h2]; group

theorem exists_orderOf_eq_four {t : G} (ht : t ∈ secA T T₁) (ht1 : t ≠ 1) :
    ∃ d e : G, IsConj t d ∧ IsConj t e ∧ orderOf (d * e) = 4 := by
  obtain ⟨i, j, hi, hj, a, ha, x, hx, hax⟩ := c.exists_noncomm
  have ha1 : a ≠ 1 := fun h => hax (by rw [h]; simp)
  have hx1 : x ≠ 1 := fun h => hax (by rw [h]; simp)
  obtain ⟨hta, haa⟩ := c.isConj_invol_of_mem_secA_conj ht ht1 ha ha1
  obtain ⟨htx, hxx⟩ := c.isConj_invol_of_mem_secA_conj ht ht1 hx hx1
  refine ⟨a, x, hta, htx, ?_⟩
  have hcomm : ⁅a, x⁆ = (a * x) ^ 2 := by
    rw [commutatorElement_def, inv_eq_of_mul_eq_one_right haa, inv_eq_of_mul_eq_one_right hxx,
      sq]
    simp [mul_assoc]
  have hcA : ⁅a, x⁆ ∈ secA T T₁ :=
    c.hR' a (secA_conj_le_secR₁ hi ha) x (secA_conj_le_secR₁ hj hx)
  have hc2 : ⁅a, x⁆ * ⁅a, x⁆ = 1 := c.mul_self_T (secA_le_left hcA)
  have hne2 : ¬ (a * x) ^ 2 ^ 1 = 1 := by
    intro h
    rw [pow_one, ← hcomm, commutatorElement_eq_one_iff_mul_comm] at h
    exact hax h
  have hfin4 : (a * x) ^ 2 ^ (1 + 1) = 1 := by
    have : (a * x) ^ 2 ^ (1 + 1) = ((a * x) ^ 2) ^ 2 := by
      rw [← pow_mul]
      norm_num
    rw [this, ← hcomm, sq]
    exact hc2
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h4 := orderOf_eq_prime_pow hne2 hfin4
  simpa using h4

end Cfg56

end CFSG.CGT.T75O
