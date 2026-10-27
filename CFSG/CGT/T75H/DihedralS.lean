module

public import CFSG.GroupTheory.ABGDGroups.LinearCentralizers
public import CFSG.CGT.T75H.Split
public import CFSG.CGT.T75H.SylowData

public section

namespace CFSG.CGT.T75H

open CFSG.CGT.Timmesfeld75 CFSG.Open
open scoped commutatorElement

variable {G : Type} [Group G] {T T₁ : Subgroup G}

namespace D8Data

variable {ℓ a b y : G} (D : D8Data T T₁ ℓ a b y)

include D

theorem sq_ℓb : (ℓ * b) * (ℓ * b) = a := by
  calc (ℓ * b) * (ℓ * b) = ℓ * (b * ℓ * b) := by group
    _ = ℓ * (ℓ * a) := by rw [D.conj_ℓ_b]
    _ = (ℓ * ℓ) * a := by group
    _ = a := by rw [D.ℓℓ, one_mul]

theorem orderOf_ℓb : orderOf (ℓ * b) = 4 := by
  have h2 : (ℓ * b) ^ 2 = a := by rw [sq]; exact D.sq_ℓb
  have h4 : (ℓ * b) ^ 4 = 1 := by
    calc (ℓ * b) ^ 4 = ((ℓ * b) ^ 2) ^ 2 := by group
      _ = a * a := by rw [h2, sq]
      _ = 1 := D.aa
  have := orderOf_eq_prime_pow (p := 2) (n := 1) (x := ℓ * b)
    (by rw [pow_one]; rw [h2]; exact D.ha1) (by norm_num; exact h4)
  simpa using this

theorem zpow_ℓb_invol {j : ℤ} (h : ((ℓ * b) ^ j) * ((ℓ * b) ^ j) = 1) :
    (ℓ * b) ^ j = 1 ∨ (ℓ * b) ^ j = a := by
  have h1 : (ℓ * b) ^ (2 * j) = 1 := by rw [two_mul, zpow_add]; exact h
  have h2 : ((orderOf (ℓ * b) : ℕ) : ℤ) ∣ 2 * j := orderOf_dvd_iff_zpow_eq_one.2 h1
  rw [D.orderOf_ℓb] at h2
  obtain ⟨i, rfl⟩ : (2 : ℤ) ∣ j := by omega
  have h3 : (ℓ * b) ^ (2 * i) = a ^ i := by
    rw [zpow_mul, zpow_two, D.sq_ℓb]
  rw [h3]
  rcases Int.even_or_odd' i with ⟨m, rfl | rfl⟩
  · left
    rw [zpow_mul, zpow_two, D.aa, one_zpow]
  · right
    rw [zpow_add_one, zpow_mul, zpow_two, D.aa, one_zpow, one_mul]

theorem zpowers_sup_eq : Subgroup.zpowers (ℓ * b) ⊔ Subgroup.zpowers b = sStar T T₁ := by
  apply le_antisymm
  · exact sup_le (Subgroup.zpowers_le.2 ((sStar T T₁).mul_mem (normIn_le_sStar D.hℓ)
      (le_sStar_left D.hb))) (Subgroup.zpowers_le.2 (le_sStar_left D.hb))
  · have hg : ℓ * b ∈ Subgroup.zpowers (ℓ * b) ⊔ Subgroup.zpowers b :=
      Subgroup.mem_sup_left (Subgroup.mem_zpowers _)
    have hb : b ∈ Subgroup.zpowers (ℓ * b) ⊔ Subgroup.zpowers b :=
      Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
    have ha : a ∈ Subgroup.zpowers (ℓ * b) ⊔ Subgroup.zpowers b := by
      rw [← D.sq_ℓb]
      exact Subgroup.mul_mem _ hg hg
    refine sup_le (fun t ht => ?_) (fun t ht => ?_)
    · rcases D.hT t ht with rfl | rfl | rfl | rfl
      · exact Subgroup.one_mem _
      · exact ha
      · exact hb
      · exact Subgroup.mul_mem _ hb ha
    · rcases D.hL₁ t ht with h | h
      · rw [h]; exact Subgroup.one_mem _
      · have : t = ℓ * b * b := by rw [h, mul_assoc, D.bb, mul_one]
        rw [this]
        exact Subgroup.mul_mem _ hg hb

end D8Data

theorem sylow_eq_sStar_of_Cbar_bot {ℓ a b y : G} (D : D8Data T T₁ ℓ a b y) {S : Sylow 2 G}
    (hS : SylowData T T₁ S) (hC : Cbar T T₁ S = ⊥) : (S : Subgroup G) = sStar T T₁ := by
  apply le_antisymm
  · intro s hs
    obtain ⟨d, hd, c, hc, rfl⟩ := D.exists_split hS.norm hS.le hS.sStar_norm s hs
    rw [hC, Subgroup.mem_bot] at hc
    rw [hc, mul_one]
    exact hd
  · exact hS.le

theorem sylow_equiv_dihedral [Finite G] {ℓ a b y : G} (D : D8Data T T₁ ℓ a b y)
    {S : Sylow 2 G} (hS : SylowData T T₁ S) (hC : Cbar T T₁ S = ⊥) :
    Nonempty ((S : Subgroup G) ≃* DihedralGroup 4) := by
  have hSS : (S : Subgroup G) = sStar T T₁ := sylow_eq_sStar_of_Cbar_bot D hS hC
  have hcyc : IsCyclic (Subgroup.zpowers (ℓ * b)) := inferInstance
  have hsT : b ∉ Subgroup.zpowers (ℓ * b) := by
    intro h
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1 h
    have hℓg : (ℓ * b) ^ (1 + j) = ℓ := by
      rw [zpow_add, zpow_one, hj, mul_assoc, D.bb, mul_one]
    have hℓmem : (ℓ * b) ^ (1 + j) * (ℓ * b) ^ (1 + j) = 1 := by rw [hℓg]; exact D.ℓℓ
    rcases D.zpow_ℓb_invol hℓmem with h1 | h1
    · exact D.hℓ1 (by rw [← hℓg, h1])
    · apply D.ℓ_not_mem
      rw [← hℓg, h1]
      exact D.haT
  have hinv : ∀ x ∈ Subgroup.zpowers (ℓ * b), b * x * b⁻¹ = x⁻¹ := by
    intro x hx
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
    have h1 : b * (ℓ * b) * b⁻¹ = (ℓ * b)⁻¹ := by
      calc b * (ℓ * b) * b⁻¹ = b * ℓ := by group
        _ = b⁻¹ * ℓ⁻¹ := by rw [D.inv_b, D.inv_ℓ]
        _ = (ℓ * b)⁻¹ := by rw [mul_inv_rev]
    rw [← conj_zpow, h1, inv_zpow]
  obtain ⟨e⟩ := CFSG.ABGDGroups.nonempty_mulEquiv_dihedral_of_reflected
    (T := Subgroup.zpowers (ℓ * b)) (s := b) hsT D.bb hinv
  have hcard : Nat.card (Subgroup.zpowers (ℓ * b)) = 4 := by
    rw [Nat.card_zpowers, D.orderOf_ℓb]
  rw [hcard] at e
  exact ⟨(MulEquiv.subgroupCongr (hSS.trans D.zpowers_sup_eq.symm)).trans e⟩

end CFSG.CGT.T75H
