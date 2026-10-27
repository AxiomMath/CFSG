module

public import CFSG.HardMathSupport.Solomon.Coordinator.BGLSL2Basic

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.BGL

open scoped commutatorElement

theorem comm_mul_central {G : Type*} [Group G] {b b' z z' : G} (hz : z ∈ Subgroup.center G)
    (hz' : z' ∈ Subgroup.center G) : ⁅b * z, b' * z'⁆ = ⁅b, b'⁆ := by
  have h1 : ∀ y : G, ⁅b * z, y⁆ = ⁅b, y⁆ := fun y => by
    have hzy : z * y = y * z := (Subgroup.mem_center_iff.1 hz y).symm
    simp only [commutatorElement_def, mul_inv_rev]
    calc b * z * y * (z⁻¹ * b⁻¹) * y⁻¹ = b * (z * y) * z⁻¹ * b⁻¹ * y⁻¹ := by group
      _ = b * (y * z) * z⁻¹ * b⁻¹ * y⁻¹ := by rw [hzy]
      _ = b * y * b⁻¹ * y⁻¹ := by group
  have hzb : z' * b⁻¹ = b⁻¹ * z' := (Subgroup.mem_center_iff.1 hz' b⁻¹).symm
  rw [h1]
  simp only [commutatorElement_def, mul_inv_rev]
  calc b * (b' * z') * b⁻¹ * (z'⁻¹ * b'⁻¹) = b * b' * (z' * b⁻¹) * z'⁻¹ * b'⁻¹ := by group
    _ = b * b' * (b⁻¹ * z') * z'⁻¹ * b'⁻¹ := by rw [hzb]
    _ = b * b' * b⁻¹ * b'⁻¹ := by group

theorem eq_top_of_sup_center {G : Type*} [Group G] (hG : commutator G = ⊤) {M : Subgroup G}
    (h : M ⊔ Subgroup.center G = ⊤) : M = ⊤ := by
  rw [eq_top_iff, ← hG, commutator_def, Subgroup.commutator_le]
  intro x _ y _
  obtain ⟨m, hm, z, hz, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp (h ▸ Subgroup.mem_top x)
  obtain ⟨m', hm', z', hz', rfl⟩ := Subgroup.mem_sup_of_normal_right.mp (h ▸ Subgroup.mem_top y)
  rw [comm_mul_central hz hz']
  show m * m' * m⁻¹ * m'⁻¹ ∈ M
  exact M.mul_mem (M.mul_mem (M.mul_mem hm hm') (M.inv_mem hm)) (M.inv_mem hm')

variable {E : Type} [Field E] [Finite E]

theorem kappa_mem_of_sq_mem {p : ℕ} [hp : Fact p.Prime] [CharP E p] (K k : Subfield E) {κ : E}
    (hκ0 : κ ≠ 0) (h : ∀ m ∈ k, (2 + κ * m) ^ 2 ∈ K) : κ ∈ K ∧ k ≤ K := by
  by_cases h2 : (2 : E) = 0
  · have hp2 : p = 2 := by
      have : p ∣ 2 := (CharP.cast_eq_zero_iff E p 2).1 (by exact_mod_cast h2)
      exact (Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).1 this
    subst hp2
    have : Fintype E := Fintype.ofFinite E
    obtain ⟨n, -, hn⟩ := FiniteField.card E 2
    obtain ⟨n', hn'⟩ : ∃ n' : ℕ, (n : ℕ) = n' + 1 := ⟨(n : ℕ) - 1, by have := n.pos; omega⟩
    rw [hn'] at hn
    have hsq : ∀ x : E, x ^ 2 ∈ K → x ∈ K := by
      intro x hx
      have h1 : x = (x ^ 2) ^ (2 ^ n') := by
        rw [← pow_mul, ← pow_succ']
        have := FiniteField.pow_card x
        rw [hn] at this
        exact this.symm
      rw [h1]; exact K.pow_mem hx _
    have hf : ∀ m ∈ k, (κ * m) ^ 2 ∈ K := fun m hm => by
      have := h m hm
      rwa [h2, zero_add] at this
    have hκ2 : κ ^ 2 ∈ K := by
      have := hf 1 k.one_mem; simpa using this
    have hκK : κ ∈ K := hsq κ hκ2
    refine ⟨hκK, fun m hm => hsq m ?_⟩
    have h3 : (κ * m) ^ 2 = κ ^ 2 * m ^ 2 := mul_pow _ _ _
    have h4 : m ^ 2 = (κ * m) ^ 2 * (κ ^ 2)⁻¹ := by
      rw [h3]; field_simp
    rw [h4]
    exact K.mul_mem (hf m hm) (K.inv_mem hκ2)
  · have h8 : (8 : E) ≠ 0 := by
      have : (8 : E) = 2 ^ 3 := by norm_num
      rw [this]; exact pow_ne_zero 3 h2
    have hd : ∀ m ∈ k, κ * m ∈ K := by
      intro m hm
      have e1 := h m hm
      have e2 := h (-m) (k.neg_mem hm)
      have : κ * m = ((2 + κ * m) ^ 2 - (2 + κ * (-m)) ^ 2) / 8 := by
        field_simp; ring
      rw [this]
      exact K.div_mem (K.sub_mem e1 e2) (by simp)
    have hκK : κ ∈ K := by simpa using hd 1 k.one_mem
    refine ⟨hκK, fun m hm => ?_⟩
    have : m = (κ * m) / κ := by field_simp
    rw [this]
    exact K.div_mem (hd m hm) hκK

end CFSG.HardMathSupport.Solomon.Coordinator.BGL
