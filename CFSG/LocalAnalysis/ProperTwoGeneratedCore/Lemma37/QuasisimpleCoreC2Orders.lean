module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.QuasisimpleCoreC2Quat

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore

open QuaternionGroup

namespace PartC

variable {G : Type} [Group G] {T Q P₁ : Subgroup G} {e u y : G} {N : ℕ}
  (φ : (P₁ ⊔ Subgroup.zpowers y : Subgroup G) ≃* QuaternionGroup N)

theorem pow_four_eq_one_left (hc : PartC T Q P₁ e u) {q : G} (hq : q ∈ Q) : q ^ 4 = 1 := by
  have h4 : q ^ 4 = (q * q) * (q * q) := by
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, pow_two, pow_two]
  rw [h4]
  rcases quaternion_mul_self hc.quaternion.some hc.mem_left hc.order hq with h | h
  · rw [h, one_mul]
  · rw [h, hc.centralElt_mul_self]

include φ in
theorem pow_eq_one_of_mem_right [Finite G] [NeZero N] (hc : PartC T Q P₁ e u) (hyT : y ∈ T)
    (hy : y ∉ Q ⊔ P₁) (hyy : y * y ∈ P₁) (hP₁ : ¬ IsCyclic P₁) (hN : 8 ∣ N) {p : G}
    (hp : p ∈ P₁) : p ^ N = 1 := by
  have he : e ^ 2 = 1 := by rw [pow_two, hc.centralElt_mul_self]
  rcases hc.mem_sup_zpowers_cases φ hyT hy hyy (Subgroup.mem_sup_left hp) with
    ⟨k, rfl⟩ | ⟨hpp, -⟩
  · obtain ⟨j, rfl⟩ := (hc.quatGen_pow_mem_iff φ hyT hy hyy hP₁ k).mp hp
    rw [← pow_mul, show (j + j) * N = N * 2 * j by ring, pow_mul, pow_mul,
      hc.quatGen_pow φ hyT hy hyy, he, one_pow]
  · obtain ⟨M, rfl⟩ := hN
    rw [show 8 * M = 2 * (2 * (2 * M)) by ring, pow_mul, pow_two, hpp, pow_mul, he, one_pow]

include φ in
theorem pow_eq_one_of_mem_sup [Finite G] [NeZero N] (hc : PartC T Q P₁ e u) (hyT : y ∈ T)
    (hy : y ∉ Q ⊔ P₁) (hyy : y * y ∈ P₁) (hP₁ : ¬ IsCyclic P₁) (hN : 8 ∣ N) {t : G}
    (ht : t ∈ Q ⊔ P₁) : t ^ N = 1 := by
  obtain ⟨q, hq, p, hp, rfl⟩ := hc.mem_sup_iff.mp ht
  rw [Commute.mul_pow (hc.commute q hq p hp) N,
    hc.pow_eq_one_of_mem_right φ hyT hy hyy hP₁ hN hp, mul_one]
  obtain ⟨M, rfl⟩ := hN
  rw [show 8 * M = 4 * (2 * M) by ring, pow_mul, hc.pow_four_eq_one_left hq, one_pow]

include φ in
theorem mul_self_or_pow_of_not_mem_right [Finite G] [NeZero N] (hc : PartC T Q P₁ e u)
    (hyT : y ∈ T) (hy : y ∉ Q ⊔ P₁) (hyy : y * y ∈ P₁) (hP₁ : ¬ IsCyclic P₁) {w : G}
    (hw : w ∈ P₁ ⊔ Subgroup.zpowers y) (hw₁ : w ∉ P₁) : w * w = e ∨ w ^ N = e := by
  rcases hc.mem_sup_zpowers_cases φ hyT hy hyy hw with ⟨k, rfl⟩ | ⟨hww, -⟩
  · right
    have hk : ¬ Even k := fun h => hw₁ ((hc.quatGen_pow_mem_iff φ hyT hy hyy hP₁ k).mpr h)
    obtain ⟨j, rfl⟩ := Nat.not_even_iff_odd.mp hk
    rw [← pow_mul, show (2 * j + 1) * N = N * (2 * j + 1) by ring, pow_mul,
      hc.quatGen_pow φ hyT hy hyy, pow_succ, pow_mul, pow_two, hc.centralElt_mul_self, one_pow,
      one_mul]
  · exact Or.inl hww

include φ in
theorem pow_or_mul_self_of_not_mem [Finite G] [NeZero N] (hc : PartC T Q P₁ e u)
    (hyT : y ∈ T) (hy : y ∉ Q ⊔ P₁) (hyy : y * y ∈ P₁) (hP₁ : ¬ IsCyclic P₁) (hN : 8 ∣ N)
    {v : G} (hfix : ∀ w ∈ Q, (y * w * y⁻¹ = w ∨ y * w * y⁻¹ = w * e) →
      w = 1 ∨ w = e ∨ w = v ∨ w = v * e) {t : G} (htT : t ∈ T) (ht : t ∉ Q ⊔ P₁) :
    t ^ N = e ∨ t * t = e ∨ t * t = v ∨ t * t = v * e := by
  obtain ⟨q, hq, w, hw, rfl⟩ := hc.exists_mul_eq_of_mem hyT hy htT
  have hw₁ : w ∉ P₁ := fun h => ht (mul_mem_sup hq h)
  have hs := hc.mul_conj_mem hyT hyy hfix hq
  have hsQ : q * (y * q * y⁻¹) ∈ Q := Q.mul_mem hq (hc.normal_left y hyT q hq)
  have hsq : q * w * (q * w) = q * (y * q * y⁻¹) * (w * w) := by
    rw [mul_mul_self_eq, hc.conj_eq_conj_of_not_mem hyT hyy hw hw₁ hq]
  rcases hc.mul_self_or_pow_of_not_mem_right φ hyT hy hyy hP₁ hw hw₁ with hww | hwN
  · right
    rw [hsq, hww]
    rcases hs with h | h | h | h <;> rw [h]
    · exact Or.inl (one_mul e)
    · exfalso
      have ht1 : q * w ≠ 1 := fun h1 => ht (h1 ▸ (Q ⊔ P₁).one_mem)
      have h2 : orderOf (q * w) = 2 := orderOf_eq_prime (by
        rw [pow_two, hsq, hww, h, hc.centralElt_mul_self]) ht1
      exact ht (hc.involution_mem _ htT h2)
    · exact Or.inr (Or.inr rfl)
    · exact Or.inr (Or.inl (hc.mul_centralElt_mul_centralElt v))
  · left
    obtain ⟨M, rfl⟩ := hN
    have hcomm : Commute (q * (y * q * y⁻¹)) (w * w) :=
      hc.commute _ hsQ _ (hc.mul_self_mem_right hyT hyy hw)
    rw [show 8 * M = 2 * (4 * M) by ring, pow_mul, pow_two, hsq, hcomm.mul_pow, pow_mul,
      hc.pow_four_eq_one_left hsQ, one_pow, one_mul, ← pow_two, ← pow_mul,
      show 2 * (4 * M) = 8 * M by ring, hwN]

end PartC

end CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore
