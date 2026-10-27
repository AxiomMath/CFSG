module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.QuasisimpleCoreC2Quat

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore

open QuaternionGroup

namespace PartC

variable {G : Type} [Group G] {T Q P₁ : Subgroup G} {e u y : G} {N : ℕ}
  (φ : (P₁ ⊔ Subgroup.zpowers y : Subgroup G) ≃* QuaternionGroup N)

theorem pow_four_mem_zpowers [NeZero N] (hc : PartC T Q P₁ e u) (hyT : y ∈ T)
    (hy : y ∉ Q ⊔ P₁) (hyy : y * y ∈ P₁) (hN : 4 ∣ N) {t : G} (htT : t ∈ T) :
    t ^ 4 ∈ Subgroup.zpowers (quatGen φ ^ 4) := by
  obtain ⟨q, hq, w, hw, rfl⟩ := hc.exists_mul_eq_of_mem hyT hy htT
  have hwT := hc.sup_zpowers_le hyT hw
  have hsQ : q * (w * q * w⁻¹) ∈ Q := Q.mul_mem hq (hc.normal_left w hwT q hq)
  have hcomm : Commute (q * (w * q * w⁻¹)) (w * w) :=
    hc.commute _ hsQ _ (hc.mul_self_mem_right hyT hyy hw)
  have h4 : (q * w) ^ 4 = (q * (w * q * w⁻¹)) ^ 2 * w ^ 4 := by
    have h1 : (q * w) ^ 4 = (q * w * (q * w)) ^ 2 := by
      rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, pow_two (q * w)]
    have h2 : (w * w) ^ 2 = w ^ 4 := by
      rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, pow_two w]
    rw [h1, mul_mul_self_eq, hcomm.mul_pow, h2]
  have he : e ∈ Subgroup.zpowers (quatGen φ ^ 4) := by
    obtain ⟨K, rfl⟩ := hN
    rw [← hc.quatGen_pow φ hyT hy hyy, pow_mul]
    exact Subgroup.pow_mem _ (Subgroup.mem_zpowers _) _
  rw [h4]
  refine Subgroup.mul_mem _ ?_ ?_
  · rw [pow_two]
    rcases quaternion_mul_self hc.quaternion.some hc.mem_left hc.order hsQ with h | h
    · rw [h]
      exact Subgroup.one_mem _
    · rw [h]
      exact he
  · rcases hc.mem_sup_zpowers_cases φ hyT hy hyy hw with ⟨k, rfl⟩ | ⟨hww, -⟩
    · rw [← pow_mul, mul_comm, pow_mul]
      exact Subgroup.pow_mem _ (Subgroup.mem_zpowers _) _
    · rw [show w ^ 4 = (w * w) * (w * w) by
        rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, pow_two, pow_two], hww, hc.centralElt_mul_self]
      exact Subgroup.one_mem _

include φ in
theorem exists_pow_four_eq_self [Finite G] [NeZero N] (hc : PartC T Q P₁ e u) (hyT : y ∈ T)
    (hy : y ∉ Q ⊔ P₁) (hyy : y * y ∈ P₁) (hN : 8 ∣ N)
    (hnorm : T ≤ Subgroup.normalizer (Subgroup.zpowers u : Set G)) :
    ∃ x ∈ T, x ^ 4 = u := by
  have hcT : quatGen φ ∈ T := hc.sup_zpowers_le hyT (quatGen_mem φ)
  have hN3 : 3 ≤ N := by
    obtain ⟨M, rfl⟩ := hN
    have := NeZero.ne (8 * M)
    omega
  have hcN := hc.quatGen_pow φ hyT hy hyy
  obtain ⟨M, rfl⟩ := hN
  have hsq : quatGen φ ^ (4 * M) * quatGen φ ^ (4 * M) = e := by
    rw [← pow_add, show 4 * M + 4 * M = 8 * M by ring, hcN]
  rcases hc.eq_of_mem_zpowers_quatGen φ hyT hy hyy hN3 hnorm
      (Subgroup.pow_mem _ (Subgroup.mem_zpowers _) _) hsq with h | h
  · exact ⟨quatGen φ ^ M, T.pow_mem hcT M, by rw [← pow_mul, show M * 4 = 4 * M by ring, h]⟩
  · refine ⟨quatGen φ ^ (3 * M), T.pow_mem hcT _, ?_⟩
    rw [← pow_mul, show 3 * M * 4 = 4 * M + 8 * M by ring, pow_add, h, hcN,
      hc.mul_centralElt_mul_centralElt]

include φ in
theorem normalizer_le_normalizer_zpowers_of_quatGen [Finite G] [NeZero N]
    (hc : PartC T Q P₁ e u) (hyT : y ∈ T) (hy : y ∉ Q ⊔ P₁) (hyy : y * y ∈ P₁) (hN : 8 ∣ N)
    (hnorm : T ≤ Subgroup.normalizer (Subgroup.zpowers u : Set G)) :
    Subgroup.normalizer (T : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers u : Set G) := by
  intro g hg
  set S := Subgroup.closure {x : G | ∃ t ∈ T, t ^ 4 = x} with hS
  have hSC : S ≤ Subgroup.zpowers (quatGen φ ^ 4) := by
    rw [Subgroup.closure_le]
    rintro _ ⟨t, ht, rfl⟩
    exact hc.pow_four_mem_zpowers φ hyT hy hyy (dvd_trans ⟨2, rfl⟩ hN) ht
  have : IsCyclic S := Subgroup.isCyclic_of_le hSC
  obtain ⟨w, hwT, hww⟩ := hc.exists_pow_four_eq_self φ hyT hy hyy hN hnorm
  have huS : u ∈ S := Subgroup.subset_closure ⟨w, hwT, hww⟩
  have hgw : g * w * g⁻¹ ∈ T := (Subgroup.mem_normalizer_iff.mp hg w).mp hwT
  have hguS : g * u * g⁻¹ ∈ S :=
    Subgroup.subset_closure ⟨_, hgw, by rw [conj_pow, hww]⟩
  have hord : orderOf (g * u * g⁻¹) = orderOf u := by
    rw [← MulAut.conj_apply, MulEquiv.orderOf_eq]
  have heq : Subgroup.zpowers (⟨u, huS⟩ : S) = Subgroup.zpowers ⟨g * u * g⁻¹, hguS⟩ := by
    rw [IsCyclic.subgroup_eq_iff_card_eq, Nat.card_zpowers, Nat.card_zpowers,
      Subgroup.orderOf_mk, Subgroup.orderOf_mk, hord]
  have hmem : (⟨g * u * g⁻¹, hguS⟩ : S) ∈ Subgroup.zpowers (⟨u, huS⟩ : S) :=
    heq ▸ Subgroup.mem_zpowers _
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
  exact mem_normalizer_zpowers_of_conj_mem ⟨k, by simpa using congrArg Subtype.val hk⟩

end PartC

end CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore
