module

public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms

public section

namespace CFSG.QuasithinUnique.Setup.X1.J4Out

open CFSG.ComponentClassification
open scoped Pointwise

theorem odd_card_outer_of_sylow (G : Type*) [Group G] [Finite G] (S : Sylow 2 G)
    (h : ∀ α : MulAut G, IsPGroup 2 (Subgroup.zpowers α) →
      (∀ x ∈ (S : Subgroup G), α x ∈ (S : Subgroup G)) → α ∈ OuterAutomorphisms.inner G) :
    Odd (Nat.card (OuterAutomorphisms.Outer G)) := by
  by_contra hodd
  have heven : 2 ∣ Nat.card (OuterAutomorphisms.Outer G) := by
    rw [Nat.not_odd_iff_even, even_iff_two_dvd] at hodd
    exact hodd
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (MulAut G) :=
    Finite.of_injective (fun α : MulAut G => (α : G → G)) (fun a b hab => MulEquiv.ext (congrFun hab))
  obtain ⟨q, hq⟩ := exists_prime_orderOf_dvd_card' 2 heven
  obtain ⟨α₀, rfl⟩ := QuotientGroup.mk_surjective q
  have hpos : 0 < orderOf α₀ := orderOf_pos α₀
  obtain ⟨k, m, hm, hkm⟩ := Nat.exists_eq_two_pow_mul_odd hpos.ne'
  have hm0 : m ≠ 0 := hm.pos.ne'
  set α : MulAut G := α₀ ^ m with hα
  have hordα : orderOf α = 2 ^ k := by
    have hdvd : m ∣ orderOf α₀ := ⟨2 ^ k, by rw [hkm, mul_comm]⟩
    rw [hα, orderOf_pow_of_dvd hm0 hdvd, hkm]
    exact Nat.mul_div_cancel _ hm.pos
  have hmk : (QuotientGroup.mk α : OuterAutomorphisms.Outer G) ≠ 1 := by
    have h1 : (QuotientGroup.mk α : OuterAutomorphisms.Outer G) = QuotientGroup.mk α₀ := by
      have hq2 : (QuotientGroup.mk α₀ : OuterAutomorphisms.Outer G) ^ 2 = 1 := by
        rw [← hq]; exact pow_orderOf_eq_one _
      obtain ⟨j, hj⟩ := hm
      rw [hα, hj]
      show (QuotientGroup.mk (α₀ ^ (2 * j + 1)) : OuterAutomorphisms.Outer G) = _
      rw [QuotientGroup.mk_pow, pow_succ, pow_mul, hq2, one_pow, one_mul]
    rw [h1]
    intro h1'
    rw [h1', orderOf_one] at hq
    omega
  have hΓ : IsPGroup 2 (Subgroup.zpowers α) := by
    apply IsPGroup.of_card (n := k)
    rw [Nat.card_zpowers, hordα]
  obtain ⟨P, hP⟩ : (MulAction.fixedPoints (Subgroup.zpowers α) (Sylow 2 G)).Nonempty :=
    hΓ.nonempty_fixed_point_of_prime_not_dvd_card _ (not_dvd_card_sylow 2 G)
  have hαP : α • P = P := hP ⟨α, Subgroup.mem_zpowers α⟩
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G S P
  set c : MulAut G := MulAut.conj g with hc
  have hSP : ∀ x ∈ (S : Subgroup G), c x ∈ (P : Subgroup G) := by
    intro x hx
    have h2 : (P : Subgroup G) = MulAut.conj g • (S : Subgroup G) := by
      rw [← hg, Sylow.coe_subgroup_smul]
    rw [h2]
    exact Subgroup.smul_mem_pointwise_smul _ _ _ hx
  have hPS : ∀ x ∈ (P : Subgroup G), c⁻¹ x ∈ (S : Subgroup G) := by
    intro x hx
    have h2 : (P : Subgroup G) = MulAut.conj g • (S : Subgroup G) := by
      rw [← hg, Sylow.coe_subgroup_smul]
    rw [h2, Subgroup.mem_smul_pointwise_iff_exists] at hx
    obtain ⟨y, hy, hyx⟩ := hx
    have hxy : c⁻¹ x = y := by
      rw [← hyx]
      show c⁻¹ (c y) = y
      simp
    rw [hxy]
    exact hy
  have hαP' : ∀ x ∈ (P : Subgroup G), α x ∈ (P : Subgroup G) := by
    intro x hx
    have h3 : (↑(α • P) : Subgroup G) = α • (P : Subgroup G) := Sylow.pointwise_smul_def
    rw [hαP] at h3
    rw [h3]
    exact Subgroup.smul_mem_pointwise_smul _ _ _ hx
  set α' : MulAut G := c⁻¹ * α * c with hα'
  have hα'S : ∀ x ∈ (S : Subgroup G), α' x ∈ (S : Subgroup G) := by
    intro x hx
    exact hPS _ (hαP' _ (hSP x hx))
  have hα'ord : orderOf α' = 2 ^ k := by
    rw [← hordα]
    refine (SemiconjBy.orderOf_eq c⁻¹ (x := α) (y := α') ?_).symm
    show c⁻¹ * α = α' * c⁻¹
    rw [hα']
    group
  have hΓ' : IsPGroup 2 (Subgroup.zpowers α') := by
    apply IsPGroup.of_card (n := k)
    rw [Nat.card_zpowers, hα'ord]
  have hin' : α' ∈ OuterAutomorphisms.inner G := h α' hΓ' hα'S
  have hcin : c ∈ OuterAutomorphisms.inner G := ⟨g, rfl⟩
  have hin : α ∈ OuterAutomorphisms.inner G := by
    have : α = c * α' * c⁻¹ := by rw [hα']; group
    rw [this]
    exact (OuterAutomorphisms.inner G).mul_mem ((OuterAutomorphisms.inner G).mul_mem hcin hin') ((OuterAutomorphisms.inner G).inv_mem hcin)
  exact hmk ((QuotientGroup.eq_one_iff α).2 hin)

theorem odd_card_outer_of_mulEquiv {A B : Type*} [Group A] [Group B] (e : A ≃* B)
    (h : Odd (Nat.card (OuterAutomorphisms.Outer B))) :
    Odd (Nat.card (OuterAutomorphisms.Outer A)) := by
  rw [Nat.card_congr (OuterAutomorphisms.equivalence e).toEquiv]
  exact h

end CFSG.QuasithinUnique.Setup.X1.J4Out
