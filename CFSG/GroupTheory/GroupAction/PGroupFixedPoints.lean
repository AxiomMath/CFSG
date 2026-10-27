module

public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.GroupTheory

variable {G : Type*} [Group G]

theorem smul_eq_self_of_isPGroup_of_normal {Ω : Type*} [MulAction G Ω]
    [MulAction.IsPretransitive G Ω] {p : ℕ} [Fact p.Prime] {Q : Subgroup G} [Q.Normal]
    (hQ : IsPGroup p Q) (hp : ¬ p ∣ Nat.card Ω) {q : G} (hq : q ∈ Q) (a : Ω) : q • a = a := by
  obtain ⟨b, hb⟩ := hQ.nonempty_fixed_point_of_prime_not_dvd_card Ω hp
  have hfixb : ∀ r ∈ Q, r • b = b := fun r hr => (MulAction.mem_fixedPoints.mp hb) ⟨r, hr⟩
  obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq G b a
  have hconj : g⁻¹ * q * g ∈ Q := by
    simpa using (inferInstance : Q.Normal).conj_mem q hq g⁻¹
  have hfix : (g⁻¹ * q * g) • b = b := hfixb (g⁻¹ * q * g) hconj
  calc q • (g • b) = (q * g) • b := (mul_smul q g b).symm
    _ = (g * (g⁻¹ * q * g)) • b := by rw [show q * g = g * (g⁻¹ * q * g) by group]
    _ = g • ((g⁻¹ * q * g) • b) := mul_smul g (g⁻¹ * q * g) b
    _ = g • b := by rw [hfix]

theorem exists_orderOf_eq_forall_smul_eq {A Q : Type*} [Group A] [Group Q] [Finite Q]
    [MulDistribMulAction A Q] {p : ℕ} [Fact p.Prime] (hA : IsPGroup p A) (hQ : IsPGroup p Q)
    [Nontrivial Q] : ∃ x : Q, orderOf x = p ∧ ∀ a : A, a • x = x := by
  let F : Subgroup Q := FixedPoints.subgroup A Q
  have hdvdQ : p ∣ Nat.card Q := by
    obtain ⟨n, hn, hcard⟩ := hQ.nontrivial_iff_card.mp inferInstance
    exact hcard.symm ▸ dvd_pow_self p (ne_of_gt hn)
  have hdvdF : p ∣ Nat.card F :=
    Nat.modEq_zero_iff_dvd.mp ((hA.card_modEq_card_fixedPoints Q).symm.trans hdvdQ.modEq_zero_nat)
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' p hdvdF
  refine ⟨(x : Q), (Subgroup.orderOf_coe x).trans hx, fun a => ?_⟩
  exact (FixedPoints.mem_subgroup A Q (x : Q)).mp x.2 a

end CFSG.GroupTheory
