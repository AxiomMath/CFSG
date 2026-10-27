module

public import CFSG.GH74.GLS.C3.Layer3.A8Cover

public section

namespace CFSG.HardMathSupport.Timmesfeld.SporadicBalance.CommutingPair

variable {G : Type*} [Group G]

theorem zpow_eq_pow_toNat_emod {p : ℕ} (hp : 0 < p) {a : G} (ha : a ^ p = 1) (m : ℤ) :
    a ^ m = a ^ (m % (p : ℤ)).toNat := by
  have hnn : 0 ≤ m % (p : ℤ) := Int.emod_nonneg m (by exact_mod_cast hp.ne')
  rw [← zpow_natCast, Int.toNat_of_nonneg hnn]
  conv_lhs => rw [← Int.emod_add_mul_ediv m p]
  rw [zpow_add, zpow_mul, zpow_natCast, ha, one_zpow, mul_one]

theorem toNat_emod_lt {p : ℕ} (hp : 0 < p) (m : ℤ) : (m % (p : ℤ)).toNat < p := by
  have hlt : m % (p : ℤ) < p := Int.emod_lt_of_pos m (by exact_mod_cast hp)
  have hnn : 0 ≤ m % (p : ℤ) := Int.emod_nonneg m (by exact_mod_cast hp.ne')
  omega

theorem exists_pow_mul_pow_of_mem {p : ℕ} (hp : 0 < p) {a b : G} (h : Commute a b)
    (ha : a ^ p = 1) (hb : b ^ p = 1) {g : G} (hg : g ∈ Subgroup.closure ({a, b} : Set G)) :
    ∃ i < p, ∃ j < p, g = a ^ i * b ^ j := by
  obtain ⟨m, n, rfl⟩ := CFSG.GH74.GLS.Layer3.mem_closure_pair_of_commute h hg
  exact ⟨_, toNat_emod_lt hp m, _, toNat_emod_lt hp n, by
    rw [zpow_eq_pow_toNat_emod hp ha m, zpow_eq_pow_toNat_emod hp hb n]⟩

theorem card_closure_pair_eq_sq [Finite G] {p : ℕ} [hp : Fact p.Prime] {a b : G} (h : Commute a b)
    (ha : a ^ p = 1) (hb : b ^ p = 1) (ha1 : a ≠ 1) (hba : ∀ k < p, b ≠ a ^ k)
    (hG : ¬ p ^ 3 ∣ Nat.card G) : Nat.card (Subgroup.closure ({a, b} : Set G)) = p ^ 2 := by
  set K := Subgroup.closure ({a, b} : Set G) with hK
  have hp0 : 0 < p := hp.out.pos
  have hexp : ∀ g ∈ K, g ^ p = 1 := by
    intro g hg
    obtain ⟨i, -, j, -, rfl⟩ := exists_pow_mul_pow_of_mem hp0 h ha hb hg
    rw [(h.pow_pow i j).mul_pow, ← pow_mul, ← pow_mul, mul_comm i, mul_comm j, pow_mul, pow_mul,
      ha, hb, one_pow, one_pow, mul_one]
  have hpK : IsPGroup p K := fun g =>
    ⟨1, Subtype.ext (by rw [pow_one, Subgroup.coe_pow]; exact hexp _ g.2)⟩
  obtain ⟨k, hk⟩ := hpK.exists_card_eq
  have hk2 : k ≤ 2 := by
    by_contra hk3
    push_neg at hk3
    apply hG
    have hdvd : Nat.card K ∣ Nat.card G := Subgroup.card_subgroup_dvd_card K
    rw [hk] at hdvd
    exact (pow_dvd_pow p hk3).trans hdvd
  have hord : orderOf a = p := orderOf_eq_prime ha ha1
  have haK : a ∈ K := Subgroup.subset_closure (by simp)
  have hbK : b ∈ K := Subgroup.subset_closure (by simp)
  have hz : Subgroup.zpowers a ≤ K := (Subgroup.zpowers_le).2 haK
  have hbz : b ∉ Subgroup.zpowers a := by
    intro hb'
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.1 hb'
    apply hba _ (toNat_emod_lt hp0 m)
    rw [← hm, zpow_eq_pow_toNat_emod hp0 ha m]
  have hk1 : 2 ≤ k := by
    by_contra hk1
    push_neg at hk1
    have hle : Nat.card (Subgroup.zpowers a) ≤ Nat.card K := Subgroup.card_le_of_le hz
    have hKle : Nat.card K ≤ p := by
      rw [hk]
      interval_cases k <;> simp <;> omega
    have heq : Subgroup.zpowers a = K := Subgroup.eq_of_le_of_card_ge hz (by
      rw [Nat.card_zpowers, hord]; exact hKle)
    exact hbz (heq ▸ hbK)
  rw [hk, le_antisymm hk2 hk1]

theorem factorization_pow_mul {p : ℕ} (hp : p.Prime) (k m : ℕ) (hm : ¬ p ∣ m) :
    (p ^ k * m).factorization p = k := by
  have hm0 : m ≠ 0 := by rintro rfl; exact hm (dvd_zero p)
  rw [Nat.factorization_mul (pow_ne_zero k hp.ne_zero) hm0, Finsupp.add_apply,
    hp.factorization_pow, Finsupp.single_eq_same, Nat.factorization_eq_zero_of_not_dvd hm,
    add_zero]

theorem orderOf_inv_mul_mul (g x : G) : orderOf (g⁻¹ * x * g) = orderOf x := by
  simpa [MulAut.conj_apply] using (MulAut.conj g⁻¹).orderOf_eq x

theorem eq_one_of_inv_mul_mul_eq_one {g x : G} (h : g⁻¹ * x * g = 1) : x = 1 := by
  calc x = g * (g⁻¹ * x * g) * g⁻¹ := by group
    _ = 1 := by rw [h]; group


end CFSG.HardMathSupport.Timmesfeld.SporadicBalance.CommutingPair
