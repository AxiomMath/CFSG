module

public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.AGLEmbeddingD2.Wilson.Census219

theorem pow_eq_one_of_pPower_of_exp {G : Type*} [Group G] [Finite G] (p n : ℕ) [hp : Fact p.Prime]
    (Q : Subgroup G) (hQ : Nat.card Q = p ^ n) (hG : ¬ p ^ (n + 1) ∣ Nat.card G)
    (hexp : ∀ q ∈ Q, q ^ p = 1) {y : G} {k : ℕ} (hy : y ^ p ^ k = 1) : y ^ p = 1 := by
  have hGne : Nat.card G ≠ 0 := Nat.card_pos.ne'
  have hfac : (Nat.card G).factorization p = n := by
    have h3 : p ^ n ∣ Nat.card G := hQ ▸ Subgroup.card_subgroup_dvd_card Q
    have a := (Nat.Prime.pow_dvd_iff_le_factorization hp.out hGne).mp h3
    have b : ¬ n + 1 ≤ (Nat.card G).factorization p := fun h =>
      hG ((Nat.Prime.pow_dvd_iff_le_factorization hp.out hGne).mpr h)
    omega
  let P₀ : Sylow p G := Sylow.ofCard Q (by rw [hQ, hfac])
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hp.out).1 (orderOf_dvd_of_pow_eq_one hy)
  have hpg : IsPGroup p (Subgroup.zpowers y) :=
    IsPGroup.of_card (n := j) (by rw [Nat.card_zpowers, hj])
  obtain ⟨P', hP'⟩ := hpg.exists_le_sylow
  obtain ⟨h, hh⟩ := MulAction.exists_smul_eq G P₀ P'
  have hyP' : y ∈ (P' : Subgroup G) := hP' (Subgroup.mem_zpowers y)
  have : (P' : Subgroup G) = (h • P₀ : Sylow p G) := by rw [hh]
  rw [this, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hyP'
  have hq : h⁻¹ * y * h ∈ Q := hyP'
  have h1 := hexp _ hq
  have : y ^ p = h * (h⁻¹ * y * h) ^ p * h⁻¹ := by
    have hc := conj_pow (a := h⁻¹) (b := y) (i := p)
    rw [inv_inv] at hc
    rw [hc]; group
  rw [this, h1]
  group

end CFSG.AGLEmbeddingD2.Wilson.Census219
