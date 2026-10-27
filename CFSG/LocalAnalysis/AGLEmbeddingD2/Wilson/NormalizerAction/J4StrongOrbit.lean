module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.NormalizerAction.J4Strong

public noncomputable section

namespace CFSG.AGLEmbeddingD2.Wilson.NormalizerAction

open CFSG.Sporadic.J4 CFSG.Sporadic.J4Schreier
open scoped commutatorElement Matrix

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem zpowers_eq_of_mem_of_ne_one {G : Type*} [Group G] [Finite G] {z x : G} (hz : orderOf z = 11)
    (hx : x ∈ Subgroup.zpowers z) (hx1 : x ≠ 1) :
    Subgroup.zpowers x = Subgroup.zpowers z := by
  have hle : Subgroup.zpowers x ≤ Subgroup.zpowers z := (Subgroup.zpowers_le).2 hx
  have hdvd : Nat.card (Subgroup.zpowers x) ∣ Nat.card (Subgroup.zpowers z) :=
    Subgroup.card_dvd_of_le hle
  rw [Nat.card_zpowers, Nat.card_zpowers, hz] at hdvd
  rcases (Nat.dvd_prime (by norm_num)).1 hdvd with h | h
  · exact absurd (orderOf_eq_one_iff.1 h) hx1
  · exact Subgroup.eq_of_le_of_card_ge hle (by rw [Nat.card_zpowers, Nat.card_zpowers, hz, h])

theorem conj_pow_nat {G : Type*} [Group G] (a b : G) (k : ℕ) :
    (a * b * a⁻¹) ^ k = a * b ^ k * a⁻¹ := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ, ih, pow_succ]; group

theorem iterate_conj_pow {G : Type*} [Group G] (a z : G) (hz : a * z * a⁻¹ = z ^ 2) (k : ℕ) :
    a ^ k * z * (a ^ k)⁻¹ = z ^ (2 ^ k) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have : a ^ (k + 1) * z * (a ^ (k + 1))⁻¹ = a * (a ^ k * z * (a ^ k)⁻¹) * a⁻¹ := by
      rw [pow_succ']; group
    have h2 : a * z ^ (2 ^ k) * a⁻¹ = (a * z * a⁻¹) ^ (2 ^ k) := (conj_pow_nat a z _).symm
    rw [this, ih, h2, hz, ← pow_mul, ← pow_succ']


theorem exists_two_pow_mod : ∀ j, j < 11 → j ≠ 0 → ∃ k < 10, 2 ^ k % 11 = j := by decide

theorem orbit_qz_eq : {x | ∃ n ∈ Subgroup.normalizer (Q11 : Set J), x = n * qz * n⁻¹} =
    (Subgroup.zpowers qz : Set J) \ {1} := by
  have hq11 : qz ^ 11 = 1 := by
    have := pow_orderOf_eq_one qz
    rwa [orderOf_qz] at this
  ext x
  constructor
  · rintro ⟨n, hn, rfl⟩
    refine ⟨(conj_mem_zpowers_iff hn).2 (Subgroup.mem_zpowers qz), ?_⟩
    intro h
    rw [Set.mem_singleton_iff] at h
    apply qz_ne_one
    have : n⁻¹ * (n * qz * n⁻¹) * n = qz := by group
    rw [← this, h]; group
  · rintro ⟨hx, hx1⟩
    rw [Set.mem_singleton_iff] at hx1
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
    have hm : qz ^ m = qz ^ (m % 11).toNat := by
      have h1 : qz ^ (m % (orderOf qz : ℤ)) = qz ^ m := zpow_mod_orderOf qz m
      rw [orderOf_qz] at h1
      rw [← h1, ← zpow_natCast, Int.toNat_of_nonneg (Int.emod_nonneg _ (by norm_num))]
      norm_num
    set j := (m % 11).toNat with hj
    have hj11 : j < 11 := by
      have := Int.emod_lt_of_pos m (show (0:ℤ) < 11 by norm_num)
      omega
    have hj0 : j ≠ 0 := by
      intro h0
      apply hx1
      rw [hm, h0, pow_zero]
    obtain ⟨k, hk, hkj⟩ : ∃ k < 10, 2 ^ k % 11 = j := exists_two_pow_mod j hj11 hj0
    refine ⟨nrm₂ ^ k, (Subgroup.normalizer (Q11 : Set J)).pow_mem nrm₂_mem_normalizer k, ?_⟩
    have h3 : qz ^ (2 ^ k % 11) = qz ^ (2 ^ k) := by
      have := pow_mod_orderOf qz (2 ^ k)
      rwa [orderOf_qz] at this
    rw [@iterate_conj_pow J (Subgroup.toGroup J) nrm₂ qz nrm₂_qz k, hm, ← hkj, h3]

theorem card_orbit_qz : Nat.card ↥({x | ∃ n ∈ Subgroup.normalizer (Q11 : Set J),
    x = n * qz * n⁻¹} : Set J) = 10 := by
  rw [orbit_qz_eq, Nat.card_coe_set_eq, Set.ncard_sdiff_singleton_of_mem (Subgroup.one_mem _),
    ← Nat.card_coe_set_eq]
  have h2 : Nat.card (Subgroup.zpowers qz) = 11 := by rw [Nat.card_zpowers, orderOf_qz]
  have h3 : Nat.card ((Subgroup.zpowers qz : Set J)) = 11 := h2
  rw [h3]

theorem card_normalizer_inf_centralizer_qz :
    Nat.card ↥(Subgroup.normalizer (Q11 : Set J) ⊓ Subgroup.centralizer ({qz} : Set J)) =
      11 ^ 3 * 24 := by
  have h := card_inf_centralizer_mul_orbit (Subgroup.normalizer (Q11 : Set J)) qz
  rw [card_orbit_qz, card_normalizer_Q11] at h
  omega

end CFSG.AGLEmbeddingD2.Wilson.NormalizerAction
