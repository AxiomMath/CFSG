module

public import CFSG.LocalAnalysis.RankThreeUC.GN15JOutBase
public import CFSG.RankThree.PartOne.S11d.OutAbstract

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15.GN15

open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.RankThree.PartOne.OutStructure
open scoped commutatorElement

namespace FFO

variable {G : Type} [Group G]

theorem conj_pow_eq_inv {a y : G} (h : a * y * a⁻¹ = y⁻¹) (n : ℕ) :
    a * y ^ n * a⁻¹ = (y ^ n)⁻¹ := by
  rw [← conj_pow, h, inv_pow]

theorem exists_pow_not_mem_pow_mem {K : Subgroup G} {y : G} {r e : ℕ}
    (hord : orderOf y = r ^ e) (hy : y ∉ K) :
    ∃ k : ℕ, y ^ (r ^ k) ∉ K ∧ (y ^ (r ^ k)) ^ r ∈ K := by
  classical
  have hex : ∃ i : ℕ, y ^ (r ^ i) ∈ K := ⟨e, by
    rw [← hord, pow_orderOf_eq_one]
    exact K.one_mem⟩
  have h0 : y ^ (r ^ Nat.find hex) ∈ K := Nat.find_spec hex
  have hne : Nat.find hex ≠ 0 := by
    intro h
    rw [h, pow_zero, pow_one] at h0
    exact hy h0
  obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero hne
  refine ⟨j, Nat.find_min hex (by omega : j < Nat.find hex), ?_⟩
  rw [← pow_mul, ← pow_succ]
  rw [hj] at h0
  exact h0

theorem false_of_outPNice {L : Subgroup G} [Group.IsPerfect ↥L] {r : ℕ} (hr : r.Prime)
    (hr2 : r ≠ 2) (hN : OutPNice r (↥L ⧸ Subgroup.center ↥L)) {a y : G}
    (ha : a ∈ Subgroup.normalizer (L : Set G)) (hy : y ∈ Subgroup.normalizer (L : Set G))
    (hinv : a * y * a⁻¹ = y⁻¹) (hyr : y ^ r ∈ L ⊔ Subgroup.centralizer (L : Set G))
    (hy1 : y ∉ L ⊔ Subgroup.centralizer (L : Set G)) : False := by
  have h := normalizer_power_of_outPNice hr L hN (a := y) (x := a) hy ha hyr hy1 (m := -1) (by
    rw [hinv, neg_neg, zpow_one, inv_mul_cancel]
    exact one_mem _)
  have h2 : (r : ℤ) ∣ 2 := by
    have : (-1 : ℤ) - 1 = -2 := by norm_num
    rw [this, dvd_neg] at h
    exact h
  have h3 : r ∣ 2 := by exact_mod_cast h2
  exact hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).1 h3)

theorem false_of_outPCentral {L : Subgroup G} [Group.IsPerfect ↥L] {r : ℕ} (hr : r.Prime)
    (hr2 : r ≠ 2) (hN : OutPCentral r (↥L ⧸ Subgroup.center ↥L)) {a y : G}
    (ha : a ∈ Subgroup.normalizer (L : Set G)) (hy : y ∈ Subgroup.normalizer (L : Set G))
    (hinv : a * y * a⁻¹ = y⁻¹) (hyr : y ^ r ∈ L ⊔ Subgroup.centralizer (L : Set G))
    (hy1 : y ∉ L ⊔ Subgroup.centralizer (L : Set G)) : False := by
  have h := normalizer_power_of_outPCentral hr L hN (a := y) (x := a) hy ha hyr hy1 (m := -1) (by
    rw [hinv, neg_neg, zpow_one, inv_mul_cancel]
    exact one_mem _)
  have h2 : (r : ℤ) ∣ 2 := by
    have : (-1 : ℤ) - 1 = -2 := by norm_num
    rw [this, dvd_neg] at h
    exact h
  have h3 : r ∣ 2 := by exact_mod_cast h2
  exact hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).1 h3)

theorem mem_of_outer_commutative {L : Subgroup G} (hc : IsMulCommutative (Outer ↥L)) {a y : G}
    (ha : a ∈ Subgroup.normalizer (L : Set G)) (hy : y ∈ Subgroup.normalizer (L : Set G))
    (hinv : a * y * a⁻¹ = y⁻¹) {r e : ℕ} (hr2 : r ≠ 2) (hr : r.Prime) (hord : y ^ (r ^ e) = 1) :
    y ∈ L ⊔ Subgroup.centralizer (L : Set G) := by
  let a' : Subgroup.normalizer (L : Set G) := ⟨a, ha⟩
  let y' : Subgroup.normalizer (L : Set G) := ⟨y, hy⟩
  have h1 : a' * y' * a'⁻¹ = y'⁻¹ := Subtype.ext hinv
  have h2 : JOut.outerHom L a' * JOut.outerHom L y' * (JOut.outerHom L a')⁻¹ =
      (JOut.outerHom L y')⁻¹ := by
    rw [← map_inv, ← map_mul, ← map_mul, h1, map_inv]
  have h3 : JOut.outerHom L a' * JOut.outerHom L y' = JOut.outerHom L y' * JOut.outerHom L a' :=
    hc.is_comm.comm _ _
  have h4 : JOut.outerHom L y' = (JOut.outerHom L y')⁻¹ := by
    rw [← h2, h3]
    group
  have h5 : JOut.outerHom L y' * JOut.outerHom L y' = 1 := by
    rw [mul_eq_one_iff_eq_inv]
    exact h4
  have hdvd2 : orderOf (JOut.outerHom L y') ∣ 2 :=
    orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact h5)
  have hpow : JOut.outerHom L y' ^ (r ^ e) = 1 := by
    rw [← map_pow]
    have : y' ^ (r ^ e) = 1 := Subtype.ext (by simpa using hord)
    rw [this, map_one]
  have hdvd1 : orderOf (JOut.outerHom L y') ∣ r ^ e := orderOf_dvd_of_pow_eq_one hpow
  have hcop : Nat.Coprime 2 (r ^ e) :=
    Nat.Coprime.pow_right _ ((Nat.coprime_primes Nat.prime_two hr).2 (Ne.symm hr2))
  have h6 : orderOf (JOut.outerHom L y') = 1 :=
    Nat.eq_one_of_dvd_coprimes hcop hdvd2 hdvd1
  exact JOut.mem_sup_centralizer_of_outerHom_eq_one (w := y') (orderOf_eq_one_iff.1 h6)

end FFO

end CFSG.LocalAnalysis.RankThreeUC.S15.GN15
