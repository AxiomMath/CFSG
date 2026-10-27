module

public import CFSG.LocalAnalysis.AGLEmbedding.LinTwoTorusFacts
public import CFSG.LocalAnalysis.AGLEmbedding.ResidualFiveOddCore
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.OddCoreElimination.CentralizerContainmentKernel
public import CFSG.Assembly.RankThreeEvenDefs

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

section Galois

theorem pow_three_eq_one_galois (n : ℕ) (a : Multiplicative (GaloisField 3 n)) : a ^ 3 = 1 := by
  have : (3 : GaloisField 3 n) = 0 := by
    have := CharP.cast_eq_zero (GaloisField 3 n) 3
    exact_mod_cast this
  apply Multiplicative.toAdd.injective
  simp only [toAdd_pow, toAdd_one]
  rw [nsmul_eq_mul, Nat.cast_ofNat, this, zero_mul]

theorem isElemAbelian_of_galois {Y : Type} [Group Y] {X : Subgroup Y} {n : ℕ} (hn : n ≠ 0)
    (φ : Multiplicative (GaloisField 3 n) ≃* X) :
    IsElemAbelian 3 X ∧ Nat.card X = 3 ^ n := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine ⟨⟨IsMulCommutative.of_comm fun a b => ?_, fun x hx => ?_⟩, ?_⟩
  · obtain ⟨a', rfl⟩ := φ.surjective a
    obtain ⟨b', rfl⟩ := φ.surjective b
    rw [← map_mul, ← map_mul, mul_comm]
  · obtain ⟨a, ha⟩ := φ.surjective ⟨x, hx⟩
    have h : (⟨x, hx⟩ : X) ^ 3 = 1 := by
      rw [← ha, ← map_pow, pow_three_eq_one_galois, map_one]
    simpa using congrArg Subtype.val h
  · rw [← Nat.card_congr φ.toEquiv]
    change Nat.card (GaloisField 3 n) = 3 ^ n
    exact GaloisField.card 3 n hn

end Galois

variable {G : Type} [Group G] [Finite G]

theorem coprime_three_card_pCore_two (M : Subgroup G) :
    Nat.Coprime 3 (Nat.card (CFSG.pCore 2 ↥M)) := by
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (CFSG.pCore_isPGroup (p := 2) (G := ↥M))
  rw [hk]
  exact ((Nat.coprime_primes Nat.prime_three Nat.prime_two).mpr (by norm_num)).pow_right k

theorem eq_of_mk_eq_three {M X : Subgroup G} (hXM : X ≤ M) (hX : IsPGroup 3 X) {a b : G}
    (ha : a ∈ X) (hb : b ∈ X)
    (hab : QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨a, hXM ha⟩ =
      QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨b, hXM hb⟩) : a = b := by
  have h := eq_of_mk_eq_of_isPGroup Nat.prime_three (CFSG.pCore 2 ↥M)
    (coprime_three_card_pCore_two M) (hX.comap_subtype (K := M))
    (Subgroup.mem_subgroupOf.mpr ha) (Subgroup.mem_subgroupOf.mpr hb) hab
  exact congrArg Subtype.val h

theorem barM_galois {M X : Subgroup G} (hXM : X ≤ M) {n : ℕ} (hn : n ≠ 0)
    (φ : Multiplicative (GaloisField 3 n) ≃* X) :
    IsElemAbelian 3 (barM M X) ∧ Nat.card (barM M X) = 3 ^ n := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hXel, hXcard⟩ := isElemAbelian_of_galois hn φ
  refine ⟨elementary_abelian_map 3 ?_ (QuotientGroup.mk' (CFSG.pCore 2 ↥M)), ?_⟩
  · refine ⟨IsMulCommutative.of_comm fun a b => Subtype.ext (Subtype.ext ?_), fun x hx => ?_⟩
    · have h := congrArg Subtype.val ((isMulCommutative_iff.mp hXel.1)
        ⟨(a : M), Subgroup.mem_subgroupOf.mp a.2⟩ ⟨(b : M), Subgroup.mem_subgroupOf.mp b.2⟩)
      simpa using h
    · exact Subtype.ext (hXel.2 _ (Subgroup.mem_subgroupOf.mp hx))
  · rw [card_barM_of_isPGroup Nat.prime_three (by norm_num) hXM (IsPGroup.of_card (n := n) hXcard),
      hXcard]

omit [Finite G] in
theorem mk_mem_centralizer_of_commute {M : Subgroup G} {t z : G} (htM : t ∈ M) (hzM : z ∈ M)
    (h : t * z = z * t) :
    QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨t, htM⟩ ∈ Subgroup.centralizer
      ({QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨z, hzM⟩} : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := by
  rw [Subgroup.mem_centralizer_singleton_iff]
  have h2 : (⟨t, htM⟩ : M) * ⟨z, hzM⟩ = ⟨z, hzM⟩ * ⟨t, htM⟩ := Subtype.ext h
  rw [← map_mul, ← map_mul, h2]

theorem coprime_six_orderOf_mk_of_isPGroup {M : Subgroup G} {t : G} (htM : t ∈ M) {r : ℕ}
    (hr : r.Prime) (hr2 : r ≠ 2) (hr3 : r ≠ 3) (htr : IsPGroup r (Subgroup.zpowers t)) :
    Nat.Coprime 6 (orderOf (QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨t, htM⟩)) := by
  have : Fact r.Prime := ⟨hr⟩
  obtain ⟨a, ha⟩ := htr.exists_card_eq
  rw [Nat.card_zpowers] at ha
  have hdvd : orderOf (QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨t, htM⟩) ∣ r ^ a := by
    rw [← ha]
    have h1 : (⟨t, htM⟩ : M) ^ orderOf t = 1 := Subtype.ext (by simp [pow_orderOf_eq_one])
    exact orderOf_dvd_of_pow_eq_one (by rw [← map_pow, h1, map_one])
  obtain ⟨b, -, hb⟩ := (Nat.dvd_prime_pow hr).mp hdvd
  rw [hb]
  refine Nat.Coprime.pow_right b ?_
  rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd hr]
  intro h6
  rcases (Nat.Prime.dvd_mul hr).mp (show r ∣ 2 * 3 by simpa using h6) with h | h
  · exact hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp h)
  · exact hr3 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_three).mp h)

theorem mside_torus_of_big {M : Subgroup G} {z : G} (hzM : z ∈ M) {n e : ℕ} {X : Subgroup G}
    (φ : Multiplicative (GaloisField 3 n) ≃* X) (hn3 : 3 ≤ n) (he : e = 1 ∨ (e = 2 ∧ 3 ≤ n))
    (hXCM : X ≤ Subgroup.centralizer ({z} : Set G) ⊓ M)
    (htor : ∀ μ : (GaloisField 3 n)ˣ, ∃ t ∈ Subgroup.centralizer ({z} : Set G) ⊓ M,
      ∀ a : Multiplicative (GaloisField 3 n), t * (φ a : G) * t⁻¹ =
        φ (Multiplicative.ofAdd ((μ : GaloisField 3 n) ^ e * Multiplicative.toAdd a))) :
    ∃ (r : ℕ) (t : ↥M ⧸ CFSG.pCore 2 ↥M), 5 ≤ r ∧ IsElemAbelian 3 (barM M X) ∧
      3 ^ n = Nat.card (barM M X) ∧ Nat.Coprime 6 (orderOf t) ∧
      t ∈ Subgroup.centralizer
        ({QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨z, hzM⟩} : Set (↥M ⧸ CFSG.pCore 2 ↥M)) ∧
      t ∈ Subgroup.normalizer (barM M X : Set (↥M ⧸ CFSG.pCore 2 ↥M)) ∧
      (∃ x ∈ barM M X, t * x * t⁻¹ ≠ x) ∧
      ∀ k : ℕ, ¬ r ∣ k → ∀ Y₀ : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M), Y₀ ≤ barM M X →
        t ^ k ∈ Subgroup.normalizer (Y₀ : Set (↥M ⧸ CFSG.pCore 2 ↥M)) → Y₀ = ⊥ ∨ Y₀ = barM M X := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hXM : X ≤ M := fun x hx => (hXCM hx).2
  obtain ⟨hXel, hXcard⟩ := barM_galois hXM (by omega) φ
  have hXp : IsPGroup 3 X := IsPGroup.of_card (n := n) (isElemAbelian_of_galois (by omega) φ).2
  have htor2 : ∃ φ : Multiplicative (GaloisField 3 n) ≃* X, ∀ μ : (GaloisField 3 n)ˣ,
      ∃ t ∈ Subgroup.centralizer ({z} : Set G) ⊓ M, ∀ a : Multiplicative (GaloisField 3 n),
        t * (φ a : G) * t⁻¹ = φ (Multiplicative.ofAdd ((μ : GaloisField 3 n) ^ 2 *
          Multiplicative.toAdd a)) := by
    refine ⟨φ, fun μ => ?_⟩
    rcases he with rfl | ⟨rfl, -⟩
    · obtain ⟨t, ht, hta⟩ := htor (μ ^ 2)
      refine ⟨t, ht, fun a => ?_⟩
      rw [hta a]
      simp
    · exact htor μ
  obtain ⟨r, t, hr, hnr, hr2, hr3, -, -, htB, htX, htr, -, hnt, hirr⟩ :=
    exists_ppd_torus_element (by norm_num : (3 : ℕ) ≠ 2) hn3 htor2
  set mk := QuotientGroup.mk' (CFSG.pCore 2 ↥M) with hmk
  have hr5 : 5 ≤ r := by
    rcases (show r = 4 ∨ 5 ≤ r by omega) with h4 | h5
    · exact absurd (h4 ▸ hr) (by norm_num)
    · exact h5
  refine ⟨r, mk ⟨t, htB.2⟩, hr5, hXel, hXcard.symm,
    coprime_six_orderOf_mk_of_isPGroup htB.2 hr hr2 hr3 htr,
    mk_mem_centralizer_of_commute htB.2 hzM (Subgroup.mem_centralizer_singleton_iff.mp htB.1),
    mem_normalizer_barM htB.2 htX, ?_, fun k hk Y₀ hY₀ hYk => ?_⟩
  · obtain ⟨x, hx, hne⟩ := hnt
    refine ⟨mk ⟨x, hXM hx⟩, Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hx), ?_⟩
    intro heq
    have hmem : t * x * t⁻¹ ∈ X := (Subgroup.mem_normalizer_iff.mp htX x).mp hx
    apply hne
    refine eq_of_mk_eq_three hXM hXp hmem hx ?_
    rw [← heq]
    simp only [← map_mul, ← map_inv]
    rfl
  · have htkM : t ^ k ∈ M := M.pow_mem htB.2 k
    have htkX : t ^ k ∈ Subgroup.normalizer (X : Set G) := Subgroup.pow_mem _ htX k
    have hpow : mk ⟨t ^ k, htkM⟩ = (mk ⟨t, htB.2⟩) ^ k := by
      rw [← map_pow]
      rfl
    exact eq_bot_or_eq_barM_of_mem_normalizer hXM htkM htkX (hirr k hk) hY₀ (hpow ▸ hYk)

end CFSG.AGLEmbedding
