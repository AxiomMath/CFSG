module

public import Mathlib.GroupTheory.Sylow
public import Mathlib.GroupTheory.IndexNormal

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

variable {G : Type} [Group G]

theorem y7a_odd_sub {A N : Subgroup G} (hAN : A ≤ N) [hn : (A.subgroupOf N).Normal]
    (hcard : Nat.card (↥N ⧸ A.subgroupOf N) = 18) :
    ∃ N₃ : Subgroup G, A ≤ N₃ ∧ N₃ ≤ N ∧ (∀ x ∈ N₃, x ^ 9 ∈ A) ∧
      ∀ x ∈ N, ∀ j : ℕ, x ^ (3 ^ j) ∈ A → x ∈ N₃ := by
  haveI h3prime : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI hfinite : Finite (↥N ⧸ A.subgroupOf N) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  let P : Sylow 3 (↥N ⧸ A.subgroupOf N) := default
  have hfact18 : (18 : ℕ).factorization 3 = 2 := by
    have h1 : (18 : ℕ).factorization 3
        = (2 : ℕ).factorization 3 + (3 ^ 2 : ℕ).factorization 3 := by
      rw [show (18 : ℕ) = 2 * 3 ^ 2 by norm_num]
      exact Nat.factorization_mul_apply_of_coprime (by norm_num : Nat.Coprime 2 (3 ^ 2))
    rw [h1, Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ (3 : ℕ) ∣ 2),
      Nat.factorization_pow_self (p := 3) (n := 2) Nat.prime_three]
  have hcardP : Nat.card P = 9 := by
    rw [Sylow.card_eq_multiplicity P, hcard, hfact18]
    norm_num
  have hindexP : P.index = 2 := by
    have h : Nat.card P * P.index = 18 := by
      simpa [hcard] using Subgroup.card_mul_index (P : Subgroup (↥N ⧸ A.subgroupOf N))
    rw [hcardP] at h
    omega
  have hPnormal : P.Normal := Subgroup.normal_of_index_eq_two hindexP
  haveI : (P : Subgroup (↥N ⧸ A.subgroupOf N)).Normal := hPnormal
  have hsub_le : ∀ H : Subgroup (↥N ⧸ A.subgroupOf N), IsPGroup 3 H → H ≤ P := by
    intro H hH
    obtain ⟨P', hP'⟩ := IsPGroup.exists_le_sylow hH
    have hle : (P : Subgroup (↥N ⧸ A.subgroupOf N)) ≤ P' :=
      P.isPGroup'.le_sylow_of_normal P'
    have hEq : (P' : Subgroup (↥N ⧸ A.subgroupOf N)) = P :=
      P.is_maximal' P'.isPGroup' hle
    intro x hx
    exact hEq ▸ hP' hx
  let φ : ↥N →* (↥N ⧸ A.subgroupOf N) := QuotientGroup.mk' (A.subgroupOf N)
  let N₃ : Subgroup G := (P.comap φ).map N.subtype
  have hmemN₃ : ∀ y : ↥N, φ y ∈ (P : Subgroup (↥N ⧸ A.subgroupOf N)) →
      N.subtype y ∈ N₃ :=
    fun y hy => Subgroup.mem_map.mpr ⟨y, Subgroup.mem_comap.mpr hy, rfl⟩
  refine ⟨N₃, ?_, ?_, ?_, ?_⟩
  · intro a ha
    refine Subgroup.mem_map.mpr ⟨⟨a, hAN ha⟩, ?_, rfl⟩
    rw [Subgroup.mem_comap]
    have hmem : (⟨a, hAN ha⟩ : ↥N) ∈ A.subgroupOf N := by
      rw [Subgroup.mem_subgroupOf]; exact ha
    have h1 : φ ⟨a, hAN ha⟩ = 1 := (QuotientGroup.eq_one_iff _).mpr hmem
    rw [h1]
    exact (P : Subgroup (↥N ⧸ A.subgroupOf N)).one_mem
  · intro x hx
    obtain ⟨y, -, hxy⟩ := Subgroup.mem_map.mp hx
    rw [← hxy]
    exact y.2
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
    have hyP : φ y ∈ (P : Subgroup (↥N ⧸ A.subgroupOf N)) := Subgroup.mem_comap.mp hy
    have hz9 : (φ y) ^ 9 = 1 := by
      have h := pow_card_eq_one' (G := ↥(P : Subgroup (↥N ⧸ A.subgroupOf N)))
        (x := ⟨φ y, hyP⟩)
      rw [hcardP] at h
      simpa using congrArg Subtype.val h
    have h1 : φ (y ^ 9) = 1 := by rw [map_pow, hz9]
    have hmem : y ^ 9 ∈ A.subgroupOf N := by
      refine (QuotientGroup.eq_one_iff (y ^ 9)).mp ?_
      change φ (y ^ 9) = 1
      exact h1
    simpa using (Subgroup.mem_subgroupOf.mp hmem)
  · intro x hxN j hxj
    let y : ↥N := ⟨x, hxN⟩
    have hpow_q : (φ y) ^ (3 ^ j) = 1 := by
      have hmem : y ^ (3 ^ j) ∈ A.subgroupOf N := by
        rw [Subgroup.mem_subgroupOf]
        simpa [y] using hxj
      have h1 : φ (y ^ (3 ^ j)) = 1 := (QuotientGroup.eq_one_iff (y ^ (3 ^ j))).mpr hmem
      simpa [map_pow] using h1
    have hIsP : IsPGroup 3 (Subgroup.zpowers (φ y)) := by
      refine IsPGroup.of_card_dvd_pow (n := j) ?_
      rw [Nat.card_zpowers]
      exact orderOf_dvd_iff_pow_eq_one.mpr hpow_q
    exact hmemN₃ y (hsub_le _ hIsP (Subgroup.mem_zpowers _))

end CFSG.OddStandard.HigherRank.YamadaG23
