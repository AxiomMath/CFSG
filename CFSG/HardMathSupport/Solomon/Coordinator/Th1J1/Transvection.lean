module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.GroupTheory.ElemAbelianClosure
public import CFSG.GroupTheory.QuasisimpleCommutingProductBound
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.I28_8.Th1J1

open CFSG.Open
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

private theorem mem_of_conj_mem_of_centralizes {K : Subgroup G} {c : G}
    (hc : ∀ z ∈ K, c * z = z * c) {y : G} (hy : c * y * c⁻¹ ∈ K) : y ∈ K := by
  have h1 : c * (c * y * c⁻¹) = c * y * c⁻¹ * c := hc _ hy
  have h2 : c⁻¹ * (c * y * c⁻¹) * c = c * y * c⁻¹ := by
    calc c⁻¹ * (c * y * c⁻¹) * c = c⁻¹ * (c * y * c⁻¹ * c) := by group
      _ = c⁻¹ * (c * (c * y * c⁻¹)) := by rw [h1]
      _ = c * y * c⁻¹ := by group
  have h3 : y = c * y * c⁻¹ := by
    calc y = c⁻¹ * (c * y * c⁻¹) * c := by group
      _ = c * y * c⁻¹ := h2
  rw [h3]
  exact hy

theorem pow_twelve_mem_centralizer {M : Subgroup G} (hM : IsElemAbelian 2 M) {e f : G}
    (he : e ∈ Subgroup.normalizer (M : Set G)) (hf : f ∈ Subgroup.normalizer (M : Set G))
    (hce : Nat.card M ≤ 2 * Nat.card (M ⊓ Subgroup.centralizer ({e} : Set G) : Subgroup G))
    (hcf : Nat.card M ≤ 2 * Nat.card (M ⊓ Subgroup.centralizer ({f} : Set G) : Subgroup G)) :
    (e * f) ^ 12 ∈ Subgroup.centralizer (M : Set G) := by
  classical
  obtain ⟨Ce, hCe⟩ : ∃ C : Subgroup G, C = M ⊓ Subgroup.centralizer ({e} : Set G) := ⟨_, rfl⟩
  obtain ⟨Cf, hCf⟩ : ∃ C : Subgroup G, C = M ⊓ Subgroup.centralizer ({f} : Set G) := ⟨_, rfl⟩
  rw [← hCe] at hce
  rw [← hCf] at hcf
  obtain ⟨K, hK⟩ : ∃ C : Subgroup G, C = Ce ⊓ Cf := ⟨_, rfl⟩
  have hmemCe : ∀ k, k ∈ Ce ↔ k ∈ M ∧ k ∈ Subgroup.centralizer ({e} : Set G) := fun k => by
    rw [hCe, Subgroup.mem_inf]
  have hmemCf : ∀ k, k ∈ Cf ↔ k ∈ M ∧ k ∈ Subgroup.centralizer ({f} : Set G) := fun k => by
    rw [hCf, Subgroup.mem_inf]
  have hmemK : ∀ k, k ∈ K ↔ (k ∈ M ∧ k ∈ Subgroup.centralizer ({e} : Set G)) ∧
      (k ∈ M ∧ k ∈ Subgroup.centralizer ({f} : Set G)) := fun k => by
    rw [hK, Subgroup.mem_inf, hmemCe, hmemCf]
  have hCeM : Ce ≤ M := fun k hk => ((hmemCe k).1 hk).1
  have hCfM : Cf ≤ M := fun k hk => ((hmemCf k).1 hk).1
  have hKM : K ≤ M := fun k hk => ((hmemK k).1 hk).1.1
  have hcc : ∀ x ∈ Ce, ∀ y ∈ Cf, x * y = y * x := fun x hx y hy =>
    hM.comm (hCeM hx) (hCfM hy)
  have hprod : Nat.card (Ce ⊔ Cf : Subgroup G) * Nat.card K = Nat.card Ce * Nat.card Cf := by
    rw [hK]
    exact (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute Ce Cf hcc).1
  have hsup : Nat.card (Ce ⊔ Cf : Subgroup G) ≤ Nat.card M :=
    Subgroup.card_le_of_le (sup_le hCeM hCfM)
  have hMpos : 0 < Nat.card M := Nat.card_pos
  have hM4 : Nat.card M ≤ 4 * Nat.card K := by
    have h1 : Nat.card M * Nat.card M ≤ (2 * Nat.card Ce) * (2 * Nat.card Cf) :=
      Nat.mul_le_mul hce hcf
    have h2 : Nat.card (Ce ⊔ Cf : Subgroup G) * Nat.card K ≤ Nat.card M * Nat.card K :=
      Nat.mul_le_mul hsup le_rfl
    have h3 : Nat.card M * Nat.card M ≤ Nat.card M * (4 * Nat.card K) := by
      nlinarith
    exact Nat.le_of_mul_le_mul_left h3 hMpos
  have hKcard : Nat.card (K.subgroupOf M) = Nat.card K :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKM).toEquiv
  have hidx : (K.subgroupOf M).index ≤ 4 := by
    have hKpos : 0 < Nat.card (K.subgroupOf M) := Nat.card_pos
    have h2 : Nat.card (K.subgroupOf M) * (K.subgroupOf M).index ≤
        Nat.card (K.subgroupOf M) * 4 := by
      calc Nat.card (K.subgroupOf M) * (K.subgroupOf M).index = Nat.card M :=
            (K.subgroupOf M).card_mul_index
        _ ≤ 4 * Nat.card K := hM4
        _ = Nat.card (K.subgroupOf M) * 4 := by rw [hKcard]; ring
    exact Nat.le_of_mul_le_mul_left h2 hKpos
  obtain ⟨g, hg⟩ : ∃ g : G, g = e * f := ⟨_, rfl⟩
  rw [← hg]
  have hgN : g ∈ Subgroup.normalizer (M : Set G) := by
    rw [hg]
    exact Subgroup.mul_mem _ he hf
  have hgK : ∀ k ∈ K, Commute g k := by
    intro k hk
    have hk' := (hmemK k).1 hk
    have hek : e * k = k * e := Subgroup.mem_centralizer_iff.1 hk'.1.2 e (Set.mem_singleton e)
    have hfk : f * k = k * f := Subgroup.mem_centralizer_iff.1 hk'.2.2 f (Set.mem_singleton f)
    show g * k = k * g
    rw [hg, mul_assoc e f k, hfk, ← mul_assoc e k f, hek, mul_assoc k e f]
  have hgpow : ∀ i : ℕ, ∀ k ∈ K, Commute (g ^ i) k := fun i k hk => (hgK k hk).pow_left i
  have hconjM : ∀ i : ℕ, ∀ y ∈ M, g ^ i * y * (g ^ i)⁻¹ ∈ M := fun i y hy =>
    (Subgroup.mem_normalizer_iff.1 (pow_mem hgN i) y).1 hy
  have hmain : ∀ x ∈ M, Commute x (g ^ 12) := by
    intro x hx
    by_cases hxK : x ∈ K
    · exact (hgpow 12 x hxK).symm
    obtain ⟨xi, hxi⟩ : ∃ xi : ℕ → G, ∀ i, xi i = g ^ i * x * (g ^ i)⁻¹ := ⟨_, fun i => rfl⟩
    have hximem : ∀ i, xi i ∈ M := fun i => by rw [hxi]; exact hconjM i x hx
    have hxinotK : ∀ i, xi i ∉ K := by
      intro i hi
      rw [hxi] at hi
      exact hxK (mem_of_conj_mem_of_centralizes (fun z hz => (hgpow i z hz).eq) hi)
    have hkey : ∀ i d : ℕ, (xi i)⁻¹ * xi (i + d) ∈ K → x⁻¹ * xi d ∈ K := by
      intro i d h
      have e1 : (xi i)⁻¹ * xi (i + d) = g ^ i * (x⁻¹ * xi d) * (g ^ i)⁻¹ := by
        rw [hxi i, hxi (i + d), hxi d, pow_add]
        group
      rw [e1] at h
      exact mem_of_conj_mem_of_centralizes (fun z hz => (hgpow i z hz).eq) h
    haveI : Finite (↥M ⧸ (K.subgroupOf M)) := inferInstance
    letI : Fintype (↥M ⧸ (K.subgroupOf M)) := Fintype.ofFinite _
    have hQcard : (Finset.univ : Finset (↥M ⧸ (K.subgroupOf M))).card ≤ 4 := by
      rw [Finset.card_univ, ← Nat.card_eq_fintype_card]
      exact hidx
    have hne : ∀ i, (QuotientGroup.mk (⟨xi i, hximem i⟩ : ↥M) : ↥M ⧸ (K.subgroupOf M)) ≠
        QuotientGroup.mk (1 : ↥M) := by
      intro i h
      rw [QuotientGroup.eq, Subgroup.mem_subgroupOf] at h
      simp at h
      exact hxinotK i h
    have hcard : ((Finset.univ : Finset (↥M ⧸ (K.subgroupOf M))).erase
        (QuotientGroup.mk (1 : ↥M))).card < (Finset.range 4).card := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_range]
      omega
    obtain ⟨i, hi, j, hj, hij, hfij⟩ :=
      Finset.exists_ne_map_eq_of_card_lt_of_maps_to hcard
        (f := fun i : ℕ => (QuotientGroup.mk (⟨xi i, hximem i⟩ : ↥M) : ↥M ⧸ (K.subgroupOf M)))
        (fun i _ => Finset.mem_erase.2 ⟨hne i, Finset.mem_univ _⟩)
    have hi4 := Finset.mem_range.1 hi
    have hj4 := Finset.mem_range.1 hj
    have hrel : (xi i)⁻¹ * xi j ∈ K := by
      have hfij' : (QuotientGroup.mk (⟨xi i, hximem i⟩ : ↥M) : ↥M ⧸ (K.subgroupOf M)) =
          QuotientGroup.mk (⟨xi j, hximem j⟩ : ↥M) := hfij
      rw [QuotientGroup.eq, Subgroup.mem_subgroupOf] at hfij'
      simpa using hfij'
    obtain ⟨d, hd1, hd3, hk⟩ : ∃ d, 1 ≤ d ∧ d ≤ 3 ∧ x⁻¹ * xi d ∈ K := by
      rcases Nat.lt_or_gt_of_ne hij with h | h
      · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h.le
        exact ⟨d, by omega, by omega, hkey i d hrel⟩
      · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h.le
        refine ⟨d, by omega, by omega, hkey j d ?_⟩
        have hinv := K.inv_mem hrel
        rwa [mul_inv_rev, inv_inv] at hinv
    obtain ⟨k, hkdef⟩ : ∃ k, k = x⁻¹ * xi d := ⟨_, rfl⟩
    rw [← hkdef] at hk
    have hkk : k * k = 1 := hM.mul_self_eq_one (hKM hk)
    have hgdk : Commute (g ^ d) k := hgpow d k hk
    have hxid : xi d = x * k := by rw [hkdef, mul_inv_cancel_left]
    have h2 : xi (d + d) = g ^ d * xi d * (g ^ d)⁻¹ := by
      rw [hxi (d + d), hxi d, pow_add]
      group
    have hgdk' : g ^ d * k * (g ^ d)⁻¹ = k := by
      rw [hgdk.eq]
      exact mul_inv_cancel_right k (g ^ d)
    have hx2d : xi (d + d) = x := by
      calc xi (d + d) = g ^ d * xi d * (g ^ d)⁻¹ := h2
        _ = g ^ d * (x * k) * (g ^ d)⁻¹ := by rw [← hxid]
        _ = (g ^ d * x * (g ^ d)⁻¹) * (g ^ d * k * (g ^ d)⁻¹) := by group
        _ = xi d * k := by rw [hgdk', ← hxi d]
        _ = x * k * k := by rw [hxid]
        _ = x := by rw [mul_assoc, hkk, mul_one]
    have hcd : Commute (g ^ (d + d)) x := by
      have h' : g ^ (d + d) * x * (g ^ (d + d))⁻¹ = x := by
        rw [← hxi (d + d), hx2d]
      exact mul_inv_eq_iff_eq_mul.1 h'
    obtain ⟨n, hn⟩ : ∃ n, 12 = (d + d) * n := by
      interval_cases d
      · exact ⟨6, by norm_num⟩
      · exact ⟨3, by norm_num⟩
      · exact ⟨2, by norm_num⟩
    have hpow : g ^ 12 = (g ^ (d + d)) ^ n := by
      rw [← pow_mul, ← hn]
    rw [hpow]
    exact hcd.symm.pow_right n
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  exact (hmain x hx).eq

theorem pow_four_mem_centralizer {M : Subgroup G} (hM : IsElemAbelian 2 M) {e f : G}
    (he : e ∈ Subgroup.normalizer (M : Set G)) (hf : f ∈ Subgroup.normalizer (M : Set G))
    (hce : Nat.card M ≤ 2 * Nat.card (M ⊓ Subgroup.centralizer ({e} : Set G) : Subgroup G))
    (hcf : Nat.card M ≤ 2 * Nat.card (M ⊓ Subgroup.centralizer ({f} : Set G) : Subgroup G))
    (h3 : ¬ 3 ∣ orderOf (e * f)) :
    (e * f) ^ 4 ∈ Subgroup.centralizer (M : Set G) := by
  have h12 := pow_twelve_mem_centralizer hM he hf hce hcf
  obtain ⟨g, hg⟩ : ∃ g : G, g = e * f := ⟨_, rfl⟩
  rw [← hg] at h12 h3 ⊢
  have hcop : Nat.Coprime 3 (orderOf g) := (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 h3
  have hgcd : Nat.gcd 12 (orderOf g) ∣ 4 := by
    have h12' : Nat.gcd 12 (orderOf g) = Nat.gcd 4 (orderOf g) := by
      have h43 : (12 : ℕ) = 4 * 3 := by norm_num
      rw [h43, Nat.Coprime.gcd_mul_right_cancel 4 hcop]
    rw [h12']
    exact Nat.gcd_dvd_left 4 (orderOf g)
  obtain ⟨A, B, h4⟩ : ∃ A B : ℤ, (4 : ℤ) = 12 * A + (orderOf g : ℤ) * B := by
    obtain ⟨c, hc⟩ := hgcd
    refine ⟨Nat.gcdA 12 (orderOf g) * c, Nat.gcdB 12 (orderOf g) * c, ?_⟩
    have hc' : (4 : ℤ) = ((Nat.gcd 12 (orderOf g) : ℕ) : ℤ) * (c : ℤ) := by exact_mod_cast hc
    rw [hc', Nat.gcd_eq_gcd_ab 12 (orderOf g)]
    ring
  have hgo : g ^ (orderOf g : ℤ) = 1 := by
    rw [zpow_natCast, pow_orderOf_eq_one]
  have h12z : g ^ (12 : ℤ) = g ^ (12 : ℕ) := by exact_mod_cast zpow_natCast g 12
  have h4z : g ^ (4 : ℤ) = g ^ (4 : ℕ) := by exact_mod_cast zpow_natCast g 4
  have hmem : g ^ (4 : ℤ) ∈ Subgroup.centralizer (M : Set G) := by
    rw [h4, zpow_add, zpow_mul, zpow_mul, hgo, one_zpow, mul_one, h12z]
    exact Subgroup.zpow_mem _ h12 A
  rw [h4z] at hmem
  exact hmem

end CFSG.HardMathSupport.Solomon.Coordinator.I28_8.Th1J1
