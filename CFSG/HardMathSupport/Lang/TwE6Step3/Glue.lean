module

public import CFSG.LieType.SeitzGeneration.HyperEx

public section

namespace CFSG.HardMathSupport.Lang.TwE6Step3

open CFSG.Open CFSG.LieType.SeitzGeneration

theorem exists_zpow_mul_zpow_of_mem_closure_pair {Y : Type*} [Group Y] {y e : Y}
    (hye : y * e = e * y) {z : Y} (hz : z ∈ Subgroup.closure ({y, e} : Set Y)) :
    ∃ i j : ℤ, z = y ^ i * e ^ j := by
  have hc : Commute y e := hye
  induction hz using Subgroup.closure_induction with
  | mem x hx =>
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact ⟨1, 0, by simp⟩
    · exact ⟨0, 1, by simp⟩
  | one => exact ⟨0, 0, by simp⟩
  | mul a b _ _ ha hb =>
    obtain ⟨i, j, rfl⟩ := ha
    obtain ⟨k, l, rfl⟩ := hb
    refine ⟨i + k, j + l, ?_⟩
    rw [zpow_add, zpow_add]
    have h1 : Commute (e ^ j) (y ^ k) := (hc.symm.zpow_left j).zpow_right k
    calc y ^ i * e ^ j * (y ^ k * e ^ l) = y ^ i * (e ^ j * y ^ k) * e ^ l := by group
      _ = y ^ i * (y ^ k * e ^ j) * e ^ l := by rw [h1.eq]
      _ = y ^ i * y ^ k * (e ^ j * e ^ l) := by group
  | inv a _ ha =>
    obtain ⟨i, j, rfl⟩ := ha
    refine ⟨-i, -j, ?_⟩
    have h1 : Commute (y ^ i) (e ^ j) := (hc.zpow_left i).zpow_right j
    rw [mul_inv_rev, zpow_neg, zpow_neg, h1.inv_inv.eq]

theorem card_closure_pair_le_sq {Y : Type*} [Group Y] {p : ℕ} [NeZero p] {y e : Y}
    (hye : y * e = e * y) (hy : y ^ p = 1) (he : e ^ p = 1) :
    Nat.card (Subgroup.closure ({y, e} : Set Y)) ≤ p ^ 2 := by
  set C := Subgroup.closure ({y, e} : Set Y)
  have hyC : y ∈ C := Subgroup.subset_closure (by simp)
  have heC : e ∈ C := Subgroup.subset_closure (by simp)
  have hf : Function.Surjective (fun ij : Fin p × Fin p =>
      (⟨y ^ (ij.1 : ℕ) * e ^ (ij.2 : ℕ), C.mul_mem (C.pow_mem hyC _) (C.pow_mem heC _)⟩ : C)) := by
    rintro ⟨z, hz⟩
    obtain ⟨i, j, rfl⟩ := exists_zpow_mul_zpow_of_mem_closure_pair hye hz
    have hp0 : (0 : ℤ) < p := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne p)
    have hmod : ∀ (x : Y), x ^ p = 1 → ∀ k : ℤ, x ^ k = x ^ (k % (p : ℤ)).toNat := by
      intro x hx k
      have h1 : x ^ k = x ^ (k % (p : ℤ)) := by
        conv_lhs => rw [← Int.emod_add_mul_ediv k p]
        rw [zpow_add, zpow_mul, zpow_natCast, hx, one_zpow, mul_one]
      rw [h1, ← zpow_natCast, Int.toNat_of_nonneg (Int.emod_nonneg _ hp0.ne')]
    refine ⟨(⟨(i % (p : ℤ)).toNat, ?_⟩, ⟨(j % (p : ℤ)).toNat, ?_⟩), ?_⟩
    · have := Int.emod_lt_of_pos i hp0
      have := Int.emod_nonneg i hp0.ne'
      omega
    · have := Int.emod_lt_of_pos j hp0
      have := Int.emod_nonneg j hp0.ne'
      omega
    · apply Subtype.ext
      simp only
      rw [← hmod y hy i, ← hmod e he j]
  have h1 := Nat.card_le_card_of_surjective _ hf
  simpa [Nat.card_eq_fintype_card, Fintype.card_prod, Fintype.card_fin, sq] using h1

theorem mem_hyperClosure_of_commute_pair {Y : Type*} [Group Y] {p : ℕ} [hp : Fact p.Prime]
    {E : Subgroup Y} (hE : IsElemAbelian p E) (hcard : Nat.card E = p ^ 3) {y e : Y}
    (hy : y ∈ E) (he : e ∈ E) (hy1 : y ≠ 1) (hey : e ∉ Subgroup.zpowers y) {k : Y}
    (hky : k * y = y * k) (hke : k * e = e * k) : k ∈ hyperClosure p ⊤ E := by
  classical
  have hFE : Subgroup.closure {y, e} ≤ E := by
    rw [Subgroup.closure_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    exacts [hy, he]
  have hye : y * e = e * y := congrArg Subtype.val (hE.1.is_comm.comm ⟨y, hy⟩ ⟨e, he⟩)
  have hyp : y ^ p = 1 := hE.2 y hy
  have hep : e ^ p = 1 := hE.2 e he
  have hfinE : Finite E := Nat.finite_of_card_ne_zero (by rw [hcard]; exact pow_ne_zero _ hp.out.ne_zero)
  have hcardF : Nat.card (Subgroup.closure ({y, e} : Set Y)) = p ^ 2 := by
    have hle := card_closure_pair_le_sq hye hyp hep
    have hzy : Nat.card (Subgroup.zpowers y) = p := by
      rw [Nat.card_zpowers, orderOf_eq_prime hyp hy1]
    have hlt : Subgroup.zpowers y < Subgroup.closure {y, e} := by
      refine lt_of_le_of_ne ?_ fun h => hey ?_
      · rw [Subgroup.zpowers_le]
        exact Subgroup.subset_closure (by simp)
      · rw [h]
        exact Subgroup.subset_closure (by simp)
    have : Finite (Subgroup.closure ({y, e} : Set Y)) :=
      Finite.of_injective (Subgroup.inclusion hFE) (Subgroup.inclusion_injective hFE)
    have hgt := Subgroup.card_lt_of_lt hlt
    have hdvd : Nat.card (Subgroup.closure ({y, e} : Set Y)) ∣ p ^ 3 := by
      rw [← hcard]
      exact Subgroup.card_dvd_of_le hFE
    obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow hp.out).mp hdvd
    rw [hk'] at hle hgt ⊢
    rw [hzy] at hgt
    have h2 : k ≤ 2 := (Nat.pow_le_pow_iff_right hp.out.one_lt).1 hle
    have h1 : 1 < k := by
      by_contra hk1
      push Not at hk1
      interval_cases k
      · simp at hgt
        exact absurd hgt (by have := hp.out.one_lt; omega)
      · simp at hgt
    have : k = 2 := by omega
    rw [this]
  refine Subgroup.subset_closure ⟨Subgroup.mem_top _, Subgroup.closure {y, e}, hFE, ?_, ?_⟩
  · have hmul := Subgroup.card_mul_index ((Subgroup.closure ({y, e} : Set Y)).subgroupOf E)
    have hsub : Nat.card ((Subgroup.closure ({y, e} : Set Y)).subgroupOf E) = p ^ 2 := by
      rw [← hcardF]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hFE).toEquiv
    rw [hsub, hcard] at hmul
    show ((Subgroup.closure ({y, e} : Set Y)).subgroupOf E).index = p
    have hp0 : 0 < p ^ 2 := pow_pos hp.out.pos 2
    have : p ^ 2 * ((Subgroup.closure ({y, e} : Set Y)).subgroupOf E).index = p ^ 2 * p := by
      rw [hmul]; ring
    exact Nat.eq_of_mul_eq_mul_left hp0 this
  · intro f hf
    have hc : Subgroup.closure {y, e} ≤ Subgroup.centralizer {k} := by
      rw [Subgroup.closure_le]
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
      rcases hx with rfl | rfl
      exacts [hky.symm, hke.symm]
    exact Subgroup.mem_centralizer_singleton_iff.1 (hc hf)

theorem exists_mem_not_mem_zpowers {Y : Type*} [Group Y] {p : ℕ} [hp : Fact p.Prime]
    {E : Subgroup Y} (hE : IsElemAbelian p E) (hcard : Nat.card E = p ^ 3) {y : Y} (hy : y ∈ E) :
    ∃ e ∈ E, e ∉ Subgroup.zpowers y := by
  by_contra h
  simp only [not_exists, not_and, not_not] at h
  have hEq : E = Subgroup.zpowers y := le_antisymm (fun e he => h e he) (Subgroup.zpowers_le.2 hy)
  have h1 : p ^ 3 = orderOf y := by rw [← hcard, hEq, Nat.card_zpowers]
  have h2 : orderOf y ∣ p := orderOf_dvd_of_pow_eq_one (hE.2 y hy)
  rw [← h1] at h2
  have h3 := Nat.le_of_dvd hp.out.pos h2
  have h4 : p ^ 1 < p ^ 3 := Nat.pow_lt_pow_right hp.out.one_lt (by norm_num)
  rw [pow_one] at h4
  omega

theorem exists_mem_ker_not_mem_zpowers {Y : Type*} [Group Y] {p : ℕ} [hp : Fact p.Prime]
    {E : Subgroup Y} (hE : IsElemAbelian p E) (hcard : Nat.card E = p ^ 3) {M : Type*} [Field M]
    (χ : E →* Mˣ) {y : Y} (hy : y ∈ E) :
    ∃ e : E, (e : Y) ∉ Subgroup.zpowers y ∧ χ e = 1 := by
  classical
  have hfinE : Finite E :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; exact pow_ne_zero _ hp.out.ne_zero)
  have hpE : ∀ x : E, x ^ p = 1 := fun x => Subtype.ext (by simpa using hE.2 x x.2)
  have hrange : χ.range ≤ rootsOfUnity p M := by
    rintro _ ⟨x, rfl⟩
    rw [mem_rootsOfUnity, ← map_pow, hpE x, map_one]
  have hcr : Nat.card χ.range ≤ p := by
    have : NeZero p := ⟨hp.out.ne_zero⟩
    have : Finite (rootsOfUnity p M) := inferInstance
    exact (Subgroup.card_le_of_le hrange).trans (card_rootsOfUnity M p)
  have hmul := Subgroup.card_mul_index χ.ker
  rw [Subgroup.index_ker, hcard] at hmul
  have hker : p ^ 2 ≤ Nat.card χ.ker := by
    by_contra h
    push Not at h
    have h1 : Nat.card χ.ker * Nat.card χ.range < p ^ 2 * p := by
      calc Nat.card χ.ker * Nat.card χ.range ≤ Nat.card χ.ker * p := Nat.mul_le_mul_left _ hcr
        _ < p ^ 2 * p := Nat.mul_lt_mul_of_pos_right h hp.out.pos
    rw [hmul] at h1
    have : p ^ 3 = p ^ 2 * p := by ring
    omega
  set y' : E := ⟨y, hy⟩
  have hy'p : Nat.card (Subgroup.zpowers y') ≤ p := by
    rw [Nat.card_zpowers]
    exact Nat.le_of_dvd hp.out.pos (orderOf_dvd_of_pow_eq_one (hpE y'))
  have hnle : ¬ χ.ker ≤ Subgroup.zpowers y' := by
    intro hle
    have h1 := Subgroup.card_le_of_le hle
    have h2 : p < p ^ 2 := by
      have := Nat.pow_lt_pow_right hp.out.one_lt (show 1 < 2 by norm_num)
      simpa using this
    omega
  obtain ⟨e, hek, hey⟩ := Set.not_subset.1 hnle
  refine ⟨e, fun h => hey ?_, hek⟩
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 h
  exact Subgroup.mem_zpowers_iff.2 ⟨k, Subtype.ext (by simpa using hk)⟩


end CFSG.HardMathSupport.Lang.TwE6Step3
