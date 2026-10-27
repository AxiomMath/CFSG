module

public import CFSG.CharacterTheory.Semidihedral.NormalForm
public import CFSG.CharacterTheory.TwoRankLowerBound.CharacterBasis
public import CFSG.LocalAnalysis.LyonsUnitaryFour.FiveColumns.FourierIntegrality

public noncomputable section

open scoped BigOperators

namespace CFSG.Semidihedral.Principal

open CFSG.Open CFSG.TwoRankLowerBound.Helpers

universe u

@[expose] def cyclicRoot (M : ℕ) : ℂ := Complex.exp (2 * Real.pi * Complex.I / M)

theorem cyclicRoot_isPrimitiveRoot {M : ℕ} (hM : 0 < M) : IsPrimitiveRoot (cyclicRoot M) M :=
  Complex.isPrimitiveRoot_exp M hM.ne'

theorem cyclicRoot_ne_zero (M : ℕ) : cyclicRoot M ≠ 0 := Complex.exp_ne_zero _

theorem cyclicRoot_pow_self (M : ℕ) : cyclicRoot M ^ M = 1 := by
  rcases Nat.eq_zero_or_pos M with rfl | hM
  · simp
  · exact (cyclicRoot_isPrimitiveRoot hM).pow_eq_one

theorem cyclicRoot_zpow_congr {M : ℕ} {x y : ℤ} (h : x ≡ y [ZMOD M]) :
    cyclicRoot M ^ x = cyclicRoot M ^ y := by
  obtain ⟨k, hk⟩ := h.symm.dvd
  rw [show x = y + M * k by linarith, zpow_add₀ (cyclicRoot_ne_zero M), zpow_mul, zpow_natCast,
    cyclicRoot_pow_self, one_zpow, mul_one]

theorem cyclicRoot_pow_half {M : ℕ} (hM : 0 < M) (hM2 : Even M) : cyclicRoot M ^ (M / 2) = -1 := by
  have h2 : 2 ∣ M := even_iff_two_dvd.mp hM2
  have hroot := (cyclicRoot_isPrimitiveRoot hM).pow_of_dvd (p := M / 2) (by omega)
    (Nat.div_dvd_of_dvd h2)
  rw [Nat.div_div_self h2 hM.ne'] at hroot
  exact hroot.eq_neg_one_of_two_right

theorem cyclicRoot_conj (M : ℕ) : starRingEnd ℂ (cyclicRoot M) = (cyclicRoot M)⁻¹ := by
  rcases Nat.eq_zero_or_pos M with rfl | hM
  · simp [cyclicRoot]
  · have hnorm : ‖cyclicRoot M‖ = 1 := (cyclicRoot_isPrimitiveRoot hM).norm'_eq_one hM.ne'
    rw [Complex.inv_def, Complex.normSq_eq_norm_sq, hnorm]
    simp

theorem sum_range_cyclicRoot_zpow {M : ℕ} (hM : 0 < M) (k : ℤ) :
    ∑ j ∈ Finset.range M, cyclicRoot M ^ (k * j) = if (M : ℤ) ∣ k then (M : ℂ) else 0 := by
  have hζ := cyclicRoot_isPrimitiveRoot hM
  have hpow : ∀ j : ℕ, cyclicRoot M ^ (k * j) = (cyclicRoot M ^ k) ^ j := fun j => by
    rw [zpow_mul, zpow_natCast]
  simp_rw [hpow]
  split_ifs with hk
  · rw [(hζ.zpow_eq_one_iff_dvd k).mpr hk]
    simp
  · have hne : cyclicRoot M ^ k ≠ 1 := fun h => hk ((hζ.zpow_eq_one_iff_dvd k).mp h)
    have hM' : (cyclicRoot M ^ k) ^ M = 1 := by
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, cyclicRoot_pow_self,
        one_zpow]
    have hgeom := geom_sum_mul (cyclicRoot M ^ k) M
    rw [hM', sub_self] at hgeom
    exact (mul_eq_zero.mp hgeom).resolve_right (sub_ne_zero.mpr hne)

@[expose] def cyclicMultiplicity {G : Type*} [Monoid G] (f : G → ℂ) (g : G) (M : ℕ) (j : ℤ) :
    ℂ :=
  (M : ℂ)⁻¹ * ∑ v ∈ Finset.range M, f (g ^ v) * cyclicRoot M ^ (-(j * v))

theorem cyclicMultiplicity_congr {G : Type*} [Monoid G] (f : G → ℂ) (g : G) (M : ℕ) {j k : ℤ}
    (h : j ≡ k [ZMOD M]) : cyclicMultiplicity f g M j = cyclicMultiplicity f g M k := by
  unfold cyclicMultiplicity
  congr 1
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [cyclicRoot_zpow_congr ((h.mul_right (v : ℤ)).neg)]

theorem cyclicMultiplicity_natural {G : Type*} [Group G] (data : FiniteComplexRepresentation G)
    (g : G) {M : ℕ} (hM : 0 < M) (hg : g ^ M = 1) (j : ℤ) :
    ∃ m : ℕ, cyclicMultiplicity data.character g M j = m := by
  let u : ℂˣ := Units.mk0 (cyclicRoot M ^ j) (zpow_ne_zero _ (cyclicRoot_ne_zero M))
  have hu : u ^ M = 1 := by
    ext
    simp only [u, Units.val_pow_eq_pow_val, Units.val_mk0, Units.val_one]
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, cyclicRoot_pow_self,
      one_zpow]
  have hρ : data.representation g ^ M = 1 := by rw [← map_pow, hg, map_one]
  obtain ⟨m, hm⟩ := CFSG.LyonsUnitaryFour.character_fourier_natural data g M hM hρ u hu
  refine ⟨m, ?_⟩
  rw [← hm]
  unfold cyclicMultiplicity
  congr 1
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [mul_comm]
  congr 1
  simp only [u, Units.val_inv_eq_inv_val, Units.val_mk0]
  rw [← zpow_natCast, ← zpow_neg, ← zpow_mul, neg_mul]

theorem cyclicMultiplicity_inversion {G : Type*} [Monoid G] (f : G → ℂ) (g : G) {M : ℕ}
    (hM : 0 < M) {w : ℕ} (hw : w < M) :
    f (g ^ w) =
      ∑ j ∈ Finset.range M, cyclicMultiplicity f g M j * cyclicRoot M ^ ((j : ℤ) * w) := by
  unfold cyclicMultiplicity
  simp_rw [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  have hinner : ∀ v ∈ Finset.range M, ∑ j ∈ Finset.range M,
      (M : ℂ)⁻¹ * (f (g ^ v) * cyclicRoot M ^ (-((j : ℤ) * v))) * cyclicRoot M ^ ((j : ℤ) * w) =
      (M : ℂ)⁻¹ * f (g ^ v) * ∑ j ∈ Finset.range M, cyclicRoot M ^ (((w : ℤ) - v) * j) := by
    intro v _
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [show ((w : ℤ) - v) * j = -((j : ℤ) * v) + (j : ℤ) * w by ring,
      zpow_add₀ (cyclicRoot_ne_zero M)]
    ring
  rw [Finset.sum_congr rfl hinner]
  simp_rw [sum_range_cyclicRoot_zpow hM]
  rw [Finset.sum_eq_single w]
  · have hM0 : (M : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hM.ne'
    rw [sub_self, ite_eq_left (dvd_zero _)]
    field_simp
  · intro v hv hvw
    have hv' := Finset.mem_range.mp hv
    have hndvd : ¬(M : ℤ) ∣ (w : ℤ) - v := by
      rintro ⟨c, hc⟩
      have hc0 : c = 0 := by
        rcases lt_trichotomy c 0 with h | h | h
        · nlinarith
        · exact h
        · nlinarith
      rw [hc0, mul_zero, sub_eq_zero] at hc
      exact hvw (by exact_mod_cast hc.symm)
    rw [ite_eq_right hndvd, mul_zero]
  · intro h
    exact absurd (Finset.mem_range.mpr hw) h

@[expose] def cyclicLinearCharacter {G : Type*} [Group G] (g : G) (M : ℕ) (j : ℤ) :
    Subgroup.zpowers g → ℂ :=
  fun x => cyclicRoot M ^ (j * Classical.choose (Subgroup.mem_zpowers_iff.mp x.2))

theorem cyclicLinearCharacter_zpow {G : Type*} [Group G] {g : G} {M : ℕ} (hg : orderOf g = M)
    (j k : ℤ) :
    cyclicLinearCharacter g M j ⟨g ^ k, Subgroup.zpow_mem_zpowers g k⟩ =
      cyclicRoot M ^ (j * k) := by
  unfold cyclicLinearCharacter
  apply cyclicRoot_zpow_congr
  have hspec := Classical.choose_spec
    (Subgroup.mem_zpowers_iff.mp (Subgroup.zpow_mem_zpowers g k))
  have hmod := zpow_eq_zpow_iff_modEq.mp hspec
  rw [hg] at hmod
  exact hmod.mul_left j

theorem cyclicLinearCharacter_mul {G : Type*} [Group G] {g : G} {M : ℕ} (hg : orderOf g = M)
    (j : ℤ) (x y : Subgroup.zpowers g) :
    cyclicLinearCharacter g M j (x * y) =
      cyclicLinearCharacter g M j x * cyclicLinearCharacter g M j y := by
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp x.2
  obtain ⟨l, hl⟩ := Subgroup.mem_zpowers_iff.mp y.2
  have hx : x = ⟨g ^ k, Subgroup.zpow_mem_zpowers g k⟩ := Subtype.ext hk.symm
  have hy : y = ⟨g ^ l, Subgroup.zpow_mem_zpowers g l⟩ := Subtype.ext hl.symm
  have hxy : x * y = ⟨g ^ (k + l), Subgroup.zpow_mem_zpowers g (k + l)⟩ := by
    rw [hx, hy]
    exact Subtype.ext (zpow_add g k l).symm
  rw [hxy, hx, hy, cyclicLinearCharacter_zpow hg, cyclicLinearCharacter_zpow hg,
    cyclicLinearCharacter_zpow hg, mul_add, zpow_add₀ (cyclicRoot_ne_zero M)]

theorem characterPairing_zpowers_cyclicLinearCharacter {G : Type*} [Group G] [Fintype G]
    (f : G → ℂ) {g : G} {M : ℕ} (hg : orderOf g = M) (j : ℤ) :
    characterPairing (fun x : Subgroup.zpowers g => f x) (cyclicLinearCharacter g M j) =
      cyclicMultiplicity f g M j := by
  have hfin : IsOfFinOrder g := isOfFinOrder_of_finite g
  unfold characterPairing cyclicMultiplicity
  rw [Nat.card_zpowers, hg]
  congr 1
  rw [← Equiv.sum_comp (finEquivZPowers hfin)]
  subst hg
  rw [← Fin.sum_univ_eq_sum_range (fun v => f (g ^ v) * cyclicRoot (orderOf g) ^ (-(j * v)))]
  refine Fintype.sum_congr _ _ fun i => ?_
  rw [finEquivZPowers_apply]
  have hinv : (⟨g ^ (i : ℕ), Subgroup.npow_mem_zpowers g i⟩ : Subgroup.zpowers g)⁻¹ =
      ⟨g ^ (-((i : ℕ) : ℤ)), Subgroup.zpow_mem_zpowers g _⟩ :=
    Subtype.ext (by simp [zpow_neg])
  simp only
  rw [hinv, cyclicLinearCharacter_zpow rfl, mul_neg]

theorem cyclicLinearCharacter_inv {G : Type*} [Group G] {g : G} {M : ℕ} (hg : orderOf g = M)
    (j : ℤ) (x : Subgroup.zpowers g) :
    cyclicLinearCharacter g M j x⁻¹ = starRingEnd ℂ (cyclicLinearCharacter g M j x) := by
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp x.2
  have hx : x = ⟨g ^ k, Subgroup.zpow_mem_zpowers g k⟩ := Subtype.ext hk.symm
  have hxinv : x⁻¹ = ⟨g ^ (-k), Subgroup.zpow_mem_zpowers g (-k)⟩ := by
    rw [hx]
    exact Subtype.ext (zpow_neg g k).symm
  rw [hxinv, hx, cyclicLinearCharacter_zpow hg, cyclicLinearCharacter_zpow hg, map_zpow₀,
    cyclicRoot_conj, inv_zpow', mul_neg]

theorem cyclicMultiplicity_eq_inner {G : Type*} [Group G] [Fintype G] (f : G → ℂ) {g : G}
    {M : ℕ} (hg : orderOf g = M) (j : ℤ) :
    cyclicMultiplicity f g M j = (Nat.card (Subgroup.zpowers g) : ℂ)⁻¹ *
      ∑ x : Subgroup.zpowers g, f x * starRingEnd ℂ (cyclicLinearCharacter g M j x) := by
  rw [← characterPairing_zpowers_cyclicLinearCharacter f hg j]
  unfold characterPairing
  congr 1
  refine Fintype.sum_congr _ _ fun x => ?_
  rw [cyclicLinearCharacter_inv hg]

theorem cyclicMultiplicity_mul_of_conj {G : Type*} [Group G] (f : G → ℂ)
    (hf : ∀ x y : G, f (y * x * y⁻¹) = f x) {g s : G} {M a : ℕ} (hM : 0 < M) (hg : g ^ M = 1)
    (hs : s * g * s⁻¹ = g ^ a) (ha : a * a % M = 1 % M) (j : ℤ) :
    cyclicMultiplicity f g M (a * j) = cyclicMultiplicity f g M j := by
  unfold cyclicMultiplicity
  congr 1
  have hinv : ∀ v ∈ Finset.range M, a * (a * v % M) % M = v := by
    intro v hv
    rw [Finset.mem_range] at hv
    rw [Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod, ← mul_assoc, Nat.mul_mod, ha, Nat.mod_mul_mod,
      one_mul, Nat.mod_mod, Nat.mod_eq_of_lt hv]
  refine Finset.sum_nbij' (fun v => a * v % M) (fun v => a * v % M) ?_ ?_ hinv hinv ?_
  · intro v _
    exact Finset.mem_range.mpr (Nat.mod_lt _ hM)
  · intro v _
    exact Finset.mem_range.mpr (Nat.mod_lt _ hM)
  · intro v _
    have hpow : g ^ (a * v % M) = s * g ^ v * s⁻¹ := by
      rw [← pow_eq_pow_mod _ hg, pow_mul, ← hs, conj_pow]
    rw [hpow, hf]
    congr 1
    apply cyclicRoot_zpow_congr
    have hmod : ((a * v % M : ℕ) : ℤ) ≡ (a : ℤ) * v [ZMOD M] := by
      have := Nat.mod_modEq (a * v) M
      exact_mod_cast this
    rw [show (a : ℤ) * j * v = j * (a * v) by ring]
    exact ((hmod.mul_left j).neg).symm

theorem sum_range_two_mul_neg_one_pow_mul (L : ℤ → ℤ) (N : ℕ) :
    ∑ j ∈ Finset.range (2 * N), (-1 : ℤ) ^ j * L j =
      ∑ l ∈ Finset.range N, L (2 * l) - ∑ l ∈ Finset.range N, L (2 * l + 1) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [show 2 * (N + 1) = 2 * N + 1 + 1 by ring, Finset.sum_range_succ, Finset.sum_range_succ,
      ih, Finset.sum_range_succ, Finset.sum_range_succ, pow_succ, pow_mul, neg_one_sq, one_pow]
    push_cast
    ring

theorem sum_range_even_reflect_columns (L : ℤ → ℤ) {K : ℕ} (hK : 1 ≤ K)
    (hsymm : ∀ l : ℕ, l ≤ 2 * K → L (2 * ((2 * K - l : ℕ) : ℤ)) = L (2 * l)) :
    ∑ l ∈ Finset.range (2 * K), L (2 * l) =
      L 0 + L (2 * K) + 2 * ∑ l ∈ Finset.Icc 1 (K - 1), L (2 * l) := by
  rw [← Finset.sum_range_add_sum_Ico _ (show K + 1 ≤ 2 * K by omega), Finset.sum_range_succ,
    Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (show 0 < K by omega)]
  have hIcc : Finset.Icc 1 (K - 1) = Finset.Ico 1 K := by
    ext l
    simp only [Finset.mem_Icc, Finset.mem_Ico]
    omega
  have hrefl : ∑ l ∈ Finset.Ico (K + 1) (2 * K), L (2 * l) =
      ∑ l ∈ Finset.Ico 1 K, L (2 * l) := by
    refine Finset.sum_nbij' (fun l => 2 * K - l) (fun l => 2 * K - l) ?_ ?_ ?_ ?_ ?_
    · intro l hl
      simp only [Finset.mem_Ico] at hl ⊢
      omega
    · intro l hl
      simp only [Finset.mem_Ico] at hl ⊢
      omega
    · intro l hl
      simp only [Finset.mem_Ico] at hl
      omega
    · intro l hl
      simp only [Finset.mem_Ico] at hl
      omega
    · intro l hl
      simp only [Finset.mem_Ico] at hl
      have h := hsymm (2 * K - l) (by omega)
      rw [show 2 * K - (2 * K - l) = l by omega] at h
      exact h
  rw [hrefl, hIcc]
  push_cast
  ring

theorem odd_mod_of_odd_of_even {y M : ℕ} (hy : Odd y) (hM : Even M) : Odd (y % M) := by
  have h1 := Nat.mod_add_div y M
  have h2 : Even (M * (y / M)) := hM.mul_right _
  rw [← h1] at hy
  exact (Nat.odd_add.mp hy).mpr h2

structure IsOddResidueTransversal {M : ℕ} (a : ZMod M) (I : Finset (ZMod M)) : Prop where
  one_mem : 1 ∈ I
  odd : ∀ j ∈ I, Odd j.val
  pair : ∀ j : ZMod M, Odd j.val → (({j, a * j} : Finset (ZMod M)) ∩ I).card = 1

theorem card_pair_inter_eq_one {α : Type*} [DecidableEq α] {x y : α} {I : Finset α}
    (h : x ∈ I ↔ y ∉ I) : (({x, y} : Finset α) ∩ I).card = 1 := by
  by_cases hx : x ∈ I
  · have hy := h.mp hx
    rw [show ({x, y} ∩ I : Finset α) = {x} by
      ext z
      simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨rfl | rfl, hz⟩
        · rfl
        · exact absurd hz hy
      · rintro rfl
        exact ⟨Or.inl rfl, hx⟩]
    exact Finset.card_singleton x
  · have hy : y ∈ I := by
      by_contra hy
      exact hx (h.mpr hy)
    rw [show ({x, y} ∩ I : Finset α) = {y} by
      ext z
      simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨rfl | rfl, hz⟩
        · exact absurd hz hx
        · rfl
      · rintro rfl
        exact ⟨Or.inr rfl, hy⟩]
    exact Finset.card_singleton y

theorem IsOddResidueTransversal.of_iff {M : ℕ} {a : ZMod M} {I : Finset (ZMod M)} (h1 : 1 ∈ I)
    (hodd : ∀ j ∈ I, Odd j.val) (hiff : ∀ j : ZMod M, Odd j.val → (j ∈ I ↔ a * j ∉ I)) :
    IsOddResidueTransversal a I :=
  ⟨h1, hodd, fun j hj => card_pair_inter_eq_one (hiff j hj)⟩

theorem isOddResidueTransversal_mod_four {M K : ℕ} [NeZero M] (hMK : M = 4 * K) (hK : Even K)
    (hK2 : 2 ≤ K) {a : ZMod M} (ha : a.val = 2 * K - 1) :
    IsOddResidueTransversal a (Finset.univ.filter fun x : ZMod M => x.val % 4 = 1) := by
  have hval4 : ∀ x : ZMod M, (a * x).val % 4 = 3 * (x.val % 4) % 4 := by
    intro x
    obtain ⟨k, hk⟩ := hK
    rw [ZMod.val_mul, ha, Nat.mod_mod_of_dvd _ (show 4 ∣ M from ⟨K, by omega⟩), Nat.mul_mod,
      show (2 * K - 1) % 4 = 3 by omega]
  have hmem : ∀ x : ZMod M,
      x ∈ (Finset.univ.filter fun x : ZMod M => x.val % 4 = 1) ↔ x.val % 4 = 1 := by
    intro x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  refine IsOddResidueTransversal.of_iff ?_ ?_ ?_
  · have : Fact (1 < M) := ⟨by omega⟩
    rw [hmem, ZMod.val_one]
  · intro j hj
    rw [hmem] at hj
    exact Nat.odd_iff.mpr (by omega)
  · intro j hj
    have hj2 := Nat.odd_iff.mp hj
    have h := hval4 j
    rw [hmem, hmem]
    omega

theorem sum_range_odd_transversal_columns {M K : ℕ} [NeZero M] (hMK : M = 4 * K) (hK : Even K)
    (hK2 : 2 ≤ K) (L : ℤ → ℤ) (hper : ∀ x y : ℤ, x ≡ y [ZMOD M] → L x = L y)
    (htwist : ∀ j : ℤ, L ((2 * K - 1 : ℤ) * j) = L j) (a : ZMod M) (ha : a.val = 2 * K - 1)
    (I : Finset (ZMod M)) (hI_odd : ∀ j ∈ I, Odd j.val)
    (hI_pair : ∀ j : ZMod M, Odd j.val → (({j, a * j} : Finset (ZMod M)) ∩ I).card = 1) :
    ∑ l ∈ Finset.range (2 * K), L (2 * l + 1) = 2 * ∑ j ∈ I, L j.val ∧ I.card = K := by
  classical
  have hMeven : Even M := ⟨2 * K, by omega⟩
  have hacast : a = ((2 * K - 1 : ℕ) : ZMod M) := by
    rw [← ha, ZMod.natCast_zmod_val]
  have haa : a * a = 1 := by
    obtain ⟨k, rfl⟩ : ∃ k, K = k + 1 := ⟨K - 1, by omega⟩
    have hsq : (2 * (k + 1) - 1) * (2 * (k + 1) - 1) = M * k + 1 := by
      rw [hMK, show 2 * (k + 1) - 1 = 2 * k + 1 by omega]
      ring
    rw [hacast, ← Nat.cast_mul, hsq]
    push_cast
    rw [ZMod.natCast_self, zero_mul, zero_add]
  have hval_mul : ∀ x : ZMod M, (a * x).val = (2 * K - 1) * x.val % M := by
    intro x
    rw [ZMod.val_mul, ha]
  have hodd_mul : ∀ x : ZMod M, Odd x.val → Odd (a * x).val := by
    intro x hx
    rw [hval_mul]
    exact odd_mod_of_odd_of_even (Nat.odd_mul.mpr ⟨⟨K - 1, by omega⟩, hx⟩) hMeven
  have hne : ∀ x : ZMod M, Odd x.val → x ≠ a * x := by
    intro x hx hxa
    have hv : x.val = (2 * K - 1) * x.val % M := by rw [← hval_mul, ← hxa]
    have hmod : (2 * K - 1) * x.val ≡ x.val [MOD M] := by
      unfold Nat.ModEq
      rw [← hv, Nat.mod_eq_of_lt (ZMod.val_lt x)]
    have hle : x.val ≤ (2 * K - 1) * x.val := Nat.le_mul_of_pos_left _ (by omega)
    have hdvd := (Nat.modEq_iff_dvd' hle).mp hmod.symm
    rw [show (2 * K - 1) * x.val - x.val = 2 * ((K - 1) * x.val) by
      rw [show 2 * K - 1 = 2 * (K - 1) + 1 by omega]
      rw [add_mul, one_mul, Nat.add_sub_cancel, mul_assoc]] at hdvd
    have hdvd' : 2 * (2 * K) ∣ 2 * ((K - 1) * x.val) := by
      rw [show 2 * (2 * K) = M by omega]
      exact hdvd
    have h2 := Nat.dvd_of_mul_dvd_mul_left (by norm_num) hdvd'
    have h3 : 2 ∣ (K - 1) * x.val := (Dvd.intro K rfl).trans h2
    have hodd : Odd ((K - 1) * x.val) := Nat.odd_mul.mpr ⟨by
      obtain ⟨k, hk⟩ := hK
      exact ⟨k - 1, by omega⟩, hx⟩
    exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h3)
  have hLa : ∀ x : ZMod M, L ((a * x).val : ℤ) = L (x.val : ℤ) := by
    intro x
    rw [← htwist (x.val : ℤ)]
    apply hper
    rw [← ZMod.intCast_eq_intCast_iff]
    push_cast
    rw [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val, hacast]
    push_cast [show 1 ≤ 2 * K by omega]
    ring
  set O : Finset (ZMod M) := Finset.univ.filter (fun x : ZMod M => Odd x.val) with hO
  have hval : ∀ l, l < 2 * K → (((2 * l + 1 : ℕ) : ZMod M)).val = 2 * l + 1 := fun l hl =>
    ZMod.val_cast_of_lt (by omega)
  have hmemO : ∀ x : ZMod M, x ∈ O ↔ Odd x.val := by
    intro x
    simp only [hO, Finset.mem_filter, Finset.mem_univ, true_and]
  have hbij_sum : ∑ l ∈ Finset.range (2 * K), L (2 * l + 1) = ∑ x ∈ O, L x.val := by
    refine Finset.sum_nbij' (fun l => ((2 * l + 1 : ℕ) : ZMod M)) (fun x => x.val / 2)
      ?_ ?_ ?_ ?_ ?_
    · intro l hl
      rw [Finset.mem_range] at hl
      rw [hmemO, hval l hl]
      exact odd_two_mul_add_one l
    · intro x hx
      rw [hmemO] at hx
      have := ZMod.val_lt x
      exact Finset.mem_range.mpr (by omega)
    · intro l hl
      rw [Finset.mem_range] at hl
      show (((2 * l + 1 : ℕ) : ZMod M)).val / 2 = l
      rw [hval l hl]
      omega
    · intro x hx
      rw [hmemO] at hx
      obtain ⟨k, hk⟩ := hx
      show ((2 * (x.val / 2) + 1 : ℕ) : ZMod M) = x
      rw [show 2 * (x.val / 2) + 1 = x.val by omega, ZMod.natCast_zmod_val]
    · intro l hl
      rw [Finset.mem_range] at hl
      show L (2 * l + 1) = L (((2 * l + 1 : ℕ) : ZMod M)).val
      rw [hval l hl]
      push_cast
      rfl
  have hcardO : O.card = 2 * K := by
    have h := Finset.card_nbij' (s := Finset.range (2 * K)) (t := O)
      (fun l => ((2 * l + 1 : ℕ) : ZMod M)) (fun x => x.val / 2) ?_ ?_ ?_ ?_
    · rw [← h, Finset.card_range]
    · intro l hl
      rw [Finset.mem_coe, Finset.mem_range] at hl
      rw [Finset.mem_coe, hmemO, hval l hl]
      exact odd_two_mul_add_one l
    · intro x hx
      rw [Finset.mem_coe, hmemO] at hx
      have := ZMod.val_lt x
      show x.val / 2 ∈ (Finset.range (2 * K) : Set ℕ)
      exact Finset.mem_coe.mpr (Finset.mem_range.mpr (by omega))
    · intro l hl
      rw [Finset.mem_coe, Finset.mem_range] at hl
      show (((2 * l + 1 : ℕ) : ZMod M)).val / 2 = l
      rw [hval l hl]
      omega
    · intro x hx
      rw [Finset.mem_coe, hmemO] at hx
      obtain ⟨k, hk⟩ := hx
      show ((2 * (x.val / 2) + 1 : ℕ) : ZMod M) = x
      rw [show 2 * (x.val / 2) + 1 = x.val by omega, ZMod.natCast_zmod_val]
  have hIO : I ⊆ O := fun x hx => (hmemO x).mpr (hI_odd x hx)
  have hinj : Function.Injective (fun x : ZMod M => a * x) := by
    intro x y hxy
    simp only at hxy
    have := congrArg (fun z => a * z) hxy
    simp only [← mul_assoc, haa, one_mul] at this
    exact this
  have hdiff : O \ I = I.image (fun x => a * x) := by
    ext y
    simp only [Finset.mem_sdiff, Finset.mem_image, hmemO]
    constructor
    · rintro ⟨hy, hyI⟩
      have hc := hI_pair y hy
      have hay : a * y ∈ I := by
        by_contra hnot
        have hempty : ({y, a * y} ∩ I : Finset (ZMod M)) = ∅ := by
          ext z
          simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton,
            Finset.notMem_empty, iff_false, not_and]
          rintro (rfl | rfl) <;> assumption
        rw [hempty, Finset.card_empty] at hc
        exact absurd hc (by norm_num)
      exact ⟨a * y, hay, by rw [← mul_assoc, haa, one_mul]⟩
    · rintro ⟨x, hx, rfl⟩
      have hxodd := hI_odd x hx
      refine ⟨hodd_mul x hxodd, fun haxI => ?_⟩
      have hc := hI_pair x hxodd
      have hfull : ({x, a * x} ∩ I : Finset (ZMod M)) = {x, a * x} := by
        ext z
        simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton,
          and_iff_left_iff_imp]
        rintro (rfl | rfl) <;> assumption
      rw [hfull, Finset.card_pair (hne x hxodd)] at hc
      exact absurd hc (by norm_num)
  refine ⟨?_, ?_⟩
  · rw [hbij_sum, ← Finset.sum_sdiff hIO, hdiff, Finset.sum_image (hinj.injOn), two_mul]
    congr 1
    exact Finset.sum_congr rfl fun x _ => hLa x
  · have h := Finset.card_sdiff_add_card_eq_card hIO
    rw [hdiff, Finset.card_image_of_injective _ hinj, hcardO] at h
    omega

theorem signed_residue_column_identity {M K : ℕ} [NeZero M] (hMK : M = 4 * K) (hK : Even K)
    (hK2 : 2 ≤ K) (L : ℤ → ℤ) (hper : ∀ x y : ℤ, x ≡ y [ZMOD M] → L x = L y)
    (htwist : ∀ j : ℤ, L ((2 * K - 1 : ℤ) * j) = L j) (a : ZMod M) (ha : a.val = 2 * K - 1)
    (I : Finset (ZMod M)) (hI_odd : ∀ j ∈ I, Odd j.val)
    (hI_pair : ∀ j : ZMod M, Odd j.val → (({j, a * j} : Finset (ZMod M)) ∩ I).card = 1) :
    ∑ j ∈ Finset.range M, (-1 : ℤ) ^ j * L j =
      (2 * K : ℤ) * (L 0 - L 1) - (L 0 - L (2 * K)) -
        2 * ∑ l ∈ Finset.Icc 1 (K - 1), (L 0 - L (2 * l)) - 2 * ∑ j ∈ I, (L j.val - L 1) := by
  obtain ⟨hodd, hcard⟩ :=
    sum_range_odd_transversal_columns hMK hK hK2 L hper htwist a ha I hI_odd hI_pair
  have hsymm : ∀ l : ℕ, l ≤ 2 * K → L (2 * ((2 * K - l : ℕ) : ℤ)) = L (2 * l) := by
    intro l hl
    rw [← htwist (2 * l)]
    apply hper
    rw [Nat.cast_sub hl, Int.modEq_iff_dvd, hMK]
    exact ⟨(l : ℤ) - 1, by push_cast; ring⟩
  rw [show Finset.range M = Finset.range (2 * (2 * K)) by congr 1; omega,
    sum_range_two_mul_neg_one_pow_mul, sum_range_even_reflect_columns L (by omega) hsymm, hodd]
  simp only [Finset.sum_sub_distrib, Finset.sum_const, Nat.card_Icc, hcard, nsmul_eq_mul]
  rw [show K - 1 + 1 - 1 = K - 1 by omega, Nat.cast_sub (show 1 ≤ K by omega)]
  push_cast
  ring

theorem two_pow_dvd_sign_mul_sub_one {q m : ℕ} (hq3 : 3 ≤ q) (hq : Odd q) (hm : 2 ≤ m)
    (hval : 2 ^ padicValNat 2 (q ^ 2 - 1) = 2 ^ m) {ε : ℤ} (hε1 : q % 4 = 1 → ε = 1)
    (hε3 : q % 4 = 3 → ε = -1) : ((2 ^ (m - 1) : ℕ) : ℤ) ∣ ε * q - 1 := by
  have hdvd : 2 ^ m ∣ q ^ 2 - 1 := hval ▸ pow_padicValNat_dvd
  have hfac : q ^ 2 - 1 = (q - 1) * (q + 1) := by
    obtain ⟨k, rfl⟩ : ∃ k, q = k + 1 := ⟨q - 1, by omega⟩
    rw [Nat.add_sub_cancel]
    ring_nf
    omega
  rw [hfac] at hdvd
  have hm' : 2 ^ m = 2 ^ (m - 1) * 2 := by
    rw [← pow_succ, Nat.sub_add_cancel (by omega)]
  have hq4 : q % 4 = 1 ∨ q % 4 = 3 := by
    obtain ⟨k, rfl⟩ := hq
    omega
  rcases hq4 with h1 | h3
  · rw [hε1 h1, one_mul]
    obtain ⟨u, hu⟩ : ∃ u, q + 1 = 2 * u := ⟨(q + 1) / 2, by omega⟩
    have hu_odd : Odd u := ⟨(u - 1) / 2, by omega⟩
    rw [hu, hm', show (q - 1) * (2 * u) = (q - 1) * u * 2 by ring] at hdvd
    have h := Nat.dvd_of_mul_dvd_mul_right (by norm_num) hdvd
    have hcop : Nat.Coprime (2 ^ (m - 1)) u :=
      Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr hu_odd)
    have h' := hcop.dvd_of_dvd_mul_right h
    have hcast : ((q - 1 : ℕ) : ℤ) = (q : ℤ) - 1 := by push_cast [show 1 ≤ q by omega]; ring
    rw [← hcast]
    exact Int.natCast_dvd_natCast.mpr h'
  · rw [hε3 h3]
    obtain ⟨u, hu⟩ : ∃ u, q - 1 = 2 * u := ⟨(q - 1) / 2, by omega⟩
    have hu_odd : Odd u := ⟨(u - 1) / 2, by omega⟩
    rw [hu, hm', show 2 * u * (q + 1) = u * (q + 1) * 2 by ring] at hdvd
    have h := Nat.dvd_of_mul_dvd_mul_right (by norm_num) hdvd
    have hcop : Nat.Coprime (2 ^ (m - 1)) u :=
      Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr hu_odd)
    have h' := hcop.dvd_of_dvd_mul_left h
    have hcast : (-1 : ℤ) * q - 1 = -((q + 1 : ℕ) : ℤ) := by push_cast; ring
    rw [hcast, dvd_neg]
    exact Int.natCast_dvd_natCast.mpr h'

section Columns

variable {G : Type u} [Group G] [Fintype G]

@[expose] def multiplicityColumn (basis : FiniteIrreducibleCharacterBasis G) (g : G) (M : ℕ)
    (j : ℤ) (χ : basis.index) : ℤ :=
  ⌊(cyclicMultiplicity (basis.representation χ).character g M j).re⌋

theorem multiplicityColumn_eq_natural (basis : FiniteIrreducibleCharacterBasis G) {g : G}
    {M : ℕ} (hM : 0 < M) (hg : g ^ M = 1) (j : ℤ) (χ : basis.index) :
    ∃ m : ℕ, cyclicMultiplicity (basis.representation χ).character g M j = m ∧
      multiplicityColumn basis g M j χ = m := by
  obtain ⟨m, hm⟩ := cyclicMultiplicity_natural (basis.representation χ) g hM hg j
  refine ⟨m, hm, ?_⟩
  rw [multiplicityColumn, hm]
  simp

theorem multiplicityColumn_cast (basis : FiniteIrreducibleCharacterBasis G) {g : G} {M : ℕ}
    (hM : 0 < M) (hg : g ^ M = 1) (j : ℤ) (χ : basis.index) :
    ((multiplicityColumn basis g M j χ : ℤ) : ℂ) =
      cyclicMultiplicity (basis.representation χ).character g M j := by
  obtain ⟨m, hm, hcol⟩ := multiplicityColumn_eq_natural basis hM hg j χ
  rw [hcol, hm]
  push_cast
  rfl

theorem multiplicityColumn_nonneg (basis : FiniteIrreducibleCharacterBasis G) {g : G} {M : ℕ}
    (hM : 0 < M) (hg : g ^ M = 1) (j : ℤ) (χ : basis.index) :
    0 ≤ multiplicityColumn basis g M j χ := by
  obtain ⟨m, -, hcol⟩ := multiplicityColumn_eq_natural basis hM hg j χ
  rw [hcol]
  positivity

theorem multiplicityColumn_congr (basis : FiniteIrreducibleCharacterBasis G) (g : G) (M : ℕ)
    {j k : ℤ} (h : j ≡ k [ZMOD M]) :
    multiplicityColumn basis g M j = multiplicityColumn basis g M k := by
  funext χ
  unfold multiplicityColumn
  rw [cyclicMultiplicity_congr _ _ _ h]

theorem multiplicityColumn_mul_of_conj (basis : FiniteIrreducibleCharacterBasis G) {g s : G}
    {M a : ℕ} (hM : 0 < M) (hg : g ^ M = 1) (hs : s * g * s⁻¹ = g ^ a)
    (ha : a * a % M = 1 % M) (j : ℤ) :
    multiplicityColumn basis g M (a * j) = multiplicityColumn basis g M j := by
  funext χ
  unfold multiplicityColumn
  rw [cyclicMultiplicity_mul_of_conj _ (fun x y => Representation.char_conj _ x y) hM hg hs ha]

theorem character_half_pow_eq_signed_sum (basis : FiniteIrreducibleCharacterBasis G) {g : G}
    {M : ℕ} (hM : 0 < M) (hM2 : Even M) (hg : g ^ M = 1) (χ : basis.index) :
    (basis.representation χ).character (g ^ (M / 2)) =
      ((∑ j ∈ Finset.range M, (-1 : ℤ) ^ j * multiplicityColumn basis g M j χ : ℤ) : ℂ) := by
  have hpow : ∀ j : ℕ, cyclicRoot M ^ ((j : ℤ) * ((M / 2 : ℕ) : ℤ)) = (-1 : ℂ) ^ j := by
    intro j
    rw [mul_comm, zpow_mul, zpow_natCast, zpow_natCast, cyclicRoot_pow_half hM hM2]
  rw [cyclicMultiplicity_inversion (basis.representation χ).character g hM
    (show M / 2 < M by omega), Int.cast_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hpow, Int.cast_mul, Int.cast_pow, Int.cast_neg, Int.cast_one,
    multiplicityColumn_cast basis hM hg, mul_comm]

theorem character_central_column_identity (basis : FiniteIrreducibleCharacterBasis G) {g s : G}
    {M K : ℕ} [NeZero M] (hMK : M = 4 * K) (hK : Even K) (hK2 : 2 ≤ K) (hg : g ^ M = 1)
    (hs : s * g * s⁻¹ = g ^ (2 * K - 1)) (a : ZMod M) (ha : a.val = 2 * K - 1)
    (I : Finset (ZMod M)) (hI_odd : ∀ j ∈ I, Odd j.val)
    (hI_pair : ∀ j : ZMod M, Odd j.val → (({j, a * j} : Finset (ZMod M)) ∩ I).card = 1)
    (χ : basis.index) :
    (basis.representation χ).character (g ^ (2 * K)) =
      (((2 * K : ℤ) * (multiplicityColumn basis g M 0 χ - multiplicityColumn basis g M 1 χ) -
        (multiplicityColumn basis g M 0 χ - multiplicityColumn basis g M (2 * K) χ) -
        2 * ∑ l ∈ Finset.Icc 1 (K - 1),
          (multiplicityColumn basis g M 0 χ - multiplicityColumn basis g M (2 * l) χ) -
        2 * ∑ j ∈ I, (multiplicityColumn basis g M j.val χ - multiplicityColumn basis g M 1 χ) :
          ℤ) : ℂ) := by
  have hM : 0 < M := by omega
  have hsq : (2 * K - 1) * (2 * K - 1) % M = 1 % M := by
    obtain ⟨k, rfl⟩ : ∃ k, K = k + 1 := ⟨K - 1, by omega⟩
    rw [hMK, show 2 * (k + 1) - 1 = 2 * k + 1 by omega,
      show (2 * k + 1) * (2 * k + 1) = 1 + 4 * (k + 1) * k by ring, Nat.add_mul_mod_self_left]
  have htwist : ∀ j : ℤ, multiplicityColumn basis g M ((2 * K - 1 : ℤ) * j) χ =
      multiplicityColumn basis g M j χ := by
    intro j
    have h := congrFun (multiplicityColumn_mul_of_conj basis hM hg hs hsq j) χ
    rwa [Nat.cast_sub (show 1 ≤ 2 * K by omega), Nat.cast_mul, Nat.cast_ofNat,
      Nat.cast_one] at h
  have hper : ∀ x y : ℤ, x ≡ y [ZMOD M] →
      multiplicityColumn basis g M x χ = multiplicityColumn basis g M y χ :=
    fun x y h => congrFun (multiplicityColumn_congr basis g M h) χ
  rw [show g ^ (2 * K) = g ^ (M / 2) by rw [show M / 2 = 2 * K by omega],
    character_half_pow_eq_signed_sum basis hM ⟨2 * K, by omega⟩ hg χ]
  congr 1
  exact signed_residue_column_identity hMK hK hK2 (fun j => multiplicityColumn basis g M j χ)
    hper htwist a ha I hI_odd hI_pair

end Columns

section Supplied

variable {G : Type u} [Group G]

theorem supplied_r_pow_modulus {n : ℕ} {S : Subgroup G} (e : SemidihedralGroup n ≃* S) :
    (e (r n) : G) ^ modulus n = 1 := by
  rw [← Subgroup.coe_pow, ← map_pow, r_modulus, map_one, Subgroup.coe_one]

theorem supplied_s_conj_r {n : ℕ} {S : Subgroup G} (e : SemidihedralGroup n ≃* S) :
    (e (s n) : G) * (e (r n) : G) * (e (s n) : G)⁻¹ = (e (r n) : G) ^ (2 ^ (n - 2) - 1) := by
  rw [← Subgroup.coe_inv, ← Subgroup.coe_mul, ← Subgroup.coe_mul, ← Subgroup.coe_pow, ← map_inv,
    ← map_mul, ← map_mul, ← map_pow, s_conj_r]

theorem modulus_eq_four_mul {n : ℕ} (hn : 4 ≤ n) :
    modulus n = 4 * 2 ^ (n - 3) ∧ Even (2 ^ (n - 3)) ∧ 2 ≤ 2 ^ (n - 3) ∧
      2 ^ (n - 2) = 2 * 2 ^ (n - 3) := by
  have h1 : n - 1 = (n - 3) + 2 := by omega
  have h2 : n - 2 = (n - 3) + 1 := by omega
  have h3 : n - 3 = (n - 4) + 1 := by omega
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [modulus, h1, pow_add]
    ring
  · rw [h3, pow_succ]
    exact ⟨2 ^ (n - 4), by ring⟩
  · rw [h3, pow_succ]
    have := Nat.one_le_two_pow (n := n - 4)
    omega
  · rw [h2, pow_succ]
    ring

theorem supplied_orderOf_r {n : ℕ} (hn : 3 ≤ n) {S : Subgroup G} (e : SemidihedralGroup n ≃* S) :
    orderOf (e (r n) : G) = modulus n := by
  have h := orderOf_injective S.subtype S.subtype_injective (e (r n))
  have he : orderOf (e (r n)) = orderOf (r n) := orderOf_injective e.toMonoidHom e.injective _
  rw [Subgroup.coe_subtype] at h
  rw [h, he, orderOf_r n hn]

theorem supplied_twist_val {n : ℕ} (hn : 4 ≤ n) :
    ((((modulus n / 2 : ℕ) : ZMod (modulus n)) - 1)).val = 2 * 2 ^ (n - 3) - 1 := by
  obtain ⟨hM, -, hK2, -⟩ := modulus_eq_four_mul hn
  rw [show modulus n / 2 = 2 * 2 ^ (n - 3) by omega,
    show ((2 * 2 ^ (n - 3) : ℕ) : ZMod (modulus n)) - 1 =
      ((2 * 2 ^ (n - 3) - 1 : ℕ) : ZMod (modulus n)) by
    rw [Nat.cast_sub (show 1 ≤ 2 * 2 ^ (n - 3) by omega), Nat.cast_one],
    ZMod.val_cast_of_lt (by omega)]

theorem exists_isOddResidueTransversal {n : ℕ} (hn : 4 ≤ n) :
    ∃ I : Finset (ZMod (modulus n)),
      IsOddResidueTransversal (((modulus n / 2 : ℕ) : ZMod (modulus n)) - 1) I := by
  obtain ⟨hM, hKeven, hK2, -⟩ := modulus_eq_four_mul hn
  exact ⟨_, isOddResidueTransversal_mod_four hM hKeven hK2 (supplied_twist_val hn)⟩

variable [Fintype G]

theorem supplied_multiplicityColumn_twist {n : ℕ} (hn : 4 ≤ n) {S : Subgroup G}
    (e : SemidihedralGroup n ≃* S) (basis : FiniteIrreducibleCharacterBasis G) (j : ℤ) :
    multiplicityColumn basis (e (r n) : G) (modulus n) ((((modulus n / 2 : ℕ) : ℤ) - 1) * j) =
      multiplicityColumn basis (e (r n) : G) (modulus n) j := by
  obtain ⟨hM, -, hK2, hhalf⟩ := modulus_eq_four_mul hn
  have hsq : (2 ^ (n - 2) - 1) * (2 ^ (n - 2) - 1) % modulus n = 1 % modulus n := by
    rw [hhalf, hM]
    obtain ⟨k, hk⟩ : ∃ k, 2 ^ (n - 3) = k + 1 := ⟨2 ^ (n - 3) - 1, by omega⟩
    rw [hk, show 2 * (k + 1) - 1 = 2 * k + 1 by omega,
      show (2 * k + 1) * (2 * k + 1) = 1 + 4 * (k + 1) * k by ring, Nat.add_mul_mod_self_left]
  have hcast : (((modulus n / 2 : ℕ) : ℤ) - 1) = (((2 ^ (n - 2) - 1 : ℕ) : ℤ)) := by
    rw [hM, hhalf, Nat.cast_sub (show 1 ≤ 2 * 2 ^ (n - 3) by omega),
      show 4 * 2 ^ (n - 3) / 2 = 2 * 2 ^ (n - 3) by omega, Nat.cast_one]
  rw [hcast]
  exact multiplicityColumn_mul_of_conj basis (Nat.pos_of_ne_zero (NeZero.ne _))
    (supplied_r_pow_modulus e) (supplied_s_conj_r e) hsq j

theorem supplied_central_column_identity {n : ℕ} (hn : 4 ≤ n) {S : Subgroup G}
    (e : SemidihedralGroup n ≃* S) (basis : FiniteIrreducibleCharacterBasis G)
    {I : Finset (ZMod (modulus n))}
    (hI : IsOddResidueTransversal (((modulus n / 2 : ℕ) : ZMod (modulus n)) - 1) I)
    (χ : basis.index) :
    (basis.representation χ).character ((e (r n) : G) ^ (modulus n / 2)) =
      ((((modulus n / 2 : ℕ) : ℤ) *
          (multiplicityColumn basis (e (r n) : G) (modulus n) 0 χ -
            multiplicityColumn basis (e (r n) : G) (modulus n) 1 χ) -
        (multiplicityColumn basis (e (r n) : G) (modulus n) 0 χ -
          multiplicityColumn basis (e (r n) : G) (modulus n) (modulus n / 2 : ℕ) χ) -
        2 * ∑ l ∈ Finset.Icc 1 (modulus n / 4 - 1),
          (multiplicityColumn basis (e (r n) : G) (modulus n) 0 χ -
            multiplicityColumn basis (e (r n) : G) (modulus n) (2 * l) χ) -
        2 * ∑ j ∈ I, (multiplicityColumn basis (e (r n) : G) (modulus n) j.val χ -
          multiplicityColumn basis (e (r n) : G) (modulus n) 1 χ) : ℤ) : ℂ) := by
  obtain ⟨hM, hKeven, hK2, hhalf⟩ := modulus_eq_four_mul hn
  have hM2 : modulus n / 2 = 2 * 2 ^ (n - 3) := by omega
  have hM4 : modulus n / 4 = 2 ^ (n - 3) := by omega
  have hs : (e (s n) : G) * (e (r n) : G) * (e (s n) : G)⁻¹ =
      (e (r n) : G) ^ (2 * 2 ^ (n - 3) - 1) := by
    rw [supplied_s_conj_r e, hhalf]
  have h := character_central_column_identity basis hM hKeven hK2 (supplied_r_pow_modulus e) hs
    _ (supplied_twist_val hn) I hI.odd hI.pair χ
  rw [hM2, hM4]
  push_cast at h ⊢
  exact h

theorem cyclic_multiplicity_central_involution_congruence {n : ℕ} (hn : 4 ≤ n) (S : Sylow 2 G)
    (e : SemidihedralGroup n ≃* (S : Subgroup G)) (basis : FiniteIrreducibleCharacterBasis G)
    (B : Finset basis.index) (I : Finset (ZMod (modulus n)))
    (hI : IsOddResidueTransversal (((modulus n / 2 : ℕ) : ZMod (modulus n)) - 1) I) :
    let M := modulus n
    let r : G := e (Semidihedral.r n)
    let t : G := r ^ (M / 2)
    let L : ℤ → basis.index → ℤ := multiplicityColumn basis r M
    let Θ : basis.index → ℤ := L 0 - L (M / 2 : ℕ)
    let E : ℕ → basis.index → ℤ := fun l => L 0 - L (2 * l)
    let F : ZMod M → basis.index → ℤ := fun j => L j.val - L 1
    (∀ j k : ℤ,
      cyclicLinearCharacter r M j ⟨r ^ k, Subgroup.zpow_mem_zpowers r k⟩ =
        cyclicRoot M ^ (j * k)) ∧
    (∀ (j : ℤ) (χ : basis.index), ∃ m : ℕ,
      (Nat.card (Subgroup.zpowers r) : ℂ)⁻¹ * ∑ x : Subgroup.zpowers r,
          (basis.representation χ).character x * starRingEnd ℂ (cyclicLinearCharacter r M j x) =
        m ∧
      characterPairing (fun x : Subgroup.zpowers r => (basis.representation χ).character x)
          (cyclicLinearCharacter r M j) = m ∧
        cyclicMultiplicity (basis.representation χ).character r M j = m ∧ L j χ = m) ∧
    (∀ j : ℤ, L ((((M / 2 : ℕ) : ℤ) - 1) * j) = L j) ∧
    (∀ χ ∈ B, (basis.representation χ).character t =
      ((((M / 2 : ℕ) : ℤ) * (L 0 χ - L 1 χ) - Θ χ -
        2 * ∑ l ∈ Finset.Icc 1 (M / 4 - 1), E l χ - 2 * ∑ j ∈ I, F j χ : ℤ) : ℂ)) ∧
    (∀ χ ∈ B, ∃ k : ℤ, (basis.representation χ).character t +
      ((Θ χ + 2 * ∑ l ∈ Finset.Icc 1 (M / 4 - 1), E l χ + 2 * ∑ j ∈ I, F j χ : ℤ) : ℂ) =
        ((((M / 2 : ℕ) : ℤ) * k : ℤ) : ℂ)) ∧
    ∀ (q : ℕ) (ε : ℤ) (U V : basis.index → ℤ), 3 ≤ q → Odd q →
      2 ^ padicValNat 2 (q ^ 2 - 1) = M → (q % 4 = 1 → ε = 1) → (q % 4 = 3 → ε = -1) →
      (∀ χ ∈ B, (basis.representation χ).character t = ((U χ + (1 + ε * q) * V χ : ℤ) : ℂ)) →
      ∀ χ ∈ B, U χ + 2 * V χ + Θ χ + 2 * ∑ l ∈ Finset.Icc 1 (M / 4 - 1), E l χ +
        2 * ∑ j ∈ I, F j χ ≡ 0 [ZMOD ((M / 2 : ℕ) : ℤ)] := by
  intro M r t L Θ E F
  have hM : 0 < M := Nat.pos_of_ne_zero (NeZero.ne _)
  have hr : r ^ M = 1 := supplied_r_pow_modulus e
  have hord : orderOf r = M := supplied_orderOf_r (by omega) e
  have hid : ∀ χ, (basis.representation χ).character t =
      ((((M / 2 : ℕ) : ℤ) * (L 0 χ - L 1 χ) - Θ χ -
        2 * ∑ l ∈ Finset.Icc 1 (M / 4 - 1), E l χ - 2 * ∑ j ∈ I, F j χ : ℤ) : ℂ) := fun χ =>
    supplied_central_column_identity hn e basis hI χ
  refine ⟨fun j k => cyclicLinearCharacter_zpow hord j k, fun j χ => ?_,
    supplied_multiplicityColumn_twist hn e basis, fun χ _ => hid χ, fun χ _ => ?_, ?_⟩
  · obtain ⟨m, hm, hL⟩ := multiplicityColumn_eq_natural basis hM hr j χ
    exact ⟨m, (cyclicMultiplicity_eq_inner _ hord j).symm.trans hm,
      (characterPairing_zpowers_cyclicLinearCharacter _ hord j).trans hm, hm, hL⟩
  · refine ⟨L 0 χ - L 1 χ, ?_⟩
    rw [hid χ]
    push_cast
    ring
  · intro q ε U V hq3 hq hval hε1 hε3 hUV χ hχ
    have hdvd : (((M / 2 : ℕ) : ℤ)) ∣ ε * q - 1 := by
      have h := two_pow_dvd_sign_mul_sub_one hq3 hq (m := n - 1) (by omega)
        (by rw [hval]; rfl) hε1 hε3
      have hpow : 2 ^ (n - 1 - 1) = M / 2 := by
        change 2 ^ (n - 1 - 1) = 2 ^ (n - 1) / 2
        obtain ⟨k, hk⟩ : ∃ k, n - 1 = k + 1 := ⟨n - 2, by omega⟩
        rw [hk, Nat.add_sub_cancel, pow_succ, Nat.mul_div_cancel _ two_pos]
      rwa [hpow] at h
    have heq : U χ + (1 + ε * q) * V χ = ((M / 2 : ℕ) : ℤ) * (L 0 χ - L 1 χ) - Θ χ -
        2 * ∑ l ∈ Finset.Icc 1 (M / 4 - 1), E l χ - 2 * ∑ j ∈ I, F j χ := by
      have h := (hUV χ hχ).symm.trans (hid χ)
      exact_mod_cast h
    apply Int.modEq_zero_iff_dvd.mpr
    have hrw : U χ + 2 * V χ + Θ χ + 2 * ∑ l ∈ Finset.Icc 1 (M / 4 - 1), E l χ +
        2 * ∑ j ∈ I, F j χ = ((M / 2 : ℕ) : ℤ) * (L 0 χ - L 1 χ) - (ε * q - 1) * V χ := by
      linear_combination heq
    rw [hrw]
    exact (dvd_mul_right _ _).sub (hdvd.mul_right _)

end Supplied

end CFSG.Semidihedral.Principal
