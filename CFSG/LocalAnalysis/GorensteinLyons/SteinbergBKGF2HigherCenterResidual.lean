module

public import CFSG.LocalAnalysis.GorensteinLyons.SteinbergBKGF2CriticalQuotientWidth
public import CFSG.LocalAnalysis.GorensteinLyons.SteinbergBKGF2HigherCriticalFusion
public import CFSG.LocalAnalysis.GorensteinLyons.SteinbergBLCriticalCoreAction

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.GorensteinLyons

open Subgroup CFSG.Open
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.SectionRank.Ccomm (ThompsonCritical)
open scoped IsMulCommutative commutatorElement

namespace SteinbergBK



@[expose] def metacyclicRels (n : ℕ) (c j : ℤ) : Set (FreeGroup (Fin 2)) :=
  {FreeGroup.of 0 ^ n, FreeGroup.of 1 ^ 2 * FreeGroup.of 0 ^ (-c),
    (FreeGroup.of 1)⁻¹ * FreeGroup.of 0 * FreeGroup.of 1 * FreeGroup.of 0 ^ (-j)}

theorem card_presentedGroup_metacyclicRels_le {n : ℕ} (hn : 0 < n) (c j : ℤ) :
    Finite (PresentedGroup (metacyclicRels n c j)) ∧
      Nat.card (PresentedGroup (metacyclicRels n c j)) ≤ 2 * n := by
  classical
  set H := PresentedGroup (metacyclicRels n c j)
  set y : H := PresentedGroup.of 0 with hydef
  set s : H := PresentedGroup.of 1 with hsdef
  have hrel : ∀ x ∈ metacyclicRels n c j, PresentedGroup.mk (metacyclicRels n c j) x = 1 :=
    fun x hx => PresentedGroup.one_of_mem hx
  have hy : y ^ n = 1 := by
    have h := hrel (FreeGroup.of 0 ^ n) (by simp [metacyclicRels])
    rw [map_pow] at h
    exact h
  have hs : s ^ 2 = y ^ c := by
    have h := hrel (FreeGroup.of 1 ^ 2 * FreeGroup.of 0 ^ (-c)) (by simp [metacyclicRels])
    rw [map_mul, map_pow, map_zpow] at h
    have h2 : s ^ 2 * y ^ (-c) = 1 := h
    rw [mul_eq_one_iff_eq_inv.mp h2, zpow_neg, inv_inv]
  have hys : s⁻¹ * y * s = y ^ j := by
    have h := hrel ((FreeGroup.of 1)⁻¹ * FreeGroup.of 0 * FreeGroup.of 1 * FreeGroup.of 0 ^ (-j))
      (by simp [metacyclicRels])
    rw [map_mul, map_mul, map_mul, map_inv, map_zpow] at h
    have h2 : s⁻¹ * y * s * y ^ (-j) = 1 := h
    rw [mul_eq_one_iff_eq_inv.mp h2, zpow_neg, inv_inv]
  have hys' : s * y * s⁻¹ = y ^ j := by
    have h1 : s * y * s⁻¹ = s ^ 2 * (s⁻¹ * y * s) * (s ^ 2)⁻¹ := by group
    rw [h1, hys, hs, ← zpow_add, ← zpow_neg, ← zpow_add]
    congr 1
    ring
  set N := zpowers y with hNdef
  have hconj1 : ∀ x ∈ N, s * x * s⁻¹ ∈ N := by
    rintro _ ⟨i, rfl⟩
    have h1 : s * y ^ i * s⁻¹ = (s * y * s⁻¹) ^ i := (conj_zpow).symm
    simp only at h1 ⊢
    rw [h1, hys', ← zpow_mul]
    exact zpow_mem (mem_zpowers y) _
  have hconj2 : ∀ x ∈ N, s⁻¹ * x * s ∈ N := by
    rintro _ ⟨i, rfl⟩
    have h1 : s⁻¹ * y ^ i * s = (s⁻¹ * y * s) ^ i := by
      have := conj_zpow (a := s⁻¹) (b := y) (i := i)
      rw [inv_inv] at this
      exact this.symm
    simp only at h1 ⊢
    rw [h1, hys, ← zpow_mul]
    exact zpow_mem (mem_zpowers y) _
  have hsN : s ∈ normalizer (N : Set H) := by
    rw [mem_normalizer_iff]
    intro x
    refine ⟨hconj1 x, fun hx => ?_⟩
    have h1 := hconj2 _ hx
    rwa [show s⁻¹ * (s * x * s⁻¹) * s = x by group] at h1
  have hNn : N.Normal := by
    rw [← normalizer_eq_top_iff, eq_top_iff]
    intro x _
    refine PresentedGroup.generated_by _ (normalizer (N : Set H)) (fun i => ?_) x
    fin_cases i
    · exact le_normalizer (mem_zpowers y)
    · exact hsN
  let π := QuotientGroup.mk' N
  have hπy : π y = 1 := (QuotientGroup.eq_one_iff y).mpr (mem_zpowers y)
  have hπs2 : π s ^ 2 = 1 := by
    rw [← map_pow, hs]
    exact (QuotientGroup.eq_one_iff _).mpr (zpow_mem (mem_zpowers y) c)
  have htop : zpowers (π s) = ⊤ := by
    rw [eq_top_iff]
    intro x _
    obtain ⟨h, rfl⟩ := QuotientGroup.mk'_surjective N x
    have h1 : h ∈ (zpowers (π s)).comap π := by
      refine PresentedGroup.generated_by _ _ (fun i => ?_) h
      fin_cases i
      · change π y ∈ zpowers (π s)
        rw [hπy]
        exact one_mem _
      · exact mem_zpowers (π s)
    exact h1
  have hord : orderOf (π s) ∣ 2 := orderOf_dvd_of_pow_eq_one hπs2
  have hordpos : 0 < orderOf (π s) := Nat.pos_of_dvd_of_pos hord (by norm_num)
  have hQcard : Nat.card (H ⧸ N) = orderOf (π s) := by
    rw [← Nat.card_zpowers, htop]
    exact (Subgroup.card_top (G := H ⧸ N)).symm
  have hyord : orderOf y ∣ n := orderOf_dvd_of_pow_eq_one hy
  have hNcard : Nat.card N = orderOf y := Nat.card_zpowers y
  have hNle : Nat.card N ≤ n := hNcard ▸ Nat.le_of_dvd hn hyord
  have hNpos : 0 < Nat.card N := hNcard ▸ Nat.pos_of_dvd_of_pos hyord hn
  have hcard := card_eq_card_quotient_mul_card_subgroup N
  have hle : Nat.card H ≤ 2 * n := by
    rw [hcard, hQcard]
    exact Nat.mul_le_mul (Nat.le_of_dvd (by norm_num) hord) hNle
  refine ⟨Nat.finite_of_card_ne_zero ?_, hle⟩
  rw [hcard, hQcard]
  exact (Nat.mul_pos hordpos hNpos).ne'

theorem exists_presentedGroup_mulEquiv {X : Type*} [Group X] {n : ℕ} (hn : 0 < n) {c j : ℤ}
    {R : Subgroup X} {y s : X} (hyR : y ∈ R) (hsR : s ∈ R) (hy : y ^ n = 1) (hs : s ^ 2 = y ^ c)
    (hys : s⁻¹ * y * s = y ^ j) (hR : closure {y, s} = R) (hcard : Nat.card R = 2 * n) :
    ∃ e : PresentedGroup (metacyclicRels n c j) ≃* R,
      (e (PresentedGroup.of 0) : X) = y ∧ (e (PresentedGroup.of 1) : X) = s := by
  classical
  obtain ⟨hfin, hle⟩ := card_presentedGroup_metacyclicRels_le hn c j
  let f : Fin 2 → R := fun i => if i = 0 then ⟨y, hyR⟩ else ⟨s, hsR⟩
  have hf0 : f 0 = ⟨y, hyR⟩ := rfl
  have hf1 : f 1 = ⟨s, hsR⟩ := rfl
  have hrel : ∀ r ∈ metacyclicRels n c j, FreeGroup.lift f r = 1 := by
    intro r hr
    simp only [metacyclicRels, Set.mem_insert_iff, Set.mem_singleton_iff] at hr
    rcases hr with rfl | rfl | rfl
    · rw [map_pow, FreeGroup.lift_apply_of, hf0]
      exact Subtype.ext (by simpa using hy)
    · rw [map_mul, map_pow, map_zpow, FreeGroup.lift_apply_of, FreeGroup.lift_apply_of, hf0, hf1]
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_pow, Subgroup.coe_zpow, OneMemClass.coe_one]
      rw [hs, zpow_neg, mul_inv_cancel]
    · rw [map_mul, map_mul, map_mul, map_inv, map_zpow, FreeGroup.lift_apply_of,
        FreeGroup.lift_apply_of, hf0, hf1]
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_zpow, OneMemClass.coe_one]
      rw [hys, zpow_neg, mul_inv_cancel]
  let φ := PresentedGroup.toGroup hrel
  have hφ0 : φ (PresentedGroup.of 0) = ⟨y, hyR⟩ := PresentedGroup.toGroup.of hrel
  have hφ1 : φ (PresentedGroup.of 1) = ⟨s, hsR⟩ := PresentedGroup.toGroup.of hrel
  have hsurj : Function.Surjective φ := by
    rw [← MonoidHom.range_eq_top, eq_top_iff]
    intro x _
    have h1 : (x : X) ∈ closure ({y, s} : Set X) := hR ▸ x.2
    have h2 : closure ({y, s} : Set X) ≤ φ.range.map R.subtype := by
      rw [closure_le]
      intro g hg
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
      rcases hg with rfl | rfl
      · exact ⟨⟨g, hyR⟩, ⟨PresentedGroup.of 0, hφ0⟩, rfl⟩
      · exact ⟨⟨g, hsR⟩, ⟨PresentedGroup.of 1, hφ1⟩, rfl⟩
    obtain ⟨x', hx', hxx'⟩ := h2 h1
    rwa [show x' = x from Subtype.ext hxx'] at hx'
  have hbij : Function.Bijective φ := hsurj.bijective_of_nat_card_le (hle.trans hcard.ge)
  exact ⟨MulEquiv.ofBijective φ hbij, by
    change ((φ (PresentedGroup.of 0) : R) : X) = y
    rw [hφ0], by
    change ((φ (PresentedGroup.of 1) : R) : X) = s
    rw [hφ1]⟩


theorem isCoprime_two_pow_of_odd {o : ℤ} (ho : Odd o) (n : ℕ) : IsCoprime ((2 : ℤ) ^ n) o := by
  have h2 : IsCoprime (2 : ℤ) o := by
    rw [Int.isCoprime_iff_gcd_eq_one]
    have h3 : Odd o.natAbs := Int.natAbs_odd.mpr ho
    have h4 : Nat.Coprime 2 o.natAbs := Nat.coprime_two_left.mpr h3
    simpa [Int.gcd] using h4
  exact h2.pow_left

theorem two_pow_dvd_of_sq_sub_one {k : ℕ} (hk : 1 ≤ k) {j : ℤ}
    (h1 : (2 : ℤ) ^ k ∣ j * j - 1) (h4 : ¬ (4 : ℤ) ∣ j - 1) :
    (2 : ℤ) ^ (k - 1) ∣ j + 1 ∧ ∀ i : ℤ, (2 : ℤ) ^ k ∣ (j - 1) * i ↔ (2 : ℤ) ^ (k - 1) ∣ i := by
  have hk2 : (2 : ℤ) ^ k = 2 * 2 ^ (k - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  have hjodd : Odd j := by
    by_contra hj
    rw [Int.not_odd_iff_even] at hj
    obtain ⟨a, rfl⟩ := hj
    have h2 : (2 : ℤ) ∣ (a + a) * (a + a) - 1 := by
      rw [hk2] at h1
      exact (dvd_mul_right 2 _).trans h1
    obtain ⟨t, ht⟩ := h2
    have h3 : (a + a) * (a + a) = 2 * (2 * a * a) := by ring
    omega
  obtain ⟨o, ho⟩ : ∃ o, j - 1 = 2 * o := by
    obtain ⟨a, ha⟩ := hjodd
    exact ⟨a, by omega⟩
  have hoodd : Odd o := by
    by_contra hoe
    rw [Int.not_odd_iff_even] at hoe
    obtain ⟨p, rfl⟩ := hoe
    exact h4 ⟨p, by omega⟩
  have hcop := isCoprime_two_pow_of_odd hoodd (k - 1)
  refine ⟨?_, fun i => ?_⟩
  · have h2 : (2 : ℤ) * 2 ^ (k - 1) ∣ 2 * (o * (j + 1)) := by
      rw [← hk2, show 2 * (o * (j + 1)) = j * j - 1 by
        rw [show j = 2 * o + 1 by omega]
        ring]
      exact h1
    have h3 := (mul_dvd_mul_iff_left (two_ne_zero : (2 : ℤ) ≠ 0)).mp h2
    exact hcop.dvd_of_dvd_mul_left h3
  · rw [ho, hk2, mul_assoc, mul_dvd_mul_iff_left (two_ne_zero : (2 : ℤ) ≠ 0)]
    constructor
    · intro h
      exact hcop.dvd_of_dvd_mul_left h
    · intro h
      exact Dvd.dvd.mul_left h o




theorem zpow_eq_zpow_iff_two_pow_dvd {X : Type*} [Group X] {y : X} {k : ℕ}
    (hy : orderOf y = 2 ^ k) (a b : ℤ) : y ^ a = y ^ b ↔ (2 : ℤ) ^ k ∣ b - a := by
  rw [zpow_eq_zpow_iff_modEq, hy, Int.modEq_iff_dvd]
  push_cast
  rfl

theorem conj_exponent_of_moves_four {X : Type*} [Group X] {y x : X} {k : ℕ} (hk : 3 ≤ k)
    (hy : orderOf y = 2 ^ k) {j : ℤ} (hj : x⁻¹ * y * x = y ^ j)
    (hx2 : x ^ 2 * y = y * x ^ 2)
    (hT : ∃ t ∈ zpowers y, t ^ 4 = 1 ∧ x⁻¹ * t * x ≠ t) :
    (y ^ j = y⁻¹ ∨ y ^ j = y ^ (-1 + 2 ^ (k - 1) : ℤ)) ∧
      (∀ i : ℤ, x⁻¹ * y ^ i * x = y ^ i ↔ (2 : ℤ) ^ (k - 1) ∣ i) ∧
      ∀ t ∈ zpowers y, t ^ 4 = 1 → x⁻¹ * t * x = t⁻¹ := by
  have hpow : ∀ i : ℤ, x⁻¹ * y ^ i * x = y ^ (j * i) := by
    intro i
    have h1 := conj_zpow (a := x⁻¹) (b := y) (i := i)
    rw [inv_inv] at h1
    rw [← h1, hj, ← zpow_mul]
  have heq := zpow_eq_zpow_iff_two_pow_dvd hy
  have hjj : (2 : ℤ) ^ k ∣ j * j - 1 := by
    have h1 : x⁻¹ * (x⁻¹ * y * x) * x = y := by
      have h2 : x⁻¹ * (x⁻¹ * y * x) * x = (x ^ 2)⁻¹ * (y * x ^ 2) := by
        rw [pow_two]
        group
      rw [h2, ← hx2]
      group
    rw [hj, hpow, mul_comm] at h1
    have h2 := (heq (j * j) 1).mp (by rw [zpow_one]; exact h1)
    rwa [show (1 : ℤ) - j * j = -(j * j - 1) by ring, dvd_neg] at h2
  have h4 : ¬ (4 : ℤ) ∣ j - 1 := by
    obtain ⟨t, ht, ht4, htx⟩ := hT
    obtain ⟨a, rfl⟩ := mem_zpowers_iff.mp ht
    intro ⟨e, he⟩
    apply htx
    rw [hpow]
    rw [← zpow_natCast, ← zpow_mul, show ((4 : ℕ) : ℤ) = 4 from rfl] at ht4
    have h5 := (heq (a * 4) 0).mp (by rw [zpow_zero]; exact ht4)
    rw [heq]
    obtain ⟨f, hf⟩ := h5
    exact ⟨e * f, by linear_combination (-a) * he + e * hf⟩
  obtain ⟨hj1, hfix⟩ := two_pow_dvd_of_sq_sub_one (by omega : 1 ≤ k) hjj h4
  obtain ⟨e, he⟩ := hj1
  have hk2 : (2 : ℤ) ^ k = 2 * 2 ^ (k - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  refine ⟨?_, fun i => ?_, fun t ht ht4 => ?_⟩
  · rcases Int.even_or_odd e with ⟨f, hf⟩ | ⟨f, hf⟩
    · left
      rw [← zpow_neg_one, heq, hk2]
      exact ⟨-f, by linear_combination (-1 : ℤ) * he - (2 ^ (k - 1) : ℤ) * hf⟩
    · right
      rw [heq, hk2]
      exact ⟨-f, by linear_combination (-1 : ℤ) * he - (2 ^ (k - 1) : ℤ) * hf⟩
  · rw [hpow, heq, ← hfix i]
    constructor
    · intro h
      obtain ⟨g, hg⟩ := h
      exact ⟨-g, by linear_combination (-1 : ℤ) * hg⟩
    · intro h
      obtain ⟨g, hg⟩ := h
      exact ⟨-g, by linear_combination (-1 : ℤ) * hg⟩
  · obtain ⟨a, rfl⟩ := mem_zpowers_iff.mp ht
    rw [← zpow_natCast, ← zpow_mul, show ((4 : ℕ) : ℤ) = 4 from rfl] at ht4
    have h5 := (heq (a * 4) 0).mp (by rw [zpow_zero]; exact ht4)
    rw [hpow, ← zpow_neg, heq]
    obtain ⟨f, hf⟩ := h5
    have hk3 : (2 : ℤ) ^ k = 4 * 2 ^ (k - 2) := by
      rw [show (4 : ℤ) = 2 ^ 2 by norm_num, ← pow_add]
      congr 1
      omega
    have ha : (2 : ℤ) ^ (k - 2) ∣ a := by
      refine ⟨-f, ?_⟩
      have : (4 : ℤ) * a = 4 * (2 ^ (k - 2) * -f) := by
        rw [hk3] at hf
        linear_combination (-1 : ℤ) * hf
      linarith
    obtain ⟨g, hg⟩ := ha
    have hk4 : (2 : ℤ) ^ (k - 1) * 2 ^ (k - 2) = 2 ^ k * 2 ^ (k - 3) := by
      rw [← pow_add, ← pow_add]
      congr 1
      omega
    refine ⟨-(e * g * 2 ^ (k - 3)), ?_⟩
    rw [hg]
    linear_combination (-(2 : ℤ) ^ (k - 2) * g) * he + (-e * g) * hk4


theorem exists_finset_closure_top_of_mulEquiv {X X' : Type*} [Group X] [Group X'] (e : X ≃* X')
    {n : ℕ} (h : ∃ T : Finset X, closure (T : Set X) = ⊤ ∧ T.card ≤ n) :
    ∃ T : Finset X', closure (T : Set X') = ⊤ ∧ T.card ≤ n := by
  classical
  obtain ⟨T, hT, hTcard⟩ := h
  refine ⟨T.map e.toEquiv.toEmbedding, ?_, by rw [Finset.card_map]; exact hTcard⟩
  rw [Finset.coe_map]
  change closure (e.toMonoidHom '' (T : Set X)) = ⊤
  rw [← MonoidHom.map_closure, hT, map_top_of_surjective _ e.surjective]

theorem subgroup_generated_of_cyclic_normal_elementary {X : Type*} [Group X] [Finite X]
    {N : Subgroup X} [N.Normal] (hN : IsCyclic N) [IsElementaryAbelian 2 (X ⧸ N)] {d : ℕ}
    (hd : Nat.card (X ⧸ N) = 2 ^ d) (K : Subgroup X) :
    ∃ S : Finset X, S.card ≤ d + 1 ∧ closure (S : Set X) = K := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let φ : K →* X ⧸ N := (QuotientGroup.mk' N).comp K.subtype
  have hker : ∃ T : Finset φ.rangeRestrict.ker,
      closure (T : Set φ.rangeRestrict.ker) = ⊤ ∧ T.card ≤ 1 := by
    have hmem : ∀ x : φ.rangeRestrict.ker, ((x : K) : X) ∈ N := fun x => by
      have h : φ.rangeRestrict (x : K) = 1 := MonoidHom.mem_ker.mp x.2
      have h2 : φ (x : K) = 1 := by
        have h3 := congrArg Subtype.val h
        simpa using h3
      exact (QuotientGroup.eq_one_iff _).mp h2
    let ι : φ.rangeRestrict.ker →* N :=
      { toFun := fun x => ⟨_, hmem x⟩
        map_one' := rfl
        map_mul' := fun _ _ => rfl }
    have hι : Function.Injective ι := fun x y h =>
      Subtype.ext (Subtype.ext (congrArg (fun w : N => (w : X)) h))
    have : IsCyclic φ.rangeRestrict.ker := isCyclic_of_injective ι hι
    exact exists_finset_closure_eq_top_of_generatorRank_le
      (CFSG.generatorRank_le_one_of_isCyclic inferInstance)
  have hran : ∃ T : Finset φ.range, closure (T : Set φ.range) = ⊤ ∧ T.card ≤ d := by
    have hpow : ∀ u : X ⧸ N, u ^ 2 = 1 := fun u =>
      Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        (IsElementaryAbelian.exponent_dvd_p 2 (X ⧸ N)) u
    have : IsElementaryAbelian 2 φ.range :=
      { toIsMulCommutative := ⟨⟨fun a b => Subtype.ext (mul_comm' (a : X ⧸ N) b)⟩⟩
        exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun a =>
          Subtype.ext (by simpa using hpow (a : X ⧸ N)) }
    have hfr : Module.finrank (ZMod 2) (Additive φ.range) ≤ d := by
      have : Fintype (Additive φ.range) := Fintype.ofFinite _
      have h1 : Nat.card (Additive φ.range) = 2 ^ Module.finrank (ZMod 2) (Additive φ.range) := by
        rw [Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := ZMod 2), ZMod.card]
      have h2 : Nat.card (Additive φ.range) ≤ 2 ^ d := by
        rw [← hd]
        exact card_le_card_group φ.range
      rw [h1] at h2
      exact (Nat.pow_le_pow_iff_right (by norm_num)).mp h2
    exact exists_finset_closure_eq_top_of_generatorRank_le
      ((CFSG.generatorRank_le_finrank_of_elementaryAbelian _).trans hfr)
  obtain ⟨TK, hTK, hTKcard⟩ := CFSG.LargeEvenClassification.Helpers.extension_generator_bound
    φ.rangeRestrict φ.rangeRestrict_surjective hker hran
  refine ⟨TK.map (Function.Embedding.subtype _), ?_, closure_map_subtype_eq hTK⟩
  rw [Finset.card_map]
  omega

theorem subgroup_generated_of_index_le_two {X : Type*} [Group X] [Finite X] {D : Subgroup X}
    [D.Normal] (hD : D.index ≤ 2) {n : ℕ}
    (hgen : ∀ K : Subgroup D, ∃ S : Finset D, S.card ≤ n ∧ closure (S : Set D) = K)
    (K : Subgroup X) : ∃ S : Finset X, S.card ≤ n + 1 ∧ closure (S : Set X) = K := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let ψ : K →* X ⧸ D := (QuotientGroup.mk' D).comp K.subtype
  have hmem : ∀ x : ψ.rangeRestrict.ker, ((x : K) : X) ∈ D := fun x => by
    have h : ψ.rangeRestrict (x : K) = 1 := MonoidHom.mem_ker.mp x.2
    have h2 : ψ (x : K) = 1 := by
      have h3 := congrArg Subtype.val h
      simpa using h3
    exact (QuotientGroup.eq_one_iff _).mp h2
  let ι : ψ.rangeRestrict.ker →* D :=
    { toFun := fun x => ⟨_, hmem x⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hι : Function.Injective ι := fun x y h =>
    Subtype.ext (Subtype.ext (congrArg (fun w : D => (w : X)) h))
  have hker : ∃ T : Finset ψ.rangeRestrict.ker,
      closure (T : Set ψ.rangeRestrict.ker) = ⊤ ∧ T.card ≤ n := by
    obtain ⟨S₀, hS₀, hS₀cl⟩ := hgen ι.range
    obtain ⟨T₀, hT₀, hT₀card⟩ := exists_finset_closure_eq_top_of_closure_eq hS₀cl
    exact exists_finset_closure_top_of_mulEquiv (MonoidHom.ofInjective hι).symm
      ⟨T₀, hT₀, hT₀card.trans hS₀⟩
  have hran : ∃ T : Finset ψ.range, closure (T : Set ψ.range) = ⊤ ∧ T.card ≤ 1 := by
    have hcard : Nat.card ψ.range ≤ 2 :=
      (card_le_card_group ψ.range).trans (by rw [← index_eq_card]; exact hD)
    have : IsCyclic ψ.range := by
      have hpos : 0 < Nat.card ψ.range := Nat.card_pos
      rcases (show Nat.card ψ.range = 1 ∨ Nat.card ψ.range = 2 by omega) with h | h
      · have : Subsingleton ψ.range := (Nat.card_eq_one_iff_unique.mp h).1
        infer_instance
      · exact isCyclic_of_prime_card h
    exact exists_finset_closure_eq_top_of_generatorRank_le
      (CFSG.generatorRank_le_one_of_isCyclic inferInstance)
  obtain ⟨TK, hTK, hTKcard⟩ := CFSG.LargeEvenClassification.Helpers.extension_generator_bound
    ψ.rangeRestrict ψ.rangeRestrict_surjective hker hran
  refine ⟨TK.map (Function.Embedding.subtype _), ?_, closure_map_subtype_eq hTK⟩
  rw [Finset.card_map]
  omega


theorem relIndex_two_mem {P : Type*} [Group P] {R Y : Subgroup P} (h2 : Y.relIndex R = 2)
    {s : P} (hsR : s ∈ R) (hsY : s ∉ Y) :
    s * s ∈ Y ∧ ∀ x ∈ R, x ∉ Y → s⁻¹ * x ∈ Y := by
  have hidx : (Y.subgroupOf R).index = 2 := h2
  have hmem : ∀ a b : R, (a : P) * b ∈ Y ↔ ((a : P) ∈ Y ↔ (b : P) ∈ Y) := fun a b => by
    have := mul_mem_iff_of_index_two hidx (a := a) (b := b)
    simpa [mem_subgroupOf] using this
  refine ⟨(hmem ⟨s, hsR⟩ ⟨s, hsR⟩).mpr Iff.rfl, fun x hxR hxY => ?_⟩
  have := (hmem ⟨s⁻¹, R.inv_mem hsR⟩ ⟨x, hxR⟩).mpr
    ⟨fun h => absurd (by simpa using Y.inv_mem h) hsY, fun h => absurd h hxY⟩
  simpa using this

abbrev ResidualDihedral {P : Type*} [Group P] (R Y : Subgroup P) (y : P) (k : ℕ) : Prop :=
  ∃ s ∈ R, s ∉ Y ∧ Nat.card R = 2 ^ (k + 1) ∧ s ^ 2 = 1 ∧ s⁻¹ * y * s = y⁻¹ ∧
    ∃ e : PresentedGroup (metacyclicRels (2 ^ k) 0 (-1)) ≃* R,
      (e (PresentedGroup.of 0) : P) = y ∧ (e (PresentedGroup.of 1) : P) = s

abbrev ResidualQuaternion {P : Type*} [Group P] (R Y : Subgroup P) (y : P) (k : ℕ) : Prop :=
  ∃ s ∈ R, s ∉ Y ∧ Nat.card R = 2 ^ (k + 1) ∧ s ^ 2 = y ^ 2 ^ (k - 1) ∧ s⁻¹ * y * s = y⁻¹ ∧
    ∃ e : PresentedGroup (metacyclicRels (2 ^ k) (2 ^ (k - 1)) (-1)) ≃* R,
      (e (PresentedGroup.of 0) : P) = y ∧ (e (PresentedGroup.of 1) : P) = s

abbrev ResidualSemidihedral {P : Type*} [Group P] (R Y : Subgroup P) (y : P) (k : ℕ) : Prop :=
  ∃ s ∈ R, s ∉ Y ∧ Nat.card R = 2 ^ (k + 1) ∧ s ^ 2 = 1 ∧
    s⁻¹ * y * s = y ^ (-1 + 2 ^ (k - 1) : ℤ) ∧
    ∃ e : PresentedGroup (metacyclicRels (2 ^ k) 0 (-1 + 2 ^ (k - 1))) ≃* R,
      (e (PresentedGroup.of 0) : P) = y ∧ (e (PresentedGroup.of 1) : P) = s

@[expose] def ResidualAlternative {P : Type*} [Group P] (R Y : Subgroup P) (y : P) (k : ℕ) :
    Fin 4 → Prop :=
  ![R = Y, ResidualDihedral R Y y k, ResidualQuaternion R Y y k, ResidualSemidihedral R Y y k]

theorem mul_comm_of_mem_of_isCyclic {P : Type*} [Group P] {Y : Subgroup P} (hY : IsCyclic Y)
    {a b : P} (ha : a ∈ Y) (hb : b ∈ Y) : a * b = b * a :=
  congrArg Subtype.val ((IsCyclic.isMulCommutative (α := Y)).is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)

theorem orderOf_pow_two_pow_pred {P : Type*} [Group P] {y : P} {k : ℕ} (hk : 1 ≤ k)
    (hy : orderOf y = 2 ^ k) : orderOf (y ^ 2 ^ (k - 1)) = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  apply orderOf_eq_prime
  · rw [← pow_mul, ← pow_succ, show k - 1 + 1 = k by omega, ← hy, pow_orderOf_eq_one]
  · intro h
    have h1 := orderOf_dvd_of_pow_eq_one h
    rw [hy] at h1
    have h2 := Nat.le_of_dvd (by positivity) h1
    have h3 : 2 ^ (k - 1) < 2 ^ k := Nat.pow_lt_pow_right (by norm_num) (by omega)
    omega

theorem residual_factor_alternatives {P : Type*} [Group P] [Finite P] {D E R Y T : Subgroup P}
    [D.Normal] [Y.Normal] {z : P} (hz : orderOf z = 2) (hzc : z ∈ center P) (hzY : z ∈ Y)
    (hYcyc : IsCyclic Y) {k : ℕ} (hk : 3 ≤ k) (hYk : Nat.card Y = 2 ^ k) (hYD : Y ≤ D)
    (hTY : T ≤ Y) (hT4 : Nat.card T = 4) (hcT : centralizer (T : Set P) = D)
    (hidx : D.index ≤ 2) (hEY : E ⊔ Y = D) (hER : E ⊔ R = ⊤) (hR : R = centralizer (E : Set P))
    (hERc : ⁅E, R⁆ = ⊥) (hEiR : E ⊓ R = zpowers z) (hEc : (center E).map E.subtype = zpowers z)
    (hRY : R ⊓ centralizer (Y : Set P) = Y) :
    R ⊓ D = Y ∧ Y.relIndex R = D.index ∧
      (∀ y : P, zpowers y = Y → ∃! i : Fin 4, ResidualAlternative R Y y k i) ∧
      (R = Y ↔ D = ⊤) ∧ (R ≠ Y → center P = zpowers z) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hYR : Y ≤ R := by
    have h := (inf_le_left : R ⊓ centralizer (Y : Set P) ≤ R)
    rwa [hRY] at h
  have hzpY : zpowers z ≤ Y := zpowers_le.mpr hzY
  have hzR : z ∈ R := by
    have h1 : z ∈ E ⊓ R := by rw [hEiR]; exact mem_zpowers z
    exact h1.2
  have hEn : E.Normal := by
    rw [← normalizer_eq_top_iff, eq_top_iff, ← hER]
    exact sup_le le_normalizer (hR.le.trans (centralizer_le_normalizer _))
  have hRn : R.Normal := by
    have hEcR : E ≤ centralizer (R : Set P) := commutator_eq_bot_iff_le_centralizer.mp hERc
    rw [← normalizer_eq_top_iff, eq_top_iff, ← hER]
    exact sup_le (hEcR.trans (centralizer_le_normalizer _)) le_normalizer
  have hED : E ≤ D := hEY ▸ le_sup_left
  have hRD : R ⊓ D = Y := by
    refine le_antisymm ?_ (le_inf hYR hYD)
    rintro x ⟨hxR, hxD⟩
    rw [← hEY] at hxD
    obtain ⟨e, he, y', hy', rfl⟩ := mem_sup_of_normal_right.mp hxD
    have he' : e ∈ R := by
      have h1 := R.mul_mem hxR (R.inv_mem (hYR hy'))
      rwa [mul_inv_cancel_right] at h1
    have heY : e ∈ Y := by
      have h1 : e ∈ E ⊓ R := ⟨he, he'⟩
      rw [hEiR] at h1
      exact hzpY h1
    exact Y.mul_mem heY hy'
  have hrel : Y.relIndex R = D.index := by
    let ψ : R →* P ⧸ D := (QuotientGroup.mk' D).comp R.subtype
    have hψ : Function.Surjective ψ := by
      intro q
      obtain ⟨p, rfl⟩ := QuotientGroup.mk'_surjective D q
      have hp : p ∈ E ⊔ R := hER ▸ mem_top p
      obtain ⟨e, he, r, hr, rfl⟩ := mem_sup_of_normal_right.mp hp
      refine ⟨⟨r, hr⟩, ?_⟩
      change QuotientGroup.mk' D r = QuotientGroup.mk' D (e * r)
      have he1 : QuotientGroup.mk' D e = 1 := (QuotientGroup.eq_one_iff e).mpr (hED he)
      rw [map_mul, he1, one_mul]
    have hker : ψ.ker = Y.subgroupOf R := by
      ext r
      rw [MonoidHom.mem_ker, mem_subgroupOf]
      change QuotientGroup.mk' D (r : P) = 1 ↔ _
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      constructor
      · intro h
        rw [← hRD]
        exact ⟨r.2, h⟩
      · intro h
        exact hYD h
    rw [relIndex, index_eq_card, index_eq_card, ← hker]
    exact Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective ψ hψ).toEquiv
  have hD1 : D.index ≠ 0 := index_ne_zero_of_finite
  have hRY_iff : R = Y ↔ D = ⊤ := by
    rw [← index_eq_one, ← hrel, relIndex_eq_one]
    exact ⟨fun h => h ▸ le_rfl, fun h => le_antisymm h hYR⟩
  have hcardR : D.index = 2 → Nat.card R = 2 ^ (k + 1) := by
    intro h2
    have h1 := card_mul_index (Y.subgroupOf R)
    have h3 : (Y.subgroupOf R).index = 2 := hrel.trans h2
    rw [h3, Nat.card_congr (subgroupOfEquivOfLe hYR).toEquiv, hYk, ← pow_succ] at h1
    exact h1.symm
  have hanalysis : ∀ y : P, zpowers y = Y → D.index = 2 → ∀ s ∈ R, s ∉ Y →
      ∃ j : ℤ, s⁻¹ * y * s = y ^ j ∧ (y ^ j = y⁻¹ ∨ y ^ j = y ^ (-1 + 2 ^ (k - 1) : ℤ)) ∧
        (∀ i : ℤ, s⁻¹ * y ^ i * s = y ^ i ↔ (2 : ℤ) ^ (k - 1) ∣ i) ∧ s * s ∈ Y := by
    intro y hy h2 s hsR hsY
    have hord : orderOf y = 2 ^ k := by rw [← Nat.card_zpowers, hy, hYk]
    have hrel2 : Y.relIndex R = 2 := hrel.trans h2
    obtain ⟨hss, -⟩ := relIndex_two_mem hrel2 hsR hsY
    obtain ⟨j, hj⟩ : ∃ j : ℤ, s⁻¹ * y * s = y ^ j := by
      have h1 : s⁻¹ * y * s ∈ Y := by
        have := (inferInstance : Y.Normal).conj_mem y (hy ▸ mem_zpowers y) s⁻¹
        simpa using this
      rw [← hy] at h1
      obtain ⟨j, hj⟩ := mem_zpowers_iff.mp h1
      exact ⟨j, hj.symm⟩
    have hsD : s ∉ D := fun h => hsY (hRD ▸ ⟨hsR, h⟩)
    have hT : ∃ t ∈ zpowers y, t ^ 4 = 1 ∧ s⁻¹ * t * s ≠ t := by
      by_contra hno
      push Not at hno
      apply hsD
      rw [← hcT, mem_centralizer_iff]
      intro t ht
      have h1 := hno t (hy ▸ hTY ht) (by
        have := pow_card_eq_one' (G := T) (x := ⟨t, ht⟩)
        rw [hT4] at this
        exact congrArg Subtype.val this)
      calc t * s = s * (s⁻¹ * t * s) := by group
        _ = s * t := by rw [h1]
    have hx2 : s ^ 2 * y = y * s ^ 2 := by
      rw [pow_two]
      exact mul_comm_of_mem_of_isCyclic hYcyc hss (hy ▸ mem_zpowers y)
    obtain ⟨hjj, hfix, -⟩ := conj_exponent_of_moves_four hk hord hj hx2 hT
    exact ⟨j, hj, hjj, hfix, hss⟩
  have hdiff : D.index = 2 → ∀ s ∈ R, s ∉ Y → ∀ s' ∈ R, s' ∉ Y → s⁻¹ * s' ∈ Y := by
    intro h2 s hsR hsY s' hs'R hs'Y
    exact (relIndex_two_mem (hrel.trans h2) hsR hsY).2 s' hs'R hs'Y
  have hnot1 : ∀ s ∈ R, s ∉ Y → D.index = 2 := by
    intro s hsR hsY
    have h1 : D ≠ ⊤ := fun h => hsY (hRY_iff.mpr h ▸ hsR)
    have h2 : D.index ≠ 1 := fun h => h1 (index_eq_one.mp h)
    omega
  have hgenR : ∀ y : P, zpowers y = Y → ∀ s ∈ R, s ∉ Y → closure {y, s} = R := by
    intro y hy s hsR hsY
    have hrel2 : Y.relIndex R = 2 := hrel.trans (hnot1 s hsR hsY)
    have hyc : zpowers y ≤ closure ({y, s} : Set P) :=
      zpowers_le.mpr (subset_closure (by simp))
    have hsc : s ∈ closure ({y, s} : Set P) := subset_closure (by simp)
    apply le_antisymm
    · rw [closure_le]
      intro g hg
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
      rcases hg with rfl | rfl
      · exact hYR (hy ▸ mem_zpowers g)
      · exact hsR
    · intro x hxR
      by_cases hxY : x ∈ Y
      · rw [← hy] at hxY
        exact hyc hxY
      · have h1 := (relIndex_two_mem hrel2 hsR hsY).2 x hxR hxY
        rw [← hy] at h1
        have h3 := mul_mem hsc (hyc h1)
        rwa [mul_inv_cancel_left] at h3
  have hsame : ∀ y : P, zpowers y = Y → ∀ s ∈ R, s ∉ Y → ∀ s' ∈ R, s' ∉ Y →
      s'⁻¹ * y * s' = s⁻¹ * y * s ∧ (s⁻¹ * y * s = y⁻¹ → s' ^ 2 = s ^ 2) := by
    intro y hy s hsR hsY s' hs'R hs'Y
    have hu := hdiff (hnot1 s hsR hsY) s hsR hsY s' hs'R hs'Y
    set u := s⁻¹ * s' with hudef
    have hs' : s' = s * u := by rw [hudef]; group
    have hsy : s⁻¹ * y * s ∈ Y := by
      have := (inferInstance : Y.Normal).conj_mem y (hy ▸ mem_zpowers y) s⁻¹
      simpa using this
    refine ⟨?_, fun hinv => ?_⟩
    · rw [hs']
      have h1 : (s * u)⁻¹ * y * (s * u) = u⁻¹ * (s⁻¹ * y * s) * u := by group
      rw [h1, mul_comm_of_mem_of_isCyclic hYcyc (Y.inv_mem hu) hsy]
      group
    · rw [← hy] at hu
      obtain ⟨i, hi⟩ := mem_zpowers_iff.mp hu
      have hsu : s⁻¹ * u * s = u⁻¹ := by
        rw [← hi]
        have h1 := conj_zpow (a := s⁻¹) (b := y) (i := i)
        rw [inv_inv] at h1
        rw [← h1, hinv, inv_zpow]
      rw [hs']
      calc (s * u) ^ 2 = s ^ 2 * (s⁻¹ * u * s) * u := by rw [pow_two, pow_two]; group
        _ = s ^ 2 := by rw [hsu, inv_mul_cancel_right]
  have hexist : ∀ y : P, zpowers y = Y → ∃ i : Fin 4, ResidualAlternative R Y y k i := by
    intro y hy
    have hord : orderOf y = 2 ^ k := by rw [← Nat.card_zpowers, hy, hYk]
    have hyn : y ^ 2 ^ k = 1 := by rw [← hord]; exact pow_orderOf_eq_one y
    have hyR : y ∈ R := hYR (hy ▸ mem_zpowers y)
    by_cases hD : D = ⊤
    · exact ⟨0, (hRY_iff.mpr hD : R = Y)⟩
    have h2 : D.index = 2 := by
      have : D.index ≠ 1 := fun h => hD (index_eq_one.mp h)
      omega
    obtain ⟨s, hsR, hsY⟩ : ∃ s ∈ R, s ∉ Y := by
      by_contra hno
      push Not at hno
      exact hD (hRY_iff.mp (le_antisymm hno hYR))
    obtain ⟨j, hj, hjj, hfix, hss⟩ := hanalysis y hy h2 s hsR hsY
    obtain ⟨c, hc⟩ : ∃ c : ℤ, s * s = y ^ c := by
      rw [← hy] at hss
      obtain ⟨c, hc⟩ := mem_zpowers_iff.mp hss
      exact ⟨c, hc.symm⟩
    have hcf : (2 : ℤ) ^ (k - 1) ∣ c := by
      rw [← hfix c, ← hc]
      group
    obtain ⟨f, hf⟩ := hcf
    have hcard := hcardR h2
    have hpos : 0 < 2 ^ k := by positivity
    have hcard' : Nat.card R = 2 * 2 ^ k := by rw [hcard, pow_succ, mul_comm]
    have hk2 : (2 : ℤ) ^ k = 2 * 2 ^ (k - 1) := by
      rw [← pow_succ']
      congr 1
      omega
    have heq := zpow_eq_zpow_iff_two_pow_dvd hord
    have hs2 : s ^ 2 = 1 ∨ s ^ 2 = y ^ 2 ^ (k - 1) := by
      rcases Int.even_or_odd f with ⟨g, hg⟩ | ⟨g, hg⟩
      · left
        rw [pow_two, hc, ← zpow_zero y, heq, hk2]
        exact ⟨-g, by rw [hf, hg]; ring⟩
      · right
        rw [pow_two, hc, ← zpow_natCast, heq, hk2]
        exact ⟨-g, by rw [hf, hg]; push_cast; ring⟩
    have hcl := hgenR y hy s hsR hsY
    rcases hjj with hjinv | hjsd
    · have hinv : s⁻¹ * y * s = y⁻¹ := hj.trans hjinv
      rcases hs2 with hs1 | hsz
      · refine ⟨1, ?_⟩
        show ResidualDihedral R Y y k
        refine ⟨s, hsR, hsY, hcard, hs1, hinv, ?_⟩
        exact exists_presentedGroup_mulEquiv hpos hyR hsR hyn (by rw [hs1, zpow_zero])
          (by rw [hinv, zpow_neg_one]) hcl hcard'
      · refine ⟨2, ?_⟩
        show ResidualQuaternion R Y y k
        refine ⟨s, hsR, hsY, hcard, hsz, hinv, ?_⟩
        exact exists_presentedGroup_mulEquiv hpos hyR hsR hyn
          (by rw [hsz, ← zpow_natCast]; push_cast; rfl) (by rw [hinv, zpow_neg_one]) hcl hcard'
    · have hsd : s⁻¹ * y * s = y ^ (-1 + 2 ^ (k - 1) : ℤ) := hj.trans hjsd
      refine ⟨3, ?_⟩
      show ResidualSemidihedral R Y y k
      rcases hs2 with hs1 | hsz
      · refine ⟨s, hsR, hsY, hcard, hs1, hsd, ?_⟩
        exact exists_presentedGroup_mulEquiv hpos hyR hsR hyn (by rw [hs1, zpow_zero]) hsd hcl
          hcard'
      ·
        have hs'R : s * y ∈ R := R.mul_mem hsR hyR
        have hs'Y : s * y ∉ Y := fun h => hsY (by
          have := Y.mul_mem h (Y.inv_mem (hy ▸ mem_zpowers y))
          rwa [mul_inv_cancel_right] at this)
        have hsd' : (s * y)⁻¹ * y * (s * y) = y ^ (-1 + 2 ^ (k - 1) : ℤ) := by
          have h1 : (s * y)⁻¹ * y * (s * y) = y⁻¹ * (s⁻¹ * y * s) * y := by group
          rw [h1, hsd]
          group
        have hs'1 : (s * y) ^ 2 = 1 := by
          have h1 : (s * y) ^ 2 = s ^ 2 * (s⁻¹ * y * s) * y := by
            rw [pow_two, pow_two]
            group
          have h3 : y ^ 2 ^ (k - 1) * y ^ (-1 + 2 ^ (k - 1) : ℤ) * y = y ^ ((2 : ℤ) ^ k) := by
            rw [← zpow_natCast, hk2]
            push_cast
            group
          have h4 : y ^ ((2 : ℤ) ^ k) = y ^ (2 ^ k : ℕ) := by
            rw [← zpow_natCast]
            push_cast
            rfl
          rw [h1, hsz, hsd, h3, h4, hyn]
        have hcl' := hgenR y hy (s * y) hs'R hs'Y
        refine ⟨s * y, hs'R, hs'Y, hcard, hs'1, hsd', ?_⟩
        exact exists_presentedGroup_mulEquiv hpos hyR hs'R hyn (by rw [hs'1, zpow_zero]) hsd'
          hcl' hcard'
  have huniq : ∀ y : P, zpowers y = Y → ∀ i i' : Fin 4, ResidualAlternative R Y y k i →
      ResidualAlternative R Y y k i' → i = i' := by
    intro y hy i i' hi hi'
    have hord : orderOf y = 2 ^ k := by rw [← Nat.card_zpowers, hy, hYk]
    have hz1 : y ^ 2 ^ (k - 1) ≠ 1 := by
      intro h
      have h1 := orderOf_pow_two_pow_pred (by omega) hord
      rw [h, orderOf_one] at h1
      omega
    have hsd_ne : y⁻¹ ≠ y ^ (-1 + 2 ^ (k - 1) : ℤ) := by
      intro h
      apply hz1
      rw [← zpow_natCast, Nat.cast_pow, Nat.cast_ofNat]
      have h1 : y ^ (-1 + 2 ^ (k - 1) : ℤ) = y⁻¹ * y ^ ((2 : ℤ) ^ (k - 1)) := by
        rw [zpow_add, zpow_neg_one]
      rw [h1] at h
      have h2 := congrArg (fun x => y * x) h
      simp only [mul_inv_cancel, mul_inv_cancel_left] at h2
      exact h2.symm
    have hne0 : ∀ i : Fin 4, i ≠ 0 → ResidualAlternative R Y y k i → ∃ s ∈ R, s ∉ Y := by
      intro i hi0 h
      fin_cases i
      · exact absurd rfl hi0
      · obtain ⟨s, hsR, hsY, -⟩ := (h : ResidualDihedral R Y y k)
        exact ⟨s, hsR, hsY⟩
      · obtain ⟨s, hsR, hsY, -⟩ := (h : ResidualQuaternion R Y y k)
        exact ⟨s, hsR, hsY⟩
      · obtain ⟨s, hsR, hsY, -⟩ := (h : ResidualSemidihedral R Y y k)
        exact ⟨s, hsR, hsY⟩
    have hRY0 : ResidualAlternative R Y y k 0 → ∀ s ∈ R, s ∉ Y → False := fun h s hsR hsY =>
      hsY ((h : R = Y) ▸ hsR)
    have h12 : ResidualDihedral R Y y k → ResidualQuaternion R Y y k → False := by
      rintro ⟨s, hsR, hsY, -, hs2, hsy, -⟩ ⟨s', hs'R, hs'Y, -, hs'2, -, -⟩
      have h1 := (hsame y hy s hsR hsY s' hs'R hs'Y).2 hsy
      rw [hs'2, hs2] at h1
      exact hz1 h1
    have hinv_sd : ∀ s ∈ R, s ∉ Y → s⁻¹ * y * s = y⁻¹ → ∀ s' ∈ R, s' ∉ Y →
        s'⁻¹ * y * s' = y ^ (-1 + 2 ^ (k - 1) : ℤ) → False := by
      intro s hsR hsY hsy s' hs'R hs'Y hs'y
      have h1 := (hsame y hy s hsR hsY s' hs'R hs'Y).1
      rw [hs'y, hsy] at h1
      exact hsd_ne h1.symm
    have h13 : ResidualDihedral R Y y k → ResidualSemidihedral R Y y k → False := by
      rintro ⟨s, hsR, hsY, -, -, hsy, -⟩ ⟨s', hs'R, hs'Y, -, -, hs'y, -⟩
      exact hinv_sd s hsR hsY hsy s' hs'R hs'Y hs'y
    have h23 : ResidualQuaternion R Y y k → ResidualSemidihedral R Y y k → False := by
      rintro ⟨s, hsR, hsY, -, -, hsy, -⟩ ⟨s', hs'R, hs'Y, -, -, hs'y, -⟩
      exact hinv_sd s hsR hsY hsy s' hs'R hs'Y hs'y
    fin_cases i <;> fin_cases i'
    all_goals first
      | rfl
      | (exfalso; exact h12 hi hi')
      | (exfalso; exact h12 hi' hi)
      | (exfalso; exact h13 hi hi')
      | (exfalso; exact h13 hi' hi)
      | (exfalso; exact h23 hi hi')
      | (exfalso; exact h23 hi' hi)
      | (exfalso; obtain ⟨s, hsR, hsY⟩ := hne0 _ (by decide) hi'; exact hRY0 hi s hsR hsY)
      | (exfalso; obtain ⟨s, hsR, hsY⟩ := hne0 _ (by decide) hi; exact hRY0 hi' s hsR hsY)
  have hcenter : R ≠ Y → center P = zpowers z := by
    intro hne
    have hD : D ≠ ⊤ := fun h => hne (hRY_iff.mpr h)
    have h2 : D.index = 2 := by
      have : D.index ≠ 1 := fun h => hD (index_eq_one.mp h)
      omega
    obtain ⟨y, hy⟩ : ∃ y : P, zpowers y = Y := by
      obtain ⟨⟨y, hyY⟩, hgen⟩ := hYcyc.exists_generator
      refine ⟨y, le_antisymm (zpowers_le.mpr hyY) fun x hx => ?_⟩
      obtain ⟨i, hi⟩ := hgen ⟨x, hx⟩
      exact ⟨i, congrArg Subtype.val hi⟩
    have hord : orderOf y = 2 ^ k := by rw [← Nat.card_zpowers, hy, hYk]
    obtain ⟨s, hsR, hsY⟩ : ∃ s ∈ R, s ∉ Y := by
      by_contra hno
      push Not at hno
      exact hne (le_antisymm hno hYR)
    obtain ⟨j, hj, -, hfix, -⟩ := hanalysis y hy h2 s hsR hsY
    have hyz : y ^ 2 ^ (k - 1) = z :=
      eq_of_orderOf_eq_two_of_isCyclic_subgroup hYcyc (hy ▸ pow_mem (mem_zpowers y) _) hzY
        (orderOf_pow_two_pow_pred (by omega) hord) hz
    apply le_antisymm
    · intro c hc
      have hcER : c ∈ E ⊔ R := hER ▸ mem_top c
      obtain ⟨e, he, r, hr, rfl⟩ := mem_sup_of_normal_right.mp hcER
      have hrE : ∀ e' ∈ E, e' * r = r * e' := by
        intro e' he'
        have h1 : r ∈ centralizer (E : Set P) := hR ▸ hr
        exact mem_centralizer_iff.mp h1 e' he'
      have heZ : e ∈ zpowers z := by
        rw [← hEc]
        refine ⟨⟨e, he⟩, mem_center_iff.mpr fun e' => Subtype.ext ?_, rfl⟩
        have h1 := mem_center_iff.mp hc e'
        have h2 := hrE e' e'.2
        show (e' : P) * e = e * e'
        calc (e' : P) * e = e' * (e * r) * r⁻¹ := by group
          _ = e * r * e' * r⁻¹ := by rw [h1]
          _ = e * (r * e') * r⁻¹ := by group
          _ = e * (e' * r) * r⁻¹ := by rw [h2]
          _ = e * e' := by group
      have hcR : e * r ∈ R := R.mul_mem (zpowers_le.mpr hzR heZ) hr
      have hcY : e * r ∈ Y := by
        rw [← hRY]
        exact ⟨hcR, mem_centralizer_iff.mpr fun y' _ => (mem_center_iff.mp hc y')⟩
      have hsc := mem_center_iff.mp hc s
      rw [← hy] at hcY
      obtain ⟨i, hi⟩ := mem_zpowers_iff.mp hcY
      have hfixc : s⁻¹ * y ^ i * s = y ^ i := by
        rw [hi]
        calc s⁻¹ * (e * r) * s = s⁻¹ * (s * (e * r)) := by rw [hsc]; group
          _ = e * r := by group
      obtain ⟨g, hg⟩ := (hfix i).mp hfixc
      have hyz' : y ^ ((2 : ℤ) ^ (k - 1)) = z := by
        rw [← hyz, ← zpow_natCast]
        push_cast
        rfl
      rw [← hi, hg, zpow_mul, hyz']
      exact zpow_mem (mem_zpowers z) g
    · rw [zpowers_le]
      exact hzc
  refine ⟨hRD, hrel, fun y hy => ?_, hRY_iff, hcenter⟩
  obtain ⟨i, hi⟩ := hexist y hy
  exact ⟨i, hi, fun i' hi' => huniq y hy i' i hi' hi⟩

theorem involution_outside_critical_action {P : Type*} [Group P] [Finite P] {D Y T : Subgroup P}
    [Y.Normal] {z : P} (hz : orderOf z = 2) (hzY : z ∈ Y) (hYcyc : IsCyclic Y) {k : ℕ}
    (hk : 3 ≤ k) (hYk : Nat.card Y = 2 ^ k) (hTY : T ≤ Y) (hT4 : Nat.card T = 4)
    (hcT : centralizer (T : Set P) = D) (hidx : D.index ≤ 2) {a : P} (ha : orderOf a = 2)
    (haD : a ∉ D) :
    D.index = 2 ∧ (∀ t ∈ T, a * t * a⁻¹ = t⁻¹) ∧ Y ⊓ centralizer {a} = zpowers z ∧
      ∀ t ∈ T, orderOf t = 4 → t⁻¹ * a * t = a * z := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2 : D.index = 2 := by
    have h1 : D ≠ ⊤ := fun h => haD (h ▸ mem_top a)
    have h3 : D.index ≠ 1 := fun h => h1 (index_eq_one.mp h)
    have h4 : D.index ≠ 0 := index_ne_zero_of_finite
    omega
  obtain ⟨y, hy⟩ : ∃ y : P, zpowers y = Y := by
    obtain ⟨⟨y, hyY⟩, hgen⟩ := hYcyc.exists_generator
    refine ⟨y, le_antisymm (zpowers_le.mpr hyY) fun x hx => ?_⟩
    obtain ⟨i, hi⟩ := hgen ⟨x, hx⟩
    exact ⟨i, congrArg Subtype.val hi⟩
  have hord : orderOf y = 2 ^ k := by rw [← Nat.card_zpowers, hy, hYk]
  have hainv : a⁻¹ = a := by
    have h1 := pow_orderOf_eq_one a
    rw [ha, pow_two] at h1
    exact inv_eq_of_mul_eq_one_right h1
  obtain ⟨j, hj⟩ : ∃ j : ℤ, a⁻¹ * y * a = y ^ j := by
    have h1 : a⁻¹ * y * a ∈ Y := by
      have := (inferInstance : Y.Normal).conj_mem y (hy ▸ mem_zpowers y) a⁻¹
      simpa using this
    rw [← hy] at h1
    obtain ⟨j, hj⟩ := mem_zpowers_iff.mp h1
    exact ⟨j, hj.symm⟩
  have hT : ∃ t ∈ zpowers y, t ^ 4 = 1 ∧ a⁻¹ * t * a ≠ t := by
    by_contra hno
    push Not at hno
    apply haD
    rw [← hcT, mem_centralizer_iff]
    intro t ht
    have h1 := hno t (hy ▸ hTY ht) (by
      have := pow_card_eq_one' (G := T) (x := ⟨t, ht⟩)
      rw [hT4] at this
      exact congrArg Subtype.val this)
    calc t * a = a * (a⁻¹ * t * a) := by group
      _ = a * t := by rw [h1]
  have hx2 : a ^ 2 * y = y * a ^ 2 := by
    rw [← ha, pow_orderOf_eq_one, one_mul, mul_one]
  obtain ⟨-, hfix, hinv⟩ := conj_exponent_of_moves_four hk hord hj hx2 hT
  have hT4' : ∀ t ∈ T, t ^ 4 = 1 := fun t ht => by
    have := pow_card_eq_one' (G := T) (x := ⟨t, ht⟩)
    rw [hT4] at this
    exact congrArg Subtype.val this
  have hinvT : ∀ t ∈ T, a * t * a⁻¹ = t⁻¹ := fun t ht => by
    have h1 := hinv t (hy ▸ hTY ht) (hT4' t ht)
    rw [hainv] at h1
    rw [hainv]
    exact h1
  refine ⟨h2, hinvT, ?_, fun t ht ht4 => ?_⟩
  · have hyz : y ^ 2 ^ (k - 1) = z :=
      eq_of_orderOf_eq_two_of_isCyclic_subgroup hYcyc (hy ▸ pow_mem (mem_zpowers y) _) hzY
        (orderOf_pow_two_pow_pred (by omega) hord) hz
    apply le_antisymm
    · rintro x ⟨hxY, hxa⟩
      rw [← hy] at hxY
      obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp hxY
      have h1 : a⁻¹ * y ^ i * a = y ^ i := by
        have h3 := mem_centralizer_singleton_iff.mp hxa
        rw [mul_assoc, h3]
        group
      obtain ⟨g, hg⟩ := (hfix i).mp h1
      have hyz' : y ^ ((2 : ℤ) ^ (k - 1)) = z := by
        rw [← hyz, ← zpow_natCast]
        push_cast
        rfl
      rw [hg, zpow_mul, hyz']
      exact zpow_mem (mem_zpowers z) g
    · rw [zpowers_le]
      refine ⟨hzY, mem_centralizer_singleton_iff.mpr ?_⟩
      have hzy : z ∈ zpowers y := hy ▸ hzY
      obtain ⟨i, hi⟩ := mem_zpowers_iff.mp hzy
      have h1 : y ^ 2 ^ (k - 1) = z :=
        eq_of_orderOf_eq_two_of_isCyclic_subgroup hYcyc (hy ▸ pow_mem (mem_zpowers y) _) hzY
          (orderOf_pow_two_pow_pred (by omega) hord) hz
      have h3 : a⁻¹ * z * a = z := by
        rw [← h1, ← zpow_natCast, (hfix _).mpr]
        exact ⟨1, by push_cast; ring⟩
      calc z * a = a * (a⁻¹ * z * a) := by group
        _ = a * z := by rw [h3]
  ·
    have h1 : a⁻¹ * t * a = t⁻¹ := hinv t (hy ▸ hTY ht) (hT4' t ht)
    have ht2 : t ^ 2 = z := by
      have h3 : orderOf (t ^ 2) = 2 := by
        rw [orderOf_pow' t (by norm_num), ht4]
        norm_num
      exact eq_of_orderOf_eq_two_of_isCyclic_subgroup hYcyc (pow_mem (hTY ht) 2) hzY h3 hz
    calc t⁻¹ * a * t = a * (a⁻¹ * t⁻¹ * a) * t := by group
      _ = a * (a⁻¹ * t * a)⁻¹ * t := by group
      _ = a * t ^ 2 := by rw [h1, inv_inv, pow_two, mul_assoc]
      _ = a * z := by rw [ht2]


theorem mem_center_subgroupOf_iff {G : Type*} [Group G] {M Q : Subgroup G} (hQM : Q ≤ M)
    {D : Subgroup Q} (d : (D.map Q.subtype).subgroupOf M) :
    d ∈ center ((D.map Q.subtype).subgroupOf M) ↔
      ((d : M) : G) ∈ ((center D).map D.subtype).map Q.subtype := by
  rw [map_center_map_subtype_eq, CFSG.SectionRank.Ccomm.map_center_subtype, mem_center_iff]
  have hd : ((d : M) : G) ∈ D.map Q.subtype := mem_subgroupOf.mp d.2
  constructor
  · intro h
    refine ⟨hd, mem_centralizer_iff.mpr fun x hx => ?_⟩
    have hxM : x ∈ M := (map_subtype_le D).trans hQM hx
    have h1 := h ⟨⟨x, hxM⟩, mem_subgroupOf.mpr hx⟩
    exact congrArg (fun w : (D.map Q.subtype).subgroupOf M => ((w : M) : G)) h1
  · rintro ⟨-, hc⟩ x
    apply Subtype.ext
    apply Subtype.ext
    exact mem_centralizer_iff.mp hc _ (mem_subgroupOf.mp x.2)

theorem critical_quotient_facts
    {G : Type*} [Group G] [Finite G]
    (hchar : IsCharacteristicPType G 2) (he : 4 ≤ CFSG.twoLocalOddRank G) {M B : Subgroup G}
    (hM : GLAIsMaxTwoLocal M) (hsym : GLASymplecticType (pCoreOf 2 M)) (hB : GLAIsBmax 3 B)
    (hBM : B ≤ M) {Q : Subgroup G} (hQ : Q = CFSG.inSubgroup (CFSG.pCore 2) M) {r : ℕ}
    (hr : r = GLATwoLocalRank 3 G) {D : Subgroup Q} (hD : ThompsonCritical D) :
    ∃ u : ℕ, 2 ≤ u ∧ r ≤ u ∧ Nat.card (D ⧸ center D) = 2 ^ (2 * u) ∧ ¬ IsCyclic D ∧
      ∀ m ∈ M, (∀ x ∈ D.map Q.subtype,
        m * x * m⁻¹ * x⁻¹ ∈ ((center D).map D.subtype).map Q.subtype) → m ∈ Q := by
  classical
  obtain ⟨⟨z₁, -, -, -, -, hMNQ, -, -⟩, -⟩ :=
    gf2_witness_centralizer_and_rank hchar hM hsym hB hBM hQ hr
  have hQM : Q ≤ M := by
    rw [hQ]
    exact map_subtype_le _
  obtain ⟨-, -, ⟨eD⟩⟩ := critical_subgroup_transport_to_core hQ hD
  have h := (gf2_critical_quotient_and_width_at_rank_four hchar he hM hsym hB hBM hQ hr).2 D hD _
    rfl
  obtain ⟨-, -, z, -, -, -, hrest⟩ := h
  obtain ⟨hEA, hrest⟩ := hrest
  obtain ⟨b, -, -, -, -, hwex⟩ := hrest
  obtain ⟨w, hw2, hw, -, hρex, -, hrw, -, hncyc⟩ := hwex
  obtain ⟨ρ, hρ, hρker, -⟩ := hρex
  have hcard' : Nat.card ((D.map Q.subtype).subgroupOf M ⧸
      center ((D.map Q.subtype).subgroupOf M)) = 2 ^ (2 * w) := by
    rw [natCard_eq_two_pow_finrank, hw]
  have hcard : Nat.card (D ⧸ center D) = 2 ^ (2 * w) := by
    rw [← hcard']
    exact Nat.card_congr (QuotientGroup.congr _ _ eD (map_center_eq eD)).toEquiv
  have hMND : M ≤ normalizer ((D.map Q.subtype : Subgroup G) : Set G) :=
    hMNQ.le.trans (normalizer_le_normalizer_map_of_characteristic hD.1)
  refine ⟨w, hw2, hrw, hcard, hncyc, fun m hm htriv => ?_⟩
  have hconj : ∀ x : (D.map Q.subtype).subgroupOf M,
      ((⟨m, hm⟩ : M) * x * (⟨m, hm⟩ : M)⁻¹ : M) ∈ (D.map Q.subtype).subgroupOf M := by
    intro x
    rw [mem_subgroupOf]
    exact (mem_normalizer_iff.mp (hMND hm) _).mp (mem_subgroupOf.mp x.2)
  have h1 : ρ ⟨m, hm⟩ = 1 := by
    apply Units.ext
    apply LinearMap.ext
    intro v
    obtain ⟨x, hx⟩ := QuotientGroup.mk_surjective (Additive.toMul v)
    have hv : v = Additive.ofMul (x : (D.map Q.subtype).subgroupOf M ⧸
        center ((D.map Q.subtype).subgroupOf M)) := by
      rw [hx]
      rfl
    rw [hv, hρ ⟨m, hm⟩ x ⟨_, hconj x⟩ rfl, Units.val_one, Module.End.one_apply]
    congr 1
    rw [QuotientGroup.eq, mem_center_subgroupOf_iff hQM]
    have hxD : ((x : M) : G) ∈ D.map Q.subtype := mem_subgroupOf.mp x.2
    have h2 := htriv _ hxD
    have hcen : ∀ c ∈ ((center D).map D.subtype).map Q.subtype, ∀ y ∈ D.map Q.subtype,
        y * c = c * y := by
      intro c hc y hy
      rw [map_center_map_subtype_eq, CFSG.SectionRank.Ccomm.map_center_subtype] at hc
      exact mem_centralizer_iff.mp hc.2 y hy
    set c := m * ((x : M) : G) * m⁻¹ * ((x : M) : G)⁻¹ with hcdef
    have h3 : (((((⟨_, hconj x⟩ : (D.map Q.subtype).subgroupOf M)⁻¹ * x :
        (D.map Q.subtype).subgroupOf M) : M) : G)) = ((x : M) : G)⁻¹ * c⁻¹ * ((x : M) : G) := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, hcdef]
      group
    rw [h3]
    have h4 : ((x : M) : G)⁻¹ * c⁻¹ * ((x : M) : G) = c⁻¹ := by
      rw [mul_assoc, ← hcen _ (inv_mem h2) _ hxD, inv_mul_cancel_left]
    rw [h4]
    exact inv_mem h2
  have h2 : (⟨m, hm⟩ : M) ∈ CFSG.pCore 2 M := by
    rw [← hρker]
    exact h1
  rw [hQ]
  exact ⟨⟨m, hm⟩, h2, rfl⟩


theorem exists_prod_mulEquiv_sup_apply {G : Type*} [Group G] {H K : Subgroup G}
    (hcomm : ∀ h ∈ H, ∀ k ∈ K, h * k = k * h) (hHK : H ⊓ K = ⊥) :
    ∃ θ : H × K ≃* (H ⊔ K : Subgroup G), ∀ (h : H) (k : K), (θ (h, k) : G) = h * k := by
  have hc : ∀ (h : H) (k : K), Commute (H.subtype h) (K.subtype k) := fun h k =>
    hcomm h h.2 k k.2
  let f : H × K →* G := H.subtype.noncommCoprod K.subtype hc
  have hf : Function.Injective f := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    rintro ⟨h, k⟩ hhk
    have h1 : (h : G) * k = 1 := hhk
    have hk : (k : G) = (h : G)⁻¹ := eq_inv_of_mul_eq_one_right h1
    have hmem : (h : G) ∈ H ⊓ K := ⟨h.2, by rw [← inv_inv (h : G), ← hk]; exact K.inv_mem k.2⟩
    rw [hHK, mem_bot] at hmem
    have hk1 : (k : G) = 1 := by rw [hk, hmem, inv_one]
    rw [mem_bot]
    exact Prod.ext (Subtype.ext hmem) (Subtype.ext hk1)
  have hrange : f.range = H ⊔ K :=
    (MonoidHom.noncommCoprod_range H.subtype K.subtype hc).trans
      (by rw [range_subtype, range_subtype])
  exact ⟨(MonoidHom.ofInjective hf).trans (MulEquiv.subgroupCongr hrange), fun _ _ => rfl⟩

theorem commuting_involutions_closure {G : Type*} [Group G] {a z : G} (ha : orderOf a = 2)
    (hz : orderOf z = 2) (hne : a ≠ z) (hcomm : a * z = z * a) :
    IsElemAbelian 2 (closure {a, z}) ∧ Nat.card (closure {a, z}) = 4 ∧
      ∀ x ∈ closure {a, z}, x = 1 ∨ x = a ∨ x = z ∨ x = a * z := by
  have ha2 : a * a = 1 := by rw [← pow_two, ← ha, pow_orderOf_eq_one]
  have hz2 : z * z = 1 := by rw [← pow_two, ← hz, pow_orderOf_eq_one]
  have ha1 : a ≠ 1 := fun h => by rw [h, orderOf_one] at ha; omega
  have hcl : closure ({a, z} : Set G) = zpowers a ⊔ zpowers z := by
    rw [Set.insert_eq, Subgroup.closure_union, zpowers_eq_closure, zpowers_eq_closure]
  have hc : ∀ h ∈ zpowers a, ∀ k ∈ zpowers z, h * k = k * h := by
    rintro _ ⟨i, rfl⟩ _ ⟨l, rfl⟩
    exact (Commute.zpow_zpow hcomm i l).eq
  have hinf : zpowers a ⊓ zpowers z = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hxa, hxz⟩
    rcases eq_one_or_eq_of_mem_zpowers ha hxa with h | h
    · rw [h]
      exact one_mem _
    · subst h
      rcases eq_one_or_eq_of_mem_zpowers hz hxz with h | h
      · exact absurd h ha1
      · exact absurd h hne
  obtain ⟨θ, hθ⟩ := exists_prod_mulEquiv_sup_apply hc hinf
  have hmem : ∀ x ∈ closure ({a, z} : Set G), x = 1 ∨ x = a ∨ x = z ∨ x = a * z := by
    intro x hx
    rw [hcl] at hx
    obtain ⟨⟨h, k⟩, hhk⟩ := θ.surjective ⟨x, hx⟩
    have hx' : x = h * k := by
      rw [← hθ h k, hhk]
    rcases eq_one_or_eq_of_mem_zpowers ha h.2 with h1 | h1 <;>
      rcases eq_one_or_eq_of_mem_zpowers hz k.2 with h2 | h2 <;>
      simp [hx', h1, h2]
  refine ⟨⟨isMulCommutative_closure ?_, fun x hx => ?_⟩, ?_, hmem⟩
  · rw [Set.pairwise_pair]
    exact fun _ => ⟨hcomm, hcomm.symm⟩
  · rcases hmem x hx with rfl | rfl | rfl | rfl
    · exact one_pow 2
    · rw [pow_two, ha2]
    · rw [pow_two, hz2]
    · rw [pow_two]
      calc a * z * (a * z) = a * (z * a) * z := by group
        _ = a * (a * z) * z := by rw [hcomm]
        _ = 1 := by rw [← mul_assoc, ha2, one_mul, hz2]
  · rw [hcl, ← Nat.card_congr θ.toEquiv, Nat.card_prod, Nat.card_zpowers, Nat.card_zpowers, ha, hz]

theorem layer_centralizer_eq {G : Type*} [Group G] {M Q : Subgroup G} {D L : Subgroup Q}
    (hDLY : ∀ d ∈ D, ∃ l ∈ L, ∃ y ∈ (center D).map D.subtype, d = l * y)
    (hMNY : M ≤ normalizer ((((center D).map D.subtype).map Q.subtype : Subgroup G) : Set G))
    (hfaith : ∀ m ∈ M, (∀ x ∈ D.map Q.subtype,
      m * x * m⁻¹ * x⁻¹ ∈ ((center D).map D.subtype).map Q.subtype) → m ∈ Q)
    (hcL : centralizer (L : Set Q) = (center D).map D.subtype)
    (hYM : ((center D).map D.subtype).map Q.subtype ≤ M) :
    M ⊓ centralizer ((L.map Q.subtype : Subgroup G) : Set G) =
      ((center D).map D.subtype).map Q.subtype := by
  have hcen : ∀ c ∈ ((center D).map D.subtype).map Q.subtype, ∀ y ∈ D.map Q.subtype,
      y * c = c * y := by
    intro c hc y hy
    rw [map_center_map_subtype_eq, CFSG.SectionRank.Ccomm.map_center_subtype] at hc
    exact mem_centralizer_iff.mp hc.2 y hy
  apply le_antisymm
  · rintro m ⟨hmM, hmL⟩
    have hmQ : m ∈ Q := by
      refine hfaith m hmM fun x hx => ?_
      obtain ⟨d, hd, rfl⟩ := hx
      obtain ⟨l, hl, y, hy, rfl⟩ := hDLY d hd
      have hlm : (l : G) * m = m * l := mem_centralizer_iff.mp hmL _ ⟨l, hl, rfl⟩
      have hyY : ((y : Q) : G) ∈ ((center D).map D.subtype).map Q.subtype := ⟨y, hy, rfl⟩
      have hmy := (mem_normalizer_iff.mp (hMNY hmM) _).mp hyY
      have hyD : y ∈ D := by
        obtain ⟨c, -, rfl⟩ := hy
        exact c.2
      have hlD : l ∈ D := by
        have h := D.mul_mem hd (D.inv_mem hyD)
        rwa [mul_inv_cancel_right] at h
      have hlDG : (l : G) ∈ D.map Q.subtype := ⟨l, hlD, rfl⟩
      set c := m * (y : G) * m⁻¹ * (y : G)⁻¹ with hc
      have hcY : c ∈ ((center D).map D.subtype).map Q.subtype := mul_mem hmy (inv_mem hyY)
      have h2 : m * ((l * y : Q) : G) * m⁻¹ * ((l * y : Q) : G)⁻¹ = (l : G) * c * (l : G)⁻¹ := by
        rw [hc]
        simp only [Subgroup.coe_mul]
        calc m * ((l : G) * y) * m⁻¹ * ((l : G) * y)⁻¹ =
              (m * l) * y * m⁻¹ * (y : G)⁻¹ * (l : G)⁻¹ := by group
          _ = (l * m) * y * m⁻¹ * (y : G)⁻¹ * (l : G)⁻¹ := by rw [hlm]
          _ = (l : G) * (m * y * m⁻¹ * (y : G)⁻¹) * (l : G)⁻¹ := by group
      show m * ((l * y : Q) : G) * m⁻¹ * ((l * y : Q) : G)⁻¹ ∈ _
      rw [h2, hcen c hcY _ hlDG, mul_inv_cancel_right]
      exact hcY
    have h1 : (⟨m, hmQ⟩ : Q) ∈ centralizer (L : Set Q) :=
      (coe_mem_centralizer_map_iff ⟨m, hmQ⟩).mp hmL
    rw [hcL] at h1
    exact ⟨⟨m, hmQ⟩, h1, rfl⟩
  · rintro _ ⟨y₀, hy₀, rfl⟩
    refine ⟨hYM ⟨y₀, hy₀, rfl⟩, ?_⟩
    have h1 : y₀ ∈ centralizer (L : Set Q) := by
      rw [hcL]
      exact hy₀
    exact (coe_mem_centralizer_map_iff y₀).mpr h1

end SteinbergBK

open SteinbergBK

theorem gf2_higher_center_residual_presentations_and_fusion
    {G : Type*} [Group G] [Finite G]
    (hchar : IsCharacteristicPType G 2) (he : 4 ≤ CFSG.twoLocalOddRank G) {M B : Subgroup G}
    (hM : GLAIsMaxTwoLocal M) (hsym : GLASymplecticType (pCoreOf 2 M)) (hB : GLAIsBmax 3 B)
    (hBM : B ≤ M) {Q : Subgroup G} (hQ : Q = CFSG.inSubgroup (CFSG.pCore 2) M) {z : G}
    (hzQ : z ∈ (center Q).map Q.subtype) (hz : orderOf z = 2) {r : ℕ}
    (hr : r = GLATwoLocalRank 3 G) {D : Subgroup Q} (hD : ThompsonCritical D)
    {Y₀ : Subgroup Q} (hY₀ : Y₀ = (center D).map D.subtype) {k : ℕ} (hk : 3 ≤ k)
    (hYk : Nat.card Y₀ = 2 ^ k) {T : Subgroup Q} (hTY : T ≤ Y₀) (hT4 : Nat.card T = 4) :
    centralizer (T : Set Q) = D ∧ D.index ≤ 2 ∧
    (∃ L : Subgroup Q, (L : Set Q) = {d | d ∈ D ∧ d ^ 4 = 1} ∧ L.Characteristic ∧
      M ≤ normalizer ((L.map Q.subtype : Subgroup G) : Set G) ∧
      centralizer (L : Set Q) = Y₀ ∧
      M ⊓ centralizer ((L.map Q.subtype : Subgroup G) : Set G) = Y₀.map Q.subtype) ∧
    ∃ u : ℕ, 2 ≤ u ∧ r ≤ u ∧ IsElementaryAbelian 2 (D ⧸ center D) ∧
      Nat.card (D ⧸ center D) = 2 ^ (2 * u) ∧
      M ≤ normalizer ((D.map Q.subtype : Subgroup G) : Set G) ∧
      M ≤ normalizer ((Y₀.map Q.subtype : Subgroup G) : Set G) ∧
      (∀ m ∈ M, (∀ x ∈ D.map Q.subtype, m * x * m⁻¹ * x⁻¹ ∈ Y₀.map Q.subtype) ↔ m ∈ Q) ∧
      (∀ K : Subgroup Q, ∃ S : Finset Q, S.card ≤ 2 * u + 2 ∧ closure (S : Set Q) = K) ∧
      (∃ E R : Subgroup Q, E ⊔ Y₀ = D ∧ E ⊔ R = ⊤ ∧ R = centralizer (E : Set Q) ∧ ⁅E, R⁆ = ⊥ ∧
        IsExtraspecialPGroup 2 E ∧ Nat.card E = 2 ^ (1 + 2 * u) ∧
        (E ⊓ R).map Q.subtype = zpowers z ∧ (E ⊓ Y₀).map Q.subtype = zpowers z ∧
        ((center E).map E.subtype).map Q.subtype = zpowers z ∧
        R ⊓ centralizer (Y₀ : Set Q) = Y₀) ∧
      (∀ E R : Subgroup Q, E ⊔ Y₀ = D → E ⊔ R = ⊤ → R = centralizer (E : Set Q) → ⁅E, R⁆ = ⊥ →
        IsExtraspecialPGroup 2 E → Nat.card E = 2 ^ (1 + 2 * u) →
        (E ⊓ R).map Q.subtype = zpowers z → (E ⊓ Y₀).map Q.subtype = zpowers z →
        ((center E).map E.subtype).map Q.subtype = zpowers z →
        R ⊓ centralizer (Y₀ : Set Q) = Y₀ →
        R ⊓ D = Y₀ ∧ Y₀.relIndex R = D.index ∧
        (∀ y : Q, zpowers y = Y₀ → ∃! i : Fin 4, ResidualAlternative R Y₀ y k i) ∧
        (R = Y₀ ↔ D = ⊤) ∧
        (R = Y₀ → center Q = Y₀ ∧ Set.range (fun g : G => g⁻¹ * z * g) ∩ (Q : Set G) = {z}) ∧
        (R ≠ Y₀ → (center Q).map Q.subtype = zpowers z)) ∧
      Set.range (fun g : G => g⁻¹ * z * g) ∩ (D.map Q.subtype : Set G) = {z} ∧
      ∀ a ∈ Set.range (fun g : G => g⁻¹ * z * g) ∩ (Q : Set G), a ≠ z →
        D.index = 2 ∧ a ∉ D.map Q.subtype ∧ (∀ t ∈ T.map Q.subtype, a * t * a⁻¹ = t⁻¹) ∧
        Y₀.map Q.subtype ⊓ centralizer {a} = zpowers z ∧
        (∀ t ∈ T.map Q.subtype, orderOf t = 4 → t⁻¹ * a * t = a * z) ∧
        IsElemAbelian 2 (closure {a, z}) ∧ Nat.card (closure {a, z}) = 4 ∧
        ∀ x ∈ closure {a, z}, x ≠ 1 → ∃ g : G, x = g⁻¹ * z * g := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨⟨z₁, -, -, -, -, hMNQ, -, -⟩, -, hQne, -⟩ :=
    gf2_witness_centralizer_and_rank hchar hM hsym hB hBM hQ hr
  have hQeq : pCoreOf 2 M = Q := by
    rw [hQ]
    unfold CFSG.Open.pCoreOf
    rfl
  have hsym' := hsym
  rw [hQeq] at hsym'
  obtain ⟨hQ2, hsymp⟩ := hsym'
  have : Nontrivial Q := (nontrivial_iff_ne_bot Q).mpr hQne
  have hQM : Q ≤ M := by
    rw [hQ]
    exact map_subtype_le _
  subst hY₀
  obtain ⟨-, hcp⟩ :=
    CFSG.RankThree.GroupTheory.SteinbergBY.symplectic_critical_subgroup_central_product hQ2 hsymp
  obtain ⟨-, hcyc, hZchar, z₀, hz₀Z, hz₀, -, hz₀c, huniqc, -, E₀, R₀, hEZ₀, hR₀, hER₀,
    hERc₀, hRZ₀, -, -, hcases, -, -⟩ := hcp D hD
  have hzz₀ : (z₀ : G) = z := by
    obtain ⟨zq, hzqc, hzq⟩ := hzQ
    have hzq' : (zq : G) = z := hzq
    have hzq2 : orderOf zq = 2 := by rw [← Subgroup.orderOf_coe, hzq']; exact hz
    rw [← huniqc zq hzqc hzq2, hzq']
  subst hzz₀
  obtain ⟨L, hLset, hLchar, -, hcT, hcL, hidx, -, -⟩ :=
    symplectic_critical_order_four_center_detects_core_action hQ2 hsymp hD hk hYk hTY hT4
  obtain ⟨u, hu2, hru, hDZcard, hncyc, hfaith⟩ :=
    critical_quotient_facts hchar he hM hsym hB hBM hQ hr hD
  obtain ⟨w', -, hEA, hDZw, -, hEx₀, hEcard₀, hE4₀, hER'₀, hEZ'₀, hEc₀, -⟩ :=
    hcases.resolve_left fun h => hncyc h.1
  have hw'u : u = w' := by
    have h1 : 2 ^ (2 * w') = 2 ^ (2 * u) := hDZw.symm.trans hDZcard
    have h2 := Nat.pow_right_injective (le_refl 2) h1
    omega
  subst hw'u
  have hY8 : 8 ≤ Nat.card (((center D).map D.subtype).map Q.subtype) := by
    rw [card_map_of_injective Q.subtype_injective, hYk]
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
  obtain ⟨hfus, hfus2⟩ := gf2_higher_critical_center_involution_fusion_exclusion hchar (by omega)
    hM hsym hB hBM hQ hzQ hz hD rfl hY8
  have hDn : D.Normal := @Subgroup.normal_of_characteristic _ _ D hD.1
  have hYn : ((center D).map D.subtype).Normal :=
    @Subgroup.normal_of_characteristic _ _ _ hZchar
  have hMNY : M ≤ normalizer ((((center D).map D.subtype).map Q.subtype : Subgroup G) : Set G) :=
    hMNQ.le.trans (normalizer_le_normalizer_map_of_characteristic hZchar)
  have hYD : (center D).map D.subtype ≤ D := map_subtype_le _
  have hYM : ((center D).map D.subtype).map Q.subtype ≤ M :=
    (map_mono hYD).trans ((map_subtype_le D).trans hQM)
  have hDLY : ∀ d ∈ D, ∃ l ∈ L, ∃ y ∈ (center D).map D.subtype, d = l * y := by
    intro d hd
    rw [← hEZ₀] at hd
    obtain ⟨e, he, y, hy, rfl⟩ := mem_sup_of_normal_right.mp hd
    refine ⟨e, ?_, y, hy, rfl⟩
    have h1 : e ∈ (L : Set Q) := by
      rw [hLset]
      exact ⟨hEZ₀ ▸ mem_sup_left he, hE4₀ e he⟩
    exact h1
  have hlayer := layer_centralizer_eq hDLY hMNY hfaith hcL hYM
  have hfaith' : ∀ m ∈ M, (∀ x ∈ D.map Q.subtype,
      m * x * m⁻¹ * x⁻¹ ∈ ((center D).map D.subtype).map Q.subtype) ↔ m ∈ Q := by
    intro m hm
    refine ⟨hfaith m hm, fun hmQ x hx => ?_⟩
    obtain ⟨d, hd, rfl⟩ := hx
    have h1 : ⁅(⟨m, hmQ⟩ : Q), d⁆ ∈ (center D).map D.subtype := by
      rw [CFSG.SectionRank.Ccomm.map_center_subtype]
      exact hD.2.2.1 (commutator_mem_commutator (mem_top _) hd)
    refine ⟨_, h1, ?_⟩
    simp [commutatorElement_def]
  let eZ : (center D).map D.subtype ≃* center D :=
    ((center D).equivMapOfInjective D.subtype D.subtype_injective).symm
  have hZDn : (center D).Normal := Subgroup.instNormalCenter
  have hZDcyc := eZ.isCyclic.mp hcyc
  have hgen : ∀ K : Subgroup Q, ∃ S : Finset Q, S.card ≤ 2 * u + 2 ∧ closure (S : Set Q) = K :=
    fun K => subgroup_generated_of_index_le_two hidx
      (fun K' => subgroup_generated_of_cyclic_normal_elementary (N := center D) hZDcyc hDZcard
        K') K
  have hzG : ∀ X : Subgroup Q, X = zpowers z₀ → X.map Q.subtype = zpowers (z₀ : G) := by
    rintro X rfl
    rw [MonoidHom.map_zpowers, coe_subtype]
  have hzG' : ∀ X : Subgroup Q, X.map Q.subtype = zpowers (z₀ : G) → X = zpowers z₀ := by
    intro X hX
    apply map_injective Q.subtype_injective
    rw [hX, MonoidHom.map_zpowers, coe_subtype]
  have hpair : ∀ E R : Subgroup Q, E ⊔ (center D).map D.subtype = D → E ⊔ R = ⊤ →
      R = centralizer (E : Set Q) → ⁅E, R⁆ = ⊥ → IsExtraspecialPGroup 2 E →
      Nat.card E = 2 ^ (1 + 2 * u) → (E ⊓ R).map Q.subtype = zpowers (z₀ : G) →
      (E ⊓ (center D).map D.subtype).map Q.subtype = zpowers (z₀ : G) →
      ((center E).map E.subtype).map Q.subtype = zpowers (z₀ : G) →
      R ⊓ centralizer (((center D).map D.subtype : Subgroup Q) : Set Q) =
        (center D).map D.subtype →
      R ⊓ D = (center D).map D.subtype ∧ ((center D).map D.subtype).relIndex R = D.index ∧
      (∀ y : Q, zpowers y = (center D).map D.subtype →
        ∃! i : Fin 4, ResidualAlternative R ((center D).map D.subtype) y k i) ∧
      (R = (center D).map D.subtype ↔ D = ⊤) ∧
      (R = (center D).map D.subtype → center Q = (center D).map D.subtype ∧
        Set.range (fun g : G => g⁻¹ * (z₀ : G) * g) ∩ (Q : Set G) = {(z₀ : G)}) ∧
      (R ≠ (center D).map D.subtype → (center Q).map Q.subtype = zpowers (z₀ : G)) := by
    intro E R hEY hER hR hERc _ _ hEiR _ hEc hRY
    obtain ⟨hRD, hrel, hex, hiff, hcen⟩ := residual_factor_alternatives hz₀ hz₀c hz₀Z hcyc hk
      hYk hYD hTY hT4 hcT hidx hEY hER hR hERc (hzG' _ hEiR) (hzG' _ hEc) hRY
    refine ⟨hRD, hrel, hex, hiff, fun hRY' => ⟨?_, ?_⟩, fun hne => hzG _ (hcen hne)⟩
    · have hDtop := hiff.mp hRY'
      rw [CFSG.SectionRank.Ccomm.map_center_subtype, hDtop, top_inf_eq]
      ext x
      rw [mem_center_iff, mem_centralizer_iff]
      exact ⟨fun h y _ => h y, fun h y => h y (mem_top y)⟩
    · have hDtop := hiff.mp hRY'
      have hDQ : D.map Q.subtype = Q := by
        rw [hDtop, ← MonoidHom.range_eq_map, range_subtype]
      have hset : ((D.map Q.subtype : Subgroup G) : Set G) = (Q : Set G) := by rw [hDQ]
      rw [← hset]
      exact hfus
  have hTcyc : IsCyclic T := (subgroupOfEquivOfLe hTY).isCyclic.mp inferInstance
  obtain ⟨t₀, ht₀⟩ := hTcyc.exists_generator
  have ht₀4 : orderOf (t₀ : Q) = 4 := by
    rw [Subgroup.orderOf_coe, orderOf_eq_card_of_forall_mem_zpowers ht₀, hT4]
  have hfusion : ∀ a ∈ Set.range (fun g : G => g⁻¹ * (z₀ : G) * g) ∩ (Q : Set G),
      a ≠ (z₀ : G) →
      D.index = 2 ∧ a ∉ D.map Q.subtype ∧ (∀ t ∈ T.map Q.subtype, a * t * a⁻¹ = t⁻¹) ∧
      ((center D).map D.subtype).map Q.subtype ⊓ centralizer {a} = zpowers (z₀ : G) ∧
      (∀ t ∈ T.map Q.subtype, orderOf t = 4 → t⁻¹ * a * t = a * z₀) ∧
      IsElemAbelian 2 (closure {a, (z₀ : G)}) ∧ Nat.card (closure {a, (z₀ : G)}) = 4 ∧
      ∀ x ∈ closure {a, (z₀ : G)}, x ≠ 1 → ∃ g : G, x = g⁻¹ * z₀ * g := by
    rintro a ⟨⟨g, rfl⟩, haQ⟩ hne
    obtain ⟨hnD, -⟩ := hfus2 g haQ hne
    have hord_a : orderOf (g⁻¹ * (z₀ : G) * g) = 2 := by
      have h1 := MulEquiv.orderOf_eq (MulAut.conj g⁻¹) (z₀ : G)
      rw [MulAut.conj_apply, inv_inv] at h1
      rw [h1, Subgroup.orderOf_coe]
      exact hz₀
    set a' : Q := ⟨g⁻¹ * z₀ * g, haQ⟩ with ha'def
    have ha' : orderOf a' = 2 := by
      rw [← Subgroup.orderOf_coe]
      exact hord_a
    have ha'D : a' ∉ D := fun h => hnD ⟨a', h, rfl⟩
    obtain ⟨h2, hinv, hcY, hconj⟩ := involution_outside_critical_action hz₀ hz₀Z hcyc hk hYk
      hTY hT4 hcT hidx ha' ha'D
    have hcomm : (g⁻¹ * (z₀ : G) * g) * (z₀ : G) = (z₀ : G) * (g⁻¹ * z₀ * g) :=
      congrArg Subtype.val (mem_center_iff.mp hz₀c a')
    obtain ⟨hEA2, hcard4, hmem4⟩ := commuting_involutions_closure hord_a
      (by rw [Subgroup.orderOf_coe]; exact hz₀) hne hcomm
    refine ⟨h2, hnD, ?_, ?_, ?_, hEA2, hcard4, ?_⟩
    · rintro _ ⟨t', ht', rfl⟩
      exact congrArg Subtype.val (hinv t' ht')
    · have hmap : (((center D).map D.subtype ⊓ centralizer {a'}).map Q.subtype : Subgroup G) =
          zpowers (z₀ : G) := hzG _ hcY
      rw [← hmap]
      ext x
      constructor
      · rintro ⟨⟨y, hy, rfl⟩, hxa⟩
        refine ⟨y, ⟨hy, mem_centralizer_singleton_iff.mpr (Subtype.ext ?_)⟩, rfl⟩
        exact mem_centralizer_singleton_iff.mp hxa
      · rintro ⟨y, ⟨hy, hya⟩, rfl⟩
        refine ⟨⟨y, hy, rfl⟩, mem_centralizer_singleton_iff.mpr ?_⟩
        exact congrArg Subtype.val (mem_centralizer_singleton_iff.mp hya)
    · rintro _ ⟨t', ht', rfl⟩ ht'4
      have h1 := hconj t' ht' (by rw [← Subgroup.orderOf_coe]; exact ht'4)
      exact congrArg Subtype.val h1
    · intro x hx hx1
      rcases hmem4 x hx with rfl | rfl | rfl | rfl
      · exact absurd rfl hx1
      · exact ⟨g, rfl⟩
      · exact ⟨1, by group⟩
      · have h1 := congrArg Subtype.val (hconj (t₀ : Q) t₀.2 ht₀4)
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, ha'def] at h1
        refine ⟨g * (t₀ : Q), ?_⟩
        rw [← h1]
        group
  refine ⟨hcT, hidx, ⟨L, hLset, hLchar,
    hMNQ.le.trans (normalizer_le_normalizer_map_of_characteristic hLchar), hcL, hlayer⟩,
    u, hu2, hru, hEA, hDZcard, hMNQ.le.trans (normalizer_le_normalizer_map_of_characteristic hD.1),
    hMNY, hfaith', hgen, ⟨E₀, R₀, hEZ₀, hER₀, hR₀, hERc₀, hEx₀, hEcard₀, hzG _ hER'₀, hzG _ hEZ'₀,
      hzG _ hEc₀, hRZ₀⟩, hpair, hfus, hfusion⟩

end CFSG.LocalAnalysis.GorensteinLyons
