module

public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.Int.Star
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.GroupTheory.IsPerfect
public import Mathlib.GroupTheory.SpecificGroups.ZGroup
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.LargeExtraspecial

open Subgroup
open scoped commutatorElement

namespace S63

section Defs

variable {G : Type*} [Group G]

@[expose] def CentConcl (C : Subgroup G) (t : G) : Prop :=
  ∀ N : Subgroup G, N ≤ C → (∀ c ∈ C, ∀ n ∈ N, c * n * c⁻¹ ∈ N) → IsPGroup 2 N → t ∈ N →
    2 ^ 4 ≤ Nat.card N →
      Nat.card N = 2 ^ 5 ∧ N ≤ zpowers t ⊔ ⁅N, C⁆ ∧ C ⊓ centralizer (N : Set G) ≤ N

@[expose] def FourClassesAtLeast (k : ℕ) (G : Type*) [Group G] : Prop :=
  ∀ x : G, orderOf x = 4 → k ≤ Nat.card {y : G // IsConj x y}

theorem CentConcl.of_map {H : Type*} [Group H] {f : G →* H} (hf : Function.Injective f)
    {C : Subgroup G} {t : G} (h : CentConcl (C.map f) (f t)) : CentConcl C t := by
  intro N hNC hNn hN2 htN hN16
  have hcard : Nat.card (N.map f) = Nat.card N := card_map_of_injective hf
  have hNn' : ∀ c ∈ C.map f, ∀ n ∈ N.map f, c * n * c⁻¹ ∈ N.map f := by
    rintro _ ⟨c, hc, rfl⟩ _ ⟨n, hn, rfl⟩
    exact ⟨c * n * c⁻¹, hNn c hc n hn, by simp⟩
  obtain ⟨h1, h2, h3⟩ := h (N.map f) (map_mono hNC) hNn' (hN2.map f) (mem_map_of_mem f htN)
    (hcard ▸ hN16)
  refine ⟨hcard ▸ h1, ?_, ?_⟩
  · rw [← MonoidHom.map_zpowers, ← map_commutator, ← Subgroup.map_sup] at h2
    exact (map_le_map_iff_of_injective hf).1 h2
  · rintro x ⟨hxC, hxN⟩
    have hx : f x ∈ C.map f ⊓ centralizer (N.map f : Set H) := by
      refine ⟨mem_map_of_mem f hxC, mem_centralizer_iff.mpr ?_⟩
      rintro _ ⟨n, hn, rfl⟩
      rw [← map_mul, ← map_mul, (mem_centralizer_iff.mp hxN) n hn]
    obtain ⟨y, hy, hyx⟩ := h3 hx
    exact hf hyx ▸ hy

theorem CentConcl.conj {C : Subgroup G} {t : G} (h : CentConcl C t) (g : G) :
    CentConcl (C.map (MulAut.conj g).toMonoidHom) (g * t * g⁻¹) := by
  refine CentConcl.of_map (f := (MulAut.conj g⁻¹).toMonoidHom) (MulAut.conj g⁻¹).injective ?_
  have hC : (C.map (MulAut.conj g).toMonoidHom).map (MulAut.conj g⁻¹).toMonoidHom = C := by
    rw [Subgroup.map_map]
    convert Subgroup.map_id C using 2
    ext x
    simp only [MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply,
      MulAut.conj_apply, inv_inv, MonoidHom.id_apply]
    group
  have ht : (MulAut.conj g⁻¹).toMonoidHom (g * t * g⁻¹) = t := by simp [mul_assoc]
  rw [hC, ht]
  exact h

theorem FourClassesAtLeast.of_mulEquiv {H : Type*} [Group H] {k : ℕ} (e : G ≃* H)
    (h : FourClassesAtLeast k H) : FourClassesAtLeast k G := by
  intro x hx
  refine (h (e x) (by rw [MulEquiv.orderOf_eq, hx])).trans (le_of_eq (Nat.card_congr ?_))
  refine (e.toEquiv.subtypeEquiv fun y => ?_).symm
  constructor
  · exact fun hxy => e.toMonoidHom.map_isConj hxy
  · intro hxy
    simpa using e.symm.toMonoidHom.map_isConj hxy

end Defs

section TwoB

variable {G : Type*} [Group G] [Finite G]

theorem false_of_twoB {C D N : Subgroup G} (hDC : D ≤ C) (hCD : C ≤ normalizer (D : Set G))
    (hD : IsSimpleGroup D) (hD60 : Nat.card D = 60)
    (hcent : Nat.card ↥(C ⊓ centralizer (D : Set G)) = 4) (hNC : N ≤ C)
    (hNn : ∀ c ∈ C, ∀ n ∈ N, c * n * c⁻¹ ∈ N) (hN2 : IsPGroup 2 N)
    (hN16 : 2 ^ 4 ≤ Nat.card N) : False := by
  have hnorm : ((N ⊓ D).subgroupOf D).Normal := by
    constructor
    intro x hx d
    rw [mem_subgroupOf] at hx ⊢
    obtain ⟨hxN, hxD⟩ := mem_inf.mp hx
    refine mem_inf.mpr ⟨?_, ?_⟩
    · simpa using hNn d (hDC d.2) x hxN
    · simpa using D.mul_mem (D.mul_mem d.2 hxD) (D.inv_mem d.2)
  rcases @IsSimpleGroup.eq_bot_or_eq_top_of_normal _ _ hD _ hnorm with hbot | htop
  · have hle : N ≤ C ⊓ centralizer (D : Set G) := by
      intro n hn
      refine mem_inf.mpr ⟨hNC hn, mem_centralizer_iff.mpr fun d hd => ?_⟩
      have hcomm : n * d * n⁻¹ * d⁻¹ ∈ N ⊓ D := by
        refine mem_inf.mpr ⟨?_, ?_⟩
        · have h2 := N.mul_mem hn (hNn d (hDC hd) n⁻¹ (N.inv_mem hn))
          simpa [mul_assoc] using h2
        · exact D.mul_mem ((mem_normalizer_iff.mp (hCD (hNC hn)) d).mp hd) (D.inv_mem hd)
      have h1 : (⟨_, (mem_inf.mp hcomm).2⟩ : D) ∈ (N ⊓ D).subgroupOf D := by
        rw [mem_subgroupOf]
        exact hcomm
      rw [hbot, mem_bot] at h1
      have h2 : n * d * n⁻¹ * d⁻¹ = 1 := congrArg Subtype.val h1
      calc d * n = (n * d * n⁻¹ * d⁻¹)⁻¹ * (n * d) := by group
        _ = n * d := by rw [h2, inv_one, one_mul]
    have := card_le_of_le hle
    rw [hcent] at this
    omega
  · have hDN : D ≤ N := fun d hd => by
      have : (⟨d, hd⟩ : D) ∈ (N ⊓ D).subgroupOf D := by
        rw [htop]
        trivial
      exact (mem_inf.mp (mem_subgroupOf.mp this)).1
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hN2
    have h3 : 3 ∣ 2 ^ k := by
      have := card_dvd_of_le hDN
      rw [hD60, hk] at this
      exact (by norm_num : (3 : ℕ) ∣ 60).trans this
    exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3) (by norm_num)

end TwoB

section TwoA

variable {G : Type*} [Group G] [Finite G]

theorem card_eq_one_of_perfect_of_squarefree {X : Type*} [Group X] [Finite X]
    [Group.IsPerfect X] (h : Squarefree (Nat.card X)) : Nat.card X = 1 := by
  have : IsZGroup X := IsZGroup.of_squarefree h
  by_contra h1
  have : Nontrivial X :=
    Finite.one_lt_card_iff_nontrivial.mp (by have := Nat.card_pos (α := X); omega)
  exact Group.IsPerfect.not_isSolvable X inferInstance

omit [Finite G] in
theorem isPerfect_of_commutator_eq {C : Subgroup G} (hperf : ⁅C, C⁆ = C) : Group.IsPerfect C := by
  rw [Group.isPerfect_def]
  apply Subgroup.map_injective C.subtype_injective
  rw [map_subtype_commutator, hperf, ← MonoidHom.range_eq_map, range_subtype]

theorem le_of_perfect {C Q N : Subgroup G} (hC : Nat.card C = 1920) (hQC : Q ≤ C)
    (hCQ : C ≤ normalizer (Q : Set G)) (hQ : Nat.card Q = 32) (hQ2 : IsPGroup 2 Q)
    (hperf : ⁅C, C⁆ = C) (hNC : N ≤ C) (hNn : ∀ c ∈ C, ∀ n ∈ N, c * n * c⁻¹ ∈ N)
    (hN2 : IsPGroup 2 N) : N ≤ Q := by
  set K := N ⊔ Q with hKdef
  have hK2 : IsPGroup 2 K := hN2.to_sup_of_normal_right' hQ2 (hNC.trans hCQ)
  have hKC : K ≤ C := sup_le hNC hQC
  have hQK : Q ≤ K := le_sup_right
  have hKn : ∀ c ∈ C, ∀ k ∈ K, c * k * c⁻¹ ∈ K := by
    intro c hc k hk
    have hmap : K.map (MulAut.conj c).toMonoidHom ≤ K := by
      rw [hKdef, Subgroup.map_sup]
      refine sup_le_sup ?_ ?_
      · rintro _ ⟨n, hn, rfl⟩
        exact hNn c hc n hn
      · rintro _ ⟨q, hq, rfl⟩
        exact (mem_normalizer_iff.mp (hCQ hc) q).mp hq
    exact hmap ⟨k, hk, rfl⟩
  have hK'n : (K.subgroupOf C).Normal := ⟨fun x hx c => by
    rw [mem_subgroupOf] at hx ⊢
    simpa using hKn c c.2 x hx⟩
  have : Group.IsPerfect C := isPerfect_of_commutator_eq hperf
  have hcardK' : Nat.card (K.subgroupOf C) = Nat.card K :=
    Nat.card_congr (subgroupOfEquivOfLe hKC).toEquiv
  have hprod := card_eq_card_quotient_mul_card_subgroup (K.subgroupOf C)
  rw [hC, hcardK'] at hprod
  obtain ⟨a, ha⟩ := IsPGroup.iff_card.mp hK2
  rw [ha] at hprod
  have h32 : 32 ≤ 2 ^ a := by
    have := card_le_of_le hQK
    rwa [hQ, ha] at this
  have ha5 : 5 ≤ a := by
    by_contra h
    have : 2 ^ a ≤ 2 ^ 4 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have ha10 : a ≤ 10 := by
    by_contra h
    have : 2 ^ 11 ≤ 2 ^ a := Nat.pow_le_pow_right (by norm_num) (by omega)
    have hq := Nat.card_pos (α := C ⧸ K.subgroupOf C)
    nlinarith
  set q := Nat.card (C ⧸ K.subgroupOf C) with hqdef
  interval_cases a
  · have hKQ : Q = K := eq_of_le_of_card_ge hQK (by rw [ha, hQ]; norm_num)
    exact le_sup_left.trans hKQ.symm.le
  · have h30 : q = 30 := by omega
    have := card_eq_one_of_perfect_of_squarefree (X := C ⧸ K.subgroupOf C)
      (by rw [← hqdef, h30]; decide +kernel)
    omega
  · have h15 : q = 15 := by omega
    have := card_eq_one_of_perfect_of_squarefree (X := C ⧸ K.subgroupOf C)
      (by rw [← hqdef, h15]; decide +kernel)
    omega
  all_goals omega

theorem exists_orderOf_eq_four {C Q : Subgroup G} (hQC : Q ≤ C) (hQ2 : IsPGroup 2 Q)
    (hcent : Nat.card ↥(C ⊓ centralizer (Q : Set G)) = 2) (hQ : 2 < Nat.card Q) :
    ∃ q ∈ Q, orderOf q = 4 := by
  by_contra hno
  simp only [not_exists, not_and] at hno
  have hsq : ∀ q ∈ Q, q * q = 1 := by
    intro q hq
    obtain ⟨k, hk⟩ := hQ2 ⟨q, hq⟩
    have hk' : q ^ 2 ^ k = 1 := by
      have := congrArg Subtype.val hk
      simpa using this
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hk')
    by_cases hj2 : 2 ≤ j
    · exfalso
      have hdvd : 2 ^ (j - 2) ∣ orderOf q := hj ▸ Nat.pow_dvd_pow 2 (Nat.sub_le j 2)
      have h4 := orderOf_pow_of_dvd (pow_ne_zero (j - 2) two_ne_zero) hdvd
      rw [hj, Nat.pow_div (Nat.sub_le j 2) two_pos, show j - (j - 2) = 2 by omega] at h4
      exact hno _ (Q.pow_mem hq _) (by rw [h4]; norm_num)
    · have : orderOf q ∣ 2 := by
        rw [hj]
        simpa using pow_dvd_pow 2 (show j ≤ 1 by omega)
      rw [← pow_two]
      exact orderOf_dvd_iff_pow_eq_one.mp this
  have hle : Q ≤ C ⊓ centralizer (Q : Set G) := by
    intro q hq
    refine mem_inf.mpr ⟨hQC hq, mem_centralizer_iff.mpr fun p hp => ?_⟩
    have h1 := hsq _ (Q.mul_mem hp hq)
    have hp' : p⁻¹ = p := inv_eq_of_mul_eq_one_left (hsq p hp)
    have hq' : q⁻¹ = q := inv_eq_of_mul_eq_one_left (hsq q hq)
    calc p * q = (p * q)⁻¹ := (inv_eq_of_mul_eq_one_left h1).symm
      _ = q * p := by rw [mul_inv_rev, hp', hq']
  have := card_le_of_le hle
  omega

theorem eq_one_or_eq_of_mem_zpowers {t x : G} (ht : orderOf t = 2) (hx : x ∈ zpowers t) :
    x = 1 ∨ x = t := by
  classical
  rw [mem_zpowers_iff_mem_range_orderOf, ht] at hx
  obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hx
  have hk2 : k < 2 := Finset.mem_range.mp hk
  interval_cases k <;> simp

theorem le_zpowers_sup_commutator {C Q : Subgroup G} {t : G} (htQ : t ∈ Q) (hQC : Q ≤ C)
    (hCQ : C ≤ normalizer (Q : Set G)) (hQ : Nat.card Q = 32) (hQ2 : IsPGroup 2 Q)
    (hcent : Nat.card ↥(C ⊓ centralizer (Q : Set G)) = 2) (hfour : FourClassesAtLeast 20 C) :
    Q ≤ zpowers t ⊔ ⁅Q, C⁆ := by
  set M := zpowers t ⊔ ⁅Q, C⁆ with hMdef
  have hMQ : M ≤ Q := by
    refine sup_le (zpowers_le.mpr htQ) (commutator_le.mpr fun q hq c hc => ?_)
    have e : ⁅q, c⁆ = q * (c * q⁻¹ * c⁻¹) := by rw [commutatorElement_def]; group
    rw [e]
    exact Q.mul_mem hq ((mem_normalizer_iff.mp (hCQ hc) q⁻¹).mp (Q.inv_mem hq))
  obtain ⟨q, hqQ, hq4⟩ := exists_orderOf_eq_four hQC hQ2 hcent (by omega)
  have h20 := hfour ⟨q, hQC hqQ⟩ (by rw [orderOf_mk]; exact hq4)
  have hinj : Nat.card {y : C // IsConj (⟨q, hQC hqQ⟩ : C) y} ≤ Nat.card M := by
    refine Nat.card_le_card_of_injective (fun y => ⟨(y.1 : G) * q⁻¹, ?_⟩) ?_
    · obtain ⟨c, hc⟩ := isConj_iff.mp y.2
      have hy : (y.1 : G) = c * q * c⁻¹ := by rw [← hc]; rfl
      rw [hy]
      refine mem_sup_right ?_
      rw [commutator_comm]
      exact commutator_mem_commutator c.2 hqQ
    · intro y₁ y₂ h
      have h' : (y₁.1 : G) * q⁻¹ = (y₂.1 : G) * q⁻¹ := congrArg Subtype.val h
      exact Subtype.ext (Subtype.ext (mul_right_cancel h'))
  have hM : Nat.card M = 32 := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (hQ2.to_le hMQ)
    have hdvd : 2 ^ k ∣ 2 ^ 5 := by
      rw [← hk, show (2 : ℕ) ^ 5 = 32 by norm_num, ← hQ]
      exact card_dvd_of_le hMQ
    have hk5 : k ≤ 5 := (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp hdvd
    have h20' : 20 ≤ 2 ^ k := hk ▸ h20.trans hinj
    rw [hk]
    interval_cases k <;> simp_all
  exact (eq_of_le_of_card_ge hMQ (by rw [hQ, hM])).symm.le

omit [Finite G] in
theorem commutator_le_of_index_two {C Q N : Subgroup G} (hCQ : C ≤ normalizer (Q : Set G))
    (hNn : ∀ c ∈ C, ∀ n ∈ N, c * n * c⁻¹ ∈ N)
    (hidx : (N.subgroupOf Q).index = 2) : ⁅Q, C⁆ ≤ N := by
  refine commutator_le.mpr fun q hq c hc => ?_
  have hcq : c * q⁻¹ * c⁻¹ ∈ Q := (mem_normalizer_iff.mp (hCQ hc) q⁻¹).mp (Q.inv_mem hq)
  have hiff : (⟨c * q⁻¹ * c⁻¹, hcq⟩ : Q) ∈ N.subgroupOf Q ↔ (⟨q, hq⟩ : Q) ∈ N.subgroupOf Q := by
    simp only [mem_subgroupOf]
    constructor
    · intro h
      have h1 := N.inv_mem (hNn c⁻¹ (C.inv_mem hc) _ h)
      simpa [mul_assoc] using h1
    · intro h
      exact hNn c hc _ (N.inv_mem h)
  have hmul := (mul_mem_iff_of_index_two hidx (a := ⟨q, hq⟩) (b := ⟨_, hcq⟩)).mpr hiff.symm
  rw [mem_subgroupOf] at hmul
  have e : ⁅q, c⁆ = q * (c * q⁻¹ * c⁻¹) := by rw [commutatorElement_def]; group
  rw [e]
  exact hmul

theorem centConcl_of_twoA {C Q : Subgroup G} {t : G} (htC : t ∈ C)
    (hCt : C ≤ centralizer ({t} : Set G)) (ht : orderOf t = 2) (hC : Nat.card C = 1920)
    (hperf : ⁅C, C⁆ = C) (hQC : Q ≤ C) (hCQ : C ≤ normalizer (Q : Set G))
    (hQ : Nat.card Q = 32) (hQ2 : IsPGroup 2 Q)
    (hcent : Nat.card ↥(C ⊓ centralizer (Q : Set G)) = 2) (hfour : FourClassesAtLeast 20 C) :
    CentConcl C t := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have htZ : t ∈ C ⊓ centralizer (Q : Set G) :=
    mem_inf.mpr ⟨htC, mem_centralizer_iff.mpr fun q hq =>
      mem_centralizer_singleton_iff.mp (hCt (hQC hq))⟩
  have hZ : C ⊓ centralizer (Q : Set G) = zpowers t :=
    (eq_of_le_of_card_ge (zpowers_le.mpr htZ) (by rw [hcent, Nat.card_zpowers, ht])).symm
  have htQ : t ∈ Q := by
    have : Nontrivial Q := Finite.one_lt_card_iff_nontrivial.mp (by rw [hQ]; norm_num)
    have := hQ2.center_nontrivial
    obtain ⟨z, hz⟩ := exists_ne (1 : center Q)
    have hzZ : ((z : Q) : G) ∈ C ⊓ centralizer (Q : Set G) := by
      refine mem_inf.mpr ⟨hQC (z : Q).2, mem_centralizer_iff.mpr fun q hq => ?_⟩
      exact congrArg Subtype.val (mem_center_iff.mp z.2 ⟨q, hq⟩)
    rw [hZ] at hzZ
    rcases eq_one_or_eq_of_mem_zpowers ht hzZ with h1 | h1
    · exact absurd (Subtype.ext (Subtype.ext h1)) hz
    · exact h1 ▸ (z : Q).2
  have hQM := le_zpowers_sup_commutator htQ hQC hCQ hQ hQ2 hcent hfour
  intro N hNC hNn hN2 htN hN16
  have hNQ : N ≤ Q := le_of_perfect hC hQC hCQ hQ hQ2 hperf hNC hNn hN2
  have hNeq : N = Q := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hN2
    have hdvd : 2 ^ k ∣ 2 ^ 5 := by
      rw [← hk, show (2 : ℕ) ^ 5 = 32 by norm_num, ← hQ]
      exact card_dvd_of_le hNQ
    have hk5 : k ≤ 5 := (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp hdvd
    have hk4 : 4 ≤ k := by
      by_contra h
      have : 2 ^ k ≤ 2 ^ 3 := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    obtain rfl | rfl : k = 4 ∨ k = 5 := by omega
    · exfalso
      have hidx : (N.subgroupOf Q).index = 2 := by
        have h := card_mul_index (N.subgroupOf Q)
        rw [Nat.card_congr (subgroupOfEquivOfLe hNQ).toEquiv, hk, hQ] at h
        omega
      have hle : zpowers t ⊔ ⁅Q, C⁆ ≤ N :=
        sup_le (zpowers_le.mpr htN) (commutator_le_of_index_two hCQ hNn hidx)
      have := card_le_of_le (hQM.trans hle)
      rw [hQ, hk] at this
      omega
    · exact eq_of_le_of_card_ge hNQ (by rw [hQ, hk]; norm_num)
  rw [hNeq, hZ]
  exact ⟨by rw [hQ]; norm_num, hQM, zpowers_le.mpr htQ⟩

end TwoA

end S63

end CFSG.LargeExtraspecial
