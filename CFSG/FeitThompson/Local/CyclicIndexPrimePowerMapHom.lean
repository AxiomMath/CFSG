module

public import CFSG.FeitThompson.Foundations.HomPreservesGeneratedCommutators
public import CFSG.FeitThompson.Foundations.CentralExtensionNilpotent
public import CFSG.FeitThompson.Local.ClassTwoProductPowers
public import CFSG.FeitThompson.Local.FrattiniQuotientPPowerElementaryAbelian
public import CFSG.FeitThompson.Local.PrimePowerMapHomClassThree
public import CFSG.FeitThompson.Local.PrimeOrderUnitsModOddPrimePower
public import CFSG.FeitThompson.Local.MaximalSubgroupsPGroupPrimeIndex

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Subgroup
open scoped commutatorElement

variable {p n : ℕ} {M : Type*} [Group M] {a b : M} {u : ℤ}

theorem mem_center_of_closure_pair {x y z : M} (hxy : Subgroup.closure ({x, y} : Set M) = ⊤)
    (hx : Commute x z) (hy : Commute y z) : z ∈ Subgroup.center M := by
  rw [Subgroup.mem_center_iff]
  intro g
  have hle : Subgroup.closure ({x, y} : Set M) ≤ Subgroup.centralizer ({z} : Set M) := by
    rw [Subgroup.closure_le]
    intro w hw
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
    rcases hw with rfl | rfl
    · exact Subgroup.mem_centralizer_singleton_iff.mpr hx
    · exact Subgroup.mem_centralizer_singleton_iff.mpr hy
  rw [hxy] at hle
  exact Subgroup.mem_centralizer_singleton_iff.mp (hle (Subgroup.mem_top g))

theorem isMulCommutative_of_closure_pair {N : Type*} [Group N] {x y : N}
    (hxy : Subgroup.closure ({x, y} : Set N) = ⊤) (h : x * y = y * x) : IsMulCommutative N := by
  have hc : ∀ w ∈ ({x, y} : Set N), ∀ z ∈ ({x, y} : Set N), w * z = z * w := by
    intro w hw z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw hz
    rcases hw with rfl | rfl <;> rcases hz with rfl | rfl
    · rfl
    · exact h
    · exact h.symm
    · rfl
  have := Subgroup.isMulCommutative_closure fun w hw z hz _ => hc w hw z hz
  exact ⟨⟨fun v w => setLike_mul_comm (s := Subgroup.closure ({x, y} : Set N))
    (by rw [hxy]; trivial) (by rw [hxy]; trivial)⟩⟩

theorem zpow_eq_zpow_of_dvd_sub {k l : ℤ} (h : (orderOf a : ℤ) ∣ l - k) : a ^ k = a ^ l :=
  zpow_eq_zpow_iff_modEq.mpr (Int.modEq_iff_dvd.mpr h)

theorem commute_of_conj_eq {x y : M} (h : x⁻¹ * y * x = y) : Commute x y := by
  calc x * y = x * (x⁻¹ * y * x) := by rw [h]
    _ = y * x := by group

theorem pow_eq_one_of_mem_zpowers {d x : M} (hd : d ^ p = 1) (hx : x ∈ Subgroup.zpowers d) :
    x ^ p = 1 := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  rw [← zpow_natCast (d ^ k) p, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hd, one_zpow]

theorem commutator_eq_closure_setOf_inv_mul_inv_mul_mul :
    commutator M = Subgroup.closure {g : M | ∃ x y : M, x⁻¹ * y⁻¹ * x * y = g} := by
  rw [commutator_def, ← closure_setOf_inv_mul_inv_mul_mul (⊤ : Subgroup M) ⊤]
  congr 1
  ext g
  constructor
  · rintro ⟨x, -, y, -, h⟩
    exact ⟨x, y, h⟩
  · rintro ⟨x, y, h⟩
    exact ⟨x, Subgroup.mem_top x, y, Subgroup.mem_top y, h⟩

theorem conj_zpow_eq_zpow_mul (hu : b⁻¹ * a * b = a ^ u) (k : ℤ) :
    b⁻¹ * a ^ k * b = a ^ (u * k) := by
  have h := conj_zpow (α := M) (i := k) (a := b⁻¹) (b := a)
  simp only [inv_inv] at h
  rw [zpow_mul, ← hu]
  exact h.symm

theorem conj_pow_eq_zpow_pow (hu : b⁻¹ * a * b = a ^ u) (k : ℕ) :
    (b ^ k)⁻¹ * a * b ^ k = a ^ (u ^ k) := by
  induction k with
  | zero => simp
  | succ k ih =>
    calc (b ^ (k + 1))⁻¹ * a * b ^ (k + 1)
        = b⁻¹ * ((b ^ k)⁻¹ * a * b ^ k) * b := by rw [pow_succ]; group
      _ = b⁻¹ * a ^ (u ^ k) * b := by rw [ih]
      _ = a ^ (u * u ^ k) := conj_zpow_eq_zpow_mul hu _
      _ = a ^ (u ^ (k + 1)) := by rw [← pow_succ']

theorem natCard_eq_prime_pow_succ (ha : orderOf a = p ^ n)
    (hidx : (Subgroup.zpowers a).index = p) : Nat.card M = p ^ (n + 1) := by
  have h := Subgroup.index_mul_card (Subgroup.zpowers a)
  rw [hidx, Nat.card_zpowers, ha] at h
  rw [← h, pow_succ, mul_comm]

theorem exists_generator_pair (hp : p.Prime) (ha : orderOf a = p ^ n)
    (hidx : (Subgroup.zpowers a).index = p) :
    ∃ b : M, Subgroup.closure ({a, b} : Set M) = ⊤ ∧
      ∃ u : ℤ, b⁻¹ * a * b = a ^ u ∧ u ^ p ≡ 1 [ZMOD (p : ℤ) ^ n] := by
  have hord : (orderOf a : ℤ) = (p : ℤ) ^ n := by rw [ha]; push_cast; ring
  have hcard : Nat.card M = p ^ (n + 1) := natCard_eq_prime_pow_succ ha hidx
  have hcoatom : IsCoatom (Subgroup.zpowers a) := isCoatom_of_index_eq_prime hp hidx
  have hAnormal : (Subgroup.zpowers a).Normal :=
    normal_of_isCoatom_of_natCard_eq_prime_pow hp hcard hcoatom
  have := hAnormal
  obtain ⟨b, hb⟩ : ∃ b : M, b ∉ Subgroup.zpowers a := by
    by_contra h
    simp only [not_exists, not_not] at h
    exact hcoatom.1 ((Subgroup.eq_top_iff' _).mpr h)
  have hle : Subgroup.zpowers a ≤ Subgroup.closure ({a, b} : Set M) := by
    rw [Subgroup.zpowers_eq_closure]
    exact Subgroup.closure_mono (by intro x hx; simp only [Set.mem_singleton_iff] at hx; simp [hx])
  refine ⟨b, hcoatom.2 _ (lt_of_le_of_ne hle fun h => hb ?_), ?_⟩
  · rw [h]; exact Subgroup.subset_closure (by simp)
  have hbp : b ^ p ∈ Subgroup.zpowers a := by
    rw [← hidx]; exact (Subgroup.zpowers a).pow_index_mem b
  obtain ⟨u, hu⟩ : ∃ u : ℤ, b⁻¹ * a * b = a ^ u := by
    obtain ⟨u, hu⟩ := Subgroup.mem_zpowers_iff.mp
      (by simpa using hAnormal.conj_mem a (mem_zpowers a) b⁻¹)
    exact ⟨u, hu.symm⟩
  refine ⟨u, hu, ?_⟩
  have hcomm_bp : Commute (b ^ p) a := by
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hbp
    rw [← hk]
    exact (Commute.refl a).zpow_left k
  have hconj : (b ^ p)⁻¹ * a * b ^ p = a := by
    rw [mul_assoc, ← hcomm_bp.eq]; group
  have hupow : a ^ (u ^ p) = a ^ (1 : ℤ) := by
    rw [← conj_pow_eq_zpow_pow hu p, zpow_one, hconj]
  have := zpow_eq_zpow_iff_modEq.mp hupow
  rwa [hord] at this

theorem exists_central_of_zpowers_index_eq_prime (hp : p.Prime) (hp2 : p ≠ 2) (hn : 1 ≤ n)
    (ha : orderOf a = p ^ n) (hidx : (Subgroup.zpowers a).index = p) :
    a ^ p ^ (n - 1) ∈ Subgroup.center M ∧ ∃ d : M, d ^ p = 1 ∧
      Subgroup.zpowers d ≤ Subgroup.center M ∧ commutator M ≤ Subgroup.zpowers d := by
  have hord : (orderOf a : ℤ) = (p : ℤ) ^ n := by rw [ha]; push_cast; ring
  obtain ⟨b, hgen, u, hu, hmod⟩ := exists_generator_pair hp ha hidx
  set s := max 1 (n - 1) with hs
  have hdvd : ((p : ℤ) ^ s) ∣ u - 1 := by
    have h := modEq_one_pow_max_of_pow_modEq_one' hp hp2 hn hmod
    simpa using (Int.modEq_iff_dvd.mp h).neg_right
  have hns : n ≤ s + 1 := by omega
  have hns2 : n ≤ s * 2 := by omega
  have hns3 : n ≤ (n - 1) + s := by omega
  set d : M := a ^ (u - 1) with hd
  have hcentral_pow : a ^ p ^ (n - 1) ∈ Subgroup.center M := by
    refine mem_center_of_closure_pair hgen ((Commute.refl a).pow_right _) (commute_of_conj_eq ?_)
    rw [← zpow_natCast a (p ^ (n - 1)), conj_zpow_eq_zpow_mul hu]
    refine (zpow_eq_zpow_of_dvd_sub ?_).symm
    rw [hord]
    have heq : u * ((p ^ (n - 1) : ℕ) : ℤ) - ((p ^ (n - 1) : ℕ) : ℤ)
        = (p : ℤ) ^ (n - 1) * (u - 1) := by push_cast; ring
    rw [heq]
    calc (p : ℤ) ^ n ∣ (p : ℤ) ^ ((n - 1) + s) := pow_dvd_pow _ hns3
      _ ∣ (p : ℤ) ^ (n - 1) * (u - 1) := by rw [pow_add]; exact mul_dvd_mul_left _ hdvd
  have hdp : d ^ p = 1 := by
    rw [hd, ← zpow_natCast (a ^ (u - 1)) p, ← zpow_mul, ← orderOf_dvd_iff_zpow_eq_one, hord]
    calc (p : ℤ) ^ n ∣ (p : ℤ) ^ (s + 1) := pow_dvd_pow _ hns
      _ ∣ (u - 1) * (p : ℤ) := by rw [pow_succ]; exact mul_dvd_mul hdvd dvd_rfl
  have hdcentral : d ∈ Subgroup.center M := by
    refine mem_center_of_closure_pair hgen ((Commute.refl a).zpow_right _) (commute_of_conj_eq ?_)
    rw [hd, conj_zpow_eq_zpow_mul hu]
    refine (zpow_eq_zpow_of_dvd_sub ?_).symm
    rw [hord]
    have heq : u * (u - 1) - (u - 1) = (u - 1) ^ 2 := by ring
    rw [heq]
    calc (p : ℤ) ^ n ∣ ((p : ℤ) ^ s) ^ 2 := by rw [← pow_mul]; exact pow_dvd_pow _ hns2
      _ ∣ (u - 1) ^ 2 := pow_dvd_pow_of_dvd hdvd 2
  have hdle : Subgroup.zpowers d ≤ Subgroup.center M := Subgroup.zpowers_le.mpr hdcentral
  refine ⟨hcentral_pow, d, hdp, hdle, ?_⟩
  have hnormal : (Subgroup.zpowers d).Normal := normal_of_le_center hdle
  have := hnormal
  have hquot : IsMulCommutative (M ⧸ Subgroup.zpowers d) := by
    refine isMulCommutative_of_closure_pair
      (x := (QuotientGroup.mk' (Subgroup.zpowers d) a))
      (y := (QuotientGroup.mk' (Subgroup.zpowers d) b)) ?_ ?_
    · have h := MonoidHom.map_closure (QuotientGroup.mk' (Subgroup.zpowers d)) ({a, b} : Set M)
      rw [hgen, Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _),
        Set.image_pair] at h
      exact h.symm
    · have hau : a ^ u = a * d := by
        rw [hd, ← zpow_one_add]
        congr 1
        ring
      have hcomm : a⁻¹ * b⁻¹ * a * b = d := by
        rw [show a⁻¹ * b⁻¹ * a * b = a⁻¹ * (b⁻¹ * a * b) by group, hu, hau]
        group
      simp only [QuotientGroup.mk'_apply, ← QuotientGroup.mk_mul]
      refine (QuotientGroup.eq.mpr ?_).symm
      rw [show (b * a)⁻¹ * (a * b) = a⁻¹ * b⁻¹ * a * b by group, hcomm]
      exact mem_zpowers d
  exact (Subgroup.Normal.quotient_commutative_iff_commutator_le).mp hquot

section Main

variable (hp : p.Prime) (hp2 : p ≠ 2) (hn : 1 ≤ n) (ha : orderOf a = p ^ n)
  (hidx : (Subgroup.zpowers a).index = p)

include hp hp2 hn ha hidx

theorem commutator_le_center : commutator M ≤ Subgroup.center M := by
  obtain ⟨-, d, -, hdle, hle⟩ := exists_central_of_zpowers_index_eq_prime hp hp2 hn ha hidx
  exact hle.trans hdle

theorem pow_prime_eq_one_of_mem_commutator {x : M} (hx : x ∈ commutator M) : x ^ p = 1 := by
  obtain ⟨-, d, hdp, -, hle⟩ := exists_central_of_zpowers_index_eq_prime hp hp2 hn ha hidx
  exact pow_eq_one_of_mem_zpowers hdp (hle hx)

theorem pow_prime_pow_pred_mem_center : a ^ p ^ (n - 1) ∈ Subgroup.center M :=
  (exists_central_of_zpowers_index_eq_prime hp hp2 hn ha hidx).1

theorem mul_pow_prime (x y : M) : (x * y) ^ p = x ^ p * y ^ p := by
  have hc := commutator_le_center hp hp2 hn ha hidx
  rw [mul_pow_of_commutator_le_center hc x y p]
  have hexp : p * (p - 1) / 2 = p * ((p - 1) / 2) :=
    Nat.mul_div_assoc _ (Nat.Odd.sub_odd (hp.odd_of_ne_two hp2) odd_one).two_dvd
  rw [hexp, pow_mul,
    pow_prime_eq_one_of_mem_commutator hp hp2 hn ha hidx
      (inv_mul_inv_mul_mul_mem_commutator y x),
    one_pow, mul_one]

def powPrimeHom : M →* M := MonoidHom.mk' (· ^ p) (mul_pow_prime hp hp2 hn ha hidx)

@[simp]
theorem powPrimeHom_apply (x : M) : powPrimeHom hp hp2 hn ha hidx x = x ^ p := (rfl)

end Main

end

end CFSG.FeitThompson
