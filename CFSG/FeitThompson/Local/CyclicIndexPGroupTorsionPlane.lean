module

public import Mathlib.Data.Nat.Prime.Int
public import CFSG.FeitThompson.Local.CyclicIndexPrimePowerMapHom
public import CFSG.FeitThompson.Local.ClassTwoPrimeTorsionCharacteristic
public import CFSG.FeitThompson.Definitions.ElementaryAbelianPRank
public import CFSG.FeitThompson.Foundations.SubgroupOrderAndIndex
public import Mathlib.Algebra.EuclideanDomain.Int

open Pointwise

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Subgroup

variable {p n : ℕ} {M : Type*} [Group M] {a : M}

def piFinTwoMulEquiv (N : Type*) [Mul N] : (Fin 2 → N) ≃* N × N :=
  { piFinTwoEquiv fun _ => N with map_mul' := fun _ _ => rfl }

@[simp]
theorem piFinTwoMulEquiv_apply {N : Type*} [Mul N] (f : Fin 2 → N) :
    piFinTwoMulEquiv N f = (f 0, f 1) := (rfl)

def piMultiplicativeZModMulEquivProd (p : ℕ) :
    (Fin 2 → Multiplicative (ZMod p)) ≃* Multiplicative (ZMod p × ZMod p) :=
  (piFinTwoMulEquiv _).trans (MulEquiv.prodMultiplicative (ZMod p) (ZMod p)).symm

theorem pow_mem_zpowers_pow_of_not_isCyclic (hp : p.Prime) (ha : orderOf a = p ^ n)
    (hnc : ¬ IsCyclic M) {b : M} (hgen : Subgroup.closure ({a, b} : Set M) = ⊤)
    (hb : b ^ p ∈ zpowers a) : b ^ p ∈ zpowers (a ^ p) := by
  obtain ⟨k, hk⟩ := mem_zpowers_iff.mp hb
  by_cases hdvd : (p : ℤ) ∣ k
  · obtain ⟨m, rfl⟩ := hdvd
    exact mem_zpowers_iff.mpr ⟨m, by rw [← zpow_natCast a p, ← zpow_mul, hk]⟩
  refine absurd ?_ hnc
  have hpz : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  obtain ⟨s, t, hst⟩ : IsCoprime ((p : ℤ) ^ n) k := (hpz.coprime_iff_not_dvd.mpr hdvd).pow_left
  have hpow : a ^ ((p : ℤ) ^ n) = 1 := by
    rw [show ((p : ℤ) ^ n) = ((p ^ n : ℕ) : ℤ) by push_cast; ring, zpow_natCast, ← ha,
      pow_orderOf_eq_one]
  have hone : a ^ (s * (p : ℤ) ^ n) = 1 := by rw [mul_comm, zpow_mul, hpow, one_zpow]
  have hain : a ∈ zpowers b := by
    have haeq : a = (b ^ p) ^ t := by
      calc a = a ^ (1 : ℤ) := (zpow_one a).symm
        _ = a ^ (s * (p : ℤ) ^ n + t * k) := by rw [hst]
        _ = a ^ (s * (p : ℤ) ^ n) * a ^ (t * k) := by rw [zpow_add]
        _ = (a ^ k) ^ t := by rw [hone, one_mul, mul_comm, zpow_mul]
        _ = (b ^ p) ^ t := by rw [hk]
    rw [haeq]
    exact (zpowers b).zpow_mem (pow_mem (mem_zpowers b) p) t
  refine isCyclic_iff_exists_zpowers_eq_top.mpr ⟨b, top_le_iff.mp ?_⟩
  rw [← hgen, Subgroup.closure_le]
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl
  · exact hain
  · exact mem_zpowers _

theorem one_le_of_not_isCyclic (hp : p.Prime) (hnc : ¬ IsCyclic M) (ha : orderOf a = p ^ n)
    (hidx : (zpowers a).index = p) : 1 ≤ n := by
  have hcard := natCard_eq_prime_pow_succ ha hidx
  rcases Nat.eq_zero_or_pos n with rfl | h
  · exact absurd (@isCyclic_of_prime_card M _ p ⟨hp⟩ (by simpa using hcard)) hnc
  · exact h

theorem omega1_eq_ker_powPrimeHom (hp : p.Prime) (hp2 : p ≠ 2) (hn : 1 ≤ n)
    (ha : orderOf a = p ^ n) (hidx : (zpowers a).index = p) :
    omega1 p M = (powPrimeHom hp hp2 hn ha hidx).ker := by
  ext x
  rw [mem_omega1_iff (hp.odd_of_ne_two hp2) (commutator_le_center hp hp2 hn ha hidx),
    MonoidHom.mem_ker, powPrimeHom_apply]

theorem natCard_omega1_eq_prime_sq (hp : p.Prime) (hp2 : p ≠ 2) (hnc : ¬ IsCyclic M)
    (ha : orderOf a = p ^ n) (hidx : (zpowers a).index = p) :
    Nat.card (omega1 p M) = p ^ 2 := by
  have hn : 1 ≤ n := one_le_of_not_isCyclic hp hnc ha hidx
  have hcard : Nat.card M = p ^ (n + 1) := natCard_eq_prime_pow_succ ha hidx
  set φ := powPrimeHom hp hp2 hn ha hidx with hφ
  obtain ⟨b, hgen, -⟩ := exists_generator_pair hp ha hidx
  have hAnormal : (zpowers a).Normal :=
    normal_of_isCoatom_of_natCard_eq_prime_pow hp hcard (isCoatom_of_index_eq_prime hp hidx)
  have := hAnormal
  have hbp : b ^ p ∈ zpowers a := by rw [← hidx]; exact (zpowers a).pow_index_mem b
  have hbp' : b ^ p ∈ zpowers (a ^ p) := pow_mem_zpowers_pow_of_not_isCyclic hp ha hnc hgen hbp
  have hrange : φ.range = zpowers (a ^ p) := by
    rw [MonoidHom.range_eq_map, ← hgen, MonoidHom.map_closure, Set.image_pair]
    refine le_antisymm ((Subgroup.closure_le _).mpr ?_) ?_
    · intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl
      · simp [hφ, mem_zpowers (a ^ p)]
      · simpa [hφ] using hbp'
    · rw [zpowers_eq_closure]
      refine Subgroup.closure_mono ?_
      intro x hx
      simp only [Set.mem_singleton_iff] at hx
      simp [hx, hφ]
  have hpn : p ^ n = p * p ^ (n - 1) := by rw [← pow_succ']; congr 1; omega
  have hcr : Nat.card φ.range = p ^ (n - 1) := by
    rw [hrange, Nat.card_zpowers,
      orderOf_pow_of_dvd hp.pos.ne' (ha ▸ dvd_pow_self p (by omega)), ha, hpn]
    exact Nat.mul_div_cancel_left _ hp.pos
  have h1 : φ.ker.index * Nat.card φ.ker = Nat.card M := Subgroup.index_mul_card φ.ker
  rw [Subgroup.index_ker, hcr, hcard] at h1
  rw [omega1_eq_ker_powPrimeHom hp hp2 hn ha hidx, ← hφ]
  refine Nat.eq_of_mul_eq_mul_left (pow_pos hp.pos (n - 1)) ?_
  rw [h1, ← pow_add]
  congr 1
  omega

theorem nonempty_mulEquiv_omega1 (hp : p.Prime) (hp2 : p ≠ 2) (hnc : ¬ IsCyclic M)
    (ha : orderOf a = p ^ n) (hidx : (zpowers a).index = p) :
    Nonempty (omega1 p M ≃* Multiplicative (ZMod p × ZMod p)) := by
  have := Fact.mk hp
  have hn : 1 ≤ n := one_le_of_not_isCyclic hp hnc ha hidx
  have hcard : Nat.card (omega1 p M) = p ^ 2 := natCard_omega1_eq_prime_sq hp hp2 hnc ha hidx
  have : IsMulCommutative (omega1 p M) := IsPGroup.isMulCommutative_of_card_eq_prime_sq hcard
  let _ : CommGroup (omega1 p M) := IsMulCommutative.instCommGroup
  have hexp : ∀ x : omega1 p M, x ^ p = 1 := fun x =>
    Subtype.ext (by
      simpa using pow_eq_one_of_mem_omega1 (hp.odd_of_ne_two hp2)
        (commutator_le_center hp hp2 hn ha hidx) x.2)
  obtain ⟨e⟩ := nonempty_mulEquiv_pi_of_exponent hp hexp hcard
  exact ⟨e.trans (piMultiplicativeZModMulEquivProd p)⟩

section Main

variable (A : Subgroup M)

theorem exists_zpowers_eq_and_orderOf_eq_prime_pow (hp : p.Prime) (hM : IsPGroup p M)
    [IsCyclic A] : ∃ (b : M) (m : ℕ), zpowers b = A ∧ orderOf b = p ^ m := by
  have := Fact.mk hp
  obtain ⟨b, hgen⟩ := A.isCyclic_iff_exists_zpowers_eq_top.mp ‹IsCyclic A›
  obtain ⟨m, hm⟩ := hM.exists_orderOf_eq_pow b
  exact ⟨b, m, hgen, hm⟩

variable (hp : p.Prime) (hodd : Odd p) (hM : IsPGroup p M) (hnc : ¬ IsCyclic M) [IsCyclic A]
  (hidx : A.index = p)

include hp hodd hM hnc hidx

theorem coe_omega1_of_isCyclic_of_index_eq_prime :
    (omega1 p M : Set M) = {x : M | x ^ p = 1} := by
  have hp2 : p ≠ 2 := by rintro rfl; exact (Nat.not_odd_iff_even.mpr even_two) hodd
  obtain ⟨b, m, hgen, hm⟩ := exists_zpowers_eq_and_orderOf_eq_prime_pow A hp hM
  rw [← hgen] at hidx
  exact coe_omega1 hodd
    (commutator_le_center hp hp2 (one_le_of_not_isCyclic hp hnc hm hidx) hm hidx)

theorem natCard_omega1_of_isCyclic_of_index_eq_prime : Nat.card (omega1 p M) = p ^ 2 := by
  have hp2 : p ≠ 2 := by rintro rfl; exact (Nat.not_odd_iff_even.mpr even_two) hodd
  obtain ⟨b, m, hgen, hm⟩ := exists_zpowers_eq_and_orderOf_eq_prime_pow A hp hM
  rw [← hgen] at hidx
  exact natCard_omega1_eq_prime_sq hp hp2 hnc hm hidx

theorem nonempty_mulEquiv_omega1_of_isCyclic_of_index_eq_prime :
    Nonempty (omega1 p M ≃* Multiplicative (ZMod p × ZMod p)) := by
  have hp2 : p ≠ 2 := by rintro rfl; exact (Nat.not_odd_iff_even.mpr even_two) hodd
  obtain ⟨b, m, hgen, hm⟩ := exists_zpowers_eq_and_orderOf_eq_prime_pow A hp hM
  rw [← hgen] at hidx
  exact nonempty_mulEquiv_omega1 hp hp2 hnc hm hidx

theorem omega1_characteristic_and_coe_and_mulEquiv :
    (omega1 p M).Characteristic ∧ (omega1 p M : Set M) = {x : M | x ^ p = 1} ∧
      Nonempty (omega1 p M ≃* Multiplicative (ZMod p × ZMod p)) :=
  ⟨omega1_characteristic, coe_omega1_of_isCyclic_of_index_eq_prime A hp hodd hM hnc hidx,
    nonempty_mulEquiv_omega1_of_isCyclic_of_index_eq_prime A hp hodd hM hnc hidx⟩

end Main

theorem omega1_characteristic_and_coe_and_mulEquiv' (A : Subgroup M) (hp : p.Prime) (hodd : Odd p)
    (hM : IsPGroup p M) (hnc : ¬ IsCyclic M) [IsCyclic A]
    (hidx : Nat.card (Set.range fun g : M => g • (A : Set M)) = p) :
    (omega1 p M).Characteristic ∧ (omega1 p M : Set M) = {x : M | x ^ p = 1} ∧
      Nonempty (omega1 p M ≃* Multiplicative (ZMod p × ZMod p)) :=
  omega1_characteristic_and_coe_and_mulEquiv A hp hodd hM hnc
    ((natCard_range_leftCoset A).symm.trans hidx)

end

end CFSG.FeitThompson
