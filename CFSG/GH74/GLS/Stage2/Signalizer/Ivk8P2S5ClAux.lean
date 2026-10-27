module

public import CFSG.GH74.GLS.Stage2.Bender.Thm1.Basic
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.Defs
public import CFSG.GroupTheory.Fitting.CharacteristicP

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg
  CFSG.GH74.GLS.Stage2.Bender.Thm1
open scoped commutatorElement

section Aux

variable {G : Type} [Group G] [Finite G]

theorem exists_orderOf_pow_of_mem_Op_cl {q : ℕ} (hq : q.Prime) {M : Subgroup G} {x : G}
    (hx : x ∈ Op q M) : ∃ j, orderOf x = q ^ j := by
  obtain ⟨k, hk⟩ := (isPGroup_Op q hq M) ⟨x, hx⟩
  have hd : orderOf x ∣ q ^ k := orderOf_dvd_of_pow_eq_one (congrArg Subtype.val hk)
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hq).1 hd
  exact ⟨j, hj⟩

theorem odd_orderOf_of_mem_Op_cl {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) {M : Subgroup G} {x : G}
    (hx : x ∈ Op q M) : Odd (orderOf x) := by
  obtain ⟨j, hj⟩ := exists_orderOf_pow_of_mem_Op_cl hq hx
  rw [hj]
  exact (hq.eq_two_or_odd'.resolve_left hq2).pow

theorem eq_one_of_mem_Op_inf_cl {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    {M : Subgroup G} {x : G} (hxp : x ∈ Op p M) (hxq : x ∈ Op q M) : x = 1 := by
  obtain ⟨i, hi⟩ := exists_orderOf_pow_of_mem_Op_cl hp hxp
  obtain ⟨j, hj⟩ := exists_orderOf_pow_of_mem_Op_cl hq hxq
  have hcop : Nat.Coprime (p ^ i) (q ^ j) := ((Nat.coprime_primes hp hq).2 hpq).pow i j
  have h := Nat.dvd_gcd (dvd_of_eq hi) (dvd_of_eq hj)
  rw [hcop.gcd_eq_one] at h
  exact orderOf_eq_one_iff.1 (Nat.dvd_one.1 h)

theorem Op_commute_Op_cl {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) (M : Subgroup G)
    {x y : G} (hx : x ∈ Op q M) (hy : y ∈ Op p M) : x * y = y * x := by
  have hxM : x ∈ M := Op_le q M hx
  have hyM : y ∈ M := Op_le p M hy
  have h1 : x * y * x⁻¹ * y⁻¹ ∈ Op q M := by
    have hyn : y * x⁻¹ * y⁻¹ ∈ Op q M :=
      (mem_normalizer_iff.1 (le_normalizer_Op q M hyM) x⁻¹).1 ((Op q M).inv_mem hx)
    have := (Op q M).mul_mem hx hyn
    simpa [mul_assoc] using this
  have h2 : x * y * x⁻¹ * y⁻¹ ∈ Op p M := by
    have hxn : x * y * x⁻¹ ∈ Op p M :=
      (mem_normalizer_iff.1 (le_normalizer_Op p M hxM) y).1 hy
    exact (Op p M).mul_mem hxn ((Op p M).inv_mem hy)
  have h3 := eq_one_of_mem_Op_inf_cl hp hq hpq h2 h1
  have h4 : x * y = y * x := by
    calc x * y = (x * y * x⁻¹ * y⁻¹) * (y * x) := by group
      _ = y * x := by rw [h3, one_mul]
  exact h4

theorem z_mem_Op_two_of_cent {z : G} {H : Subgroup G} (hz : z ∈ H) (hz2 : orderOf z = 2)
    (hFs : Fs H ≤ centralizer ({z} : Set G)) : z ∈ Op 2 H := by
  have h2 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set zH : ↥H := ⟨z, hz⟩ with hzH
  have hzH2 : orderOf zH = 2 := by rw [Subgroup.orderOf_mk]; exact hz2
  have hcent : zH ∈ centralizer (generalizedFitting ↥H : Set ↥H) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hy' : (y : G) ∈ Fs H := ⟨y, hy, rfl⟩
    have := Subgroup.mem_centralizer_singleton_iff.mp (hFs hy')
    exact Subtype.ext this
  have hF : zH ∈ generalizedFitting ↥H := centralizer_generalizedFitting_le ↥H hcent
  have hFn : (generalizedFitting ↥H).Normal := CFSG.LocalCores.generalized_fitting_characteristic.2
  let N : Subgroup ↥H := generalizedFitting ↥H ⊓ centralizer (generalizedFitting ↥H : Set ↥H)
  have hNn : N.Normal := Subgroup.normal_inf_normal _ _
  have hNc : IsMulCommutative N :=
    ⟨⟨fun a b => Subtype.ext ((Subgroup.mem_centralizer_iff.mp b.2.2) (a : ↥H) a.2.1)⟩⟩
  have hzN : zH ∈ N := ⟨hF, hcent⟩
  let n₀ : ↥N := ⟨zH, hzN⟩
  have hn₀2 : orderOf n₀ = 2 := by rw [Subgroup.orderOf_mk]; exact hzH2
  have hP2 : IsPGroup 2 ↥(zpowers n₀) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hn₀2]; norm_num)
  obtain ⟨Pn, hPn⟩ := hP2.exists_le_sylow
  have hnil : Group.IsNilpotent ↥N := inferInstance
  have hmap := Sylow.map_le_pCore hNn hnil 2 Pn
  have hzP : zH ∈ Pn.map N.subtype := ⟨n₀, hPn (Subgroup.mem_zpowers n₀), rfl⟩
  exact ⟨zH, hmap hzP, rfl⟩

theorem Op_two_eq_bot_of_odd {D : Subgroup G} (hD : Odd (Nat.card ↥D)) : Op 2 D = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨j, hj⟩ := exists_orderOf_pow_of_mem_Op_cl Nat.prime_two hx
  have hxD : x ∈ D := Op_le 2 D hx
  have hdvd : orderOf (⟨x, hxD⟩ : ↥D) ∣ Nat.card ↥D := orderOf_dvd_natCard _
  rw [Subgroup.orderOf_mk, hj] at hdvd
  have hj0 : j = 0 := by
    by_contra hne
    have h2 : 2 ∣ Nat.card ↥D := (dvd_pow_self 2 hne).trans hdvd
    exact (Nat.not_even_iff_odd.2 hD) (even_iff_two_dvd.2 h2)
  rw [hj0, pow_zero] at hj
  exact Subgroup.mem_bot.2 (orderOf_eq_one_iff.1 hj)

theorem odd_card_pPrimeCoreOf_cl (M : Subgroup G) : Odd (Nat.card ↥(pPrimeCoreOf 2 M)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  unfold pPrimeCoreOf
  rw [Subgroup.card_map_of_injective M.subtype_injective]
  exact Nat.coprime_two_left.1 pPrimeCore_coprime_card

omit [Finite G] in
theorem le_normalizer_pPrimeCoreOf_cl (M : Subgroup G) :
    M ≤ normalizer (pPrimeCoreOf 2 M : Set G) := by
  have hnorm : (pPrimeCore 2 ↥M).Normal := pPrimeCore_normal
  have key : ∀ m ∈ M, ∀ x ∈ pPrimeCoreOf 2 M, m * x * m⁻¹ ∈ pPrimeCoreOf 2 M := by
    intro m hm x hx
    obtain ⟨y, hy, rfl⟩ := hx
    refine ⟨⟨m, hm⟩ * y * ⟨m, hm⟩⁻¹, hnorm.conj_mem y hy _, ?_⟩
    simp
  intro m hm
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨fun hx => key m hm x hx, fun hx => ?_⟩
  have h1 := key m⁻¹ (M.inv_mem hm) (m * x * m⁻¹) hx
  have e : m⁻¹ * (m * x * m⁻¹) * m⁻¹⁻¹ = x := by group
  rwa [e] at h1

omit [Finite G] in
theorem commute_of_oResidual_cl {K R : Subgroup G}
    (h : ⁅inSubgroup (oResidual 2) K, R⁆ = ⊥) {x : G} (hx : x ∈ K) (hodd : Odd (orderOf x)) :
    ∀ r ∈ R, x * r = r * x := by
  intro r hr
  have hxO : x ∈ inSubgroup (oResidual 2) K := by
    refine ⟨⟨x, hx⟩, Subgroup.subset_closure ?_, rfl⟩
    show Nat.Coprime (orderOf (⟨x, hx⟩ : ↥K)) 2
    rw [Subgroup.orderOf_mk]
    exact Nat.coprime_two_right.2 hodd
  have hle := Subgroup.commutator_eq_bot_iff_le_centralizer.mp h
  exact ((Subgroup.mem_centralizer_iff.mp (hle hxO)) r hr).symm

end Aux

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
