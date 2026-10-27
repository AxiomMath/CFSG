module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87L29TwoNilp
import CFSG.GH74.GLS.Stage2.Signalizer.Odd87L29Burnside
import CFSG.GH74.GLS.Stage1.Thm6.Prod.Resid

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open Subgroup CFSG CFSG.GH74.GLS CFSG.GH74.GLS.Stage2.Local

namespace L29S1

theorem isPGroup_quotient_of_index_dvd_two {R : Type} [Group R] (K : Subgroup R) [K.Normal]
    (h : K.index ∣ 2) : IsPGroup 2 (R ⧸ K) := by
  rcases (Nat.dvd_prime Nat.prime_two).mp h with h1 | h2
  · exact IsPGroup.of_card (n := 0) (by rw [← Subgroup.index_eq_card, h1]; rfl)
  · exact IsPGroup.of_card (n := 1) (by rw [← Subgroup.index_eq_card, h2]; simp)

theorem O2Of_le_of_isPGroup_quotient {G : Type} [Group G] {X X' : Subgroup G}
    [(X.subgroupOf X').Normal] (hq : IsPGroup 2 (↥X' ⧸ X.subgroupOf X')) :
    O2Of X' ≤ O2Of X := by
  unfold O2Of
  rw [Subgroup.map_le_iff_le_comap]
  unfold oResidual
  rw [Subgroup.closure_le]
  intro y hy
  have hy1 : Odd (orderOf y) := Nat.coprime_two_right.mp hy
  have hyX : (y : G) ∈ X := L29Burnside.mem_of_odd_orderOf (X.subgroupOf X') hq hy1
  refine Subgroup.mem_map.mpr ⟨⟨y, hyX⟩, Subgroup.subset_closure ?_, rfl⟩
  show Nat.Coprime (orderOf (⟨y, hyX⟩ : ↥X)) 2
  rw [Subgroup.orderOf_mk]
  simpa [Subgroup.orderOf_coe] using hy

theorem twoNilp_of_comm {A : Type} [Group A] [Finite A] (hc : ∀ a b : A, a * b = b * a) :
    TwoNilp A := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨b, hb⟩ := L29Burnside.exists_index_oResidual_two (H := A)
  have hodd : ∀ x ∈ oResidual 2 A, Odd (orderOf x) := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem y hy => exact Nat.coprime_two_right.mp hy
    | one => simp
    | mul x y _ _ hx hy =>
      exact Odd.of_dvd_nat (Nat.odd_mul.mpr ⟨hx, hy⟩)
        ((Commute.orderOf_mul_dvd_lcm (hc x y)).trans (Nat.lcm_dvd_mul _ _))
    | inv x _ hx => simpa using hx
  refine ⟨oResidual 2 A, Stage1.Thm6.Prod.oResidual_normal 2 A, ?_, b, hb⟩
  by_contra hcon
  have h2 : 2 ∣ Nat.card ↥(oResidual 2 A) := by
    rw [Nat.not_odd_iff_even] at hcon
    exact even_iff_two_dvd.mp hcon
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥(oResidual 2 A)) 2 h2
  have := hodd x.1 x.2
  rw [Subgroup.orderOf_coe, hx] at this
  exact absurd this (by decide)

theorem mem_of_two_power_of_mem_oResidual {X A : Type} [Group X] [Finite X] [Group A] [Finite A]
    (hA : ∀ a b : A, a * b = b * a) (ψ : X →* A) (Δ Z : Subgroup X) [Δ.Normal]
    (hΔ : Δ ≤ ψ.ker) (hZc : Z ≤ center X) (hZ : IsPGroup 2 ↥Z)
    (hker : ∀ x : X, ψ x = 1 → ∃ d ∈ Δ, ∃ z ∈ Z, x = d * z)
    {x : X} (hx : x ∈ oResidual 2 X) {k : ℕ} (hxk : x ^ 2 ^ k = 1) : x ∈ Δ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let g : X ⧸ Δ →* A := QuotientGroup.lift Δ ψ hΔ
  have hgz : ∀ y ∈ g.ker, ∃ z ∈ Z, y = QuotientGroup.mk z := by
    intro y hy
    rw [QuotientGroup.ker_lift] at hy
    obtain ⟨x', hx', rfl⟩ := Subgroup.mem_map.mp hy
    obtain ⟨d, hd, z, hz, rfl⟩ := hker x' hx'
    refine ⟨z, hz, ?_⟩
    rw [map_mul, show (QuotientGroup.mk' Δ) d = 1 from (QuotientGroup.eq_one_iff d).mpr hd,
      one_mul]
    rfl
  have hkc : g.ker ≤ center (X ⧸ Δ) := by
    intro y hy
    obtain ⟨z, hz, rfl⟩ := hgz y hy
    rw [Subgroup.mem_center_iff]
    intro w
    obtain ⟨w', rfl⟩ := QuotientGroup.mk_surjective w
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    congr 1
    exact Subgroup.mem_center_iff.mp (hZc hz) w'
  have hk2 : IsPGroup 2 ↥g.ker := by
    intro y
    obtain ⟨z, hz, hy⟩ := hgz y.1 y.2
    obtain ⟨j, hj⟩ := hZ ⟨z, hz⟩
    refine ⟨j, Subtype.ext ?_⟩
    rw [Subgroup.coe_pow, hy, ← QuotientGroup.mk_pow]
    have : z ^ 2 ^ j = 1 := by simpa using congrArg Subtype.val hj
    rw [this, QuotientGroup.mk_one]
    rfl
  obtain ⟨N, hN, hNodd, a, ha⟩ := twoNilp_of_central_two_ker g hk2 hkc (twoNilp_of_comm hA)
  have hqN : IsPGroup 2 ((X ⧸ Δ) ⧸ N) :=
    IsPGroup.of_card (n := a) (by rw [← Subgroup.index_eq_card, ha])
  have hle : oResidual 2 X ≤ N.comap (QuotientGroup.mk' Δ) := by
    unfold oResidual
    rw [Subgroup.closure_le]
    intro y hy
    have hy1 : Odd (orderOf y) := Nat.coprime_two_right.mp hy
    exact L29Burnside.mem_of_odd_orderOf N hqN
      (Odd.of_dvd_nat hy1 (orderOf_map_dvd (QuotientGroup.mk' Δ) y))
  have hxN : (QuotientGroup.mk' Δ) x ∈ N := hle hx
  have h1 : orderOf ((QuotientGroup.mk' Δ) x) ∣ Nat.card N := Subgroup.orderOf_dvd_natCard N hxN
  have h2 : orderOf ((QuotientGroup.mk' Δ) x) ∣ 2 ^ k :=
    orderOf_dvd_of_pow_eq_one (by rw [← map_pow, hxk, map_one])
  have h3 : orderOf ((QuotientGroup.mk' Δ) x) = 1 := by
    have hc : Nat.Coprime (orderOf ((QuotientGroup.mk' Δ) x)) (2 ^ k) :=
      Nat.Coprime.pow_right k (Nat.coprime_two_right.mpr (Odd.of_dvd_nat hNodd h1))
    exact Nat.Coprime.eq_one_of_dvd hc h2
  exact (QuotientGroup.eq_one_iff x).mp (orderOf_eq_one_iff.mp h3)

end L29S1

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
