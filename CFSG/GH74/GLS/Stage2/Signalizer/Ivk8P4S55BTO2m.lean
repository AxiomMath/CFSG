module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55BTO2c

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT

open Subgroup CFSG CFSG.GH74.GLS.Stage2.Local
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem pCore_two_le_centralizer_of_transfer {H : Subgroup G} {Γ₀ : Type} [Group Γ₀]
    [Finite Γ₀] (π : ↥H →* Γ₀) (hπ : Function.Surjective π) {g : ↥H} {m : ℕ} (hm : Odd m)
    (hgm : g ^ m = 1)
    (hgC : ∀ c ∈ centralizer (layer (HBar H) : Set (HBar H)),
      QuotientGroup.mk' (pPrimeCore 2 ↥H) g * c = c * QuotientGroup.mk' (pPrimeCore 2 ↥H) g)
    (h3 : ∀ J₁ J₂ J₃ : Subgroup (HBar H), IsComponent J₁ → IsComponent J₂ → IsComponent J₃ →
      J₁ ≠ J₂ → J₁ ≠ J₃ → J₂ ≠ J₃ → False)
    (hOut : ∀ J : Subgroup (HBar H), IsComponent J →
      J ≤ π.ker.map (QuotientGroup.mk' (pPrimeCore 2 ↥H)) → OutTwoNilp (↥J ⧸ center ↥J)) :
    pCore 2 Γ₀ ≤ centralizer ({π g} : Set Γ₀) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set ν : ↥H →* HBar H := QuotientGroup.mk' (pPrimeCore 2 ↥H) with hν
  have hνs : Function.Surjective ν := QuotientGroup.mk'_surjective _
  set Q : Subgroup ↥H := (pCore 2 Γ₀).comap π with hQ
  set N : Subgroup (HBar H) := π.ker.map ν with hN
  set X : Subgroup (HBar H) := Q.map ν with hX
  have hNn : N.Normal := (MonoidHom.normal_ker π).map ν hνs
  have hXn : X.Normal := ((pCore_normal (p := 2) (G := Γ₀)).comap π).map ν hνs
  have hNX : N ≤ X := by
    refine Subgroup.map_mono fun h hh => ?_
    show π h ∈ pCore 2 Γ₀
    rw [MonoidHom.mem_ker.mp hh]
    exact Subgroup.one_mem _
  have hX2 : ∀ x ∈ X, ∃ n : ℕ, x ^ 2 ^ n ∈ N := by
    rintro _ ⟨y, hy, rfl⟩
    obtain ⟨n, hn⟩ := (pCore_isPGroup (p := 2) (G := Γ₀)) ⟨π y, hy⟩
    refine ⟨n, y ^ 2 ^ n, ?_, by rw [map_pow]⟩
    show π (y ^ 2 ^ n) = 1
    rw [map_pow]
    exact congrArg Subtype.val hn
  have hgm' : ν g ^ m = 1 := by rw [← map_pow, hgm, map_one]
  have hstep := step_out hNX hX2 h3 hOut hm hgm'
  have hcm := comm_mem_of_step hX2 hm hgm' hgC hstep
  intro y hy
  obtain ⟨x, rfl⟩ := hπ y
  have hxQ : x ∈ Q := hy
  set w : ↥H := x⁻¹ * (g * x * g⁻¹) with hw
  have hνw : ν w ∈ N := by
    have h1 := hcm (ν x) ⟨x, hxQ, rfl⟩
    simpa [hw, map_mul, map_inv] using h1
  obtain ⟨n, hn, hnw⟩ := hνw
  have hwn : n⁻¹ * w ∈ pPrimeCore 2 ↥H := by
    have : ν n = ν w := hnw
    rw [hν, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at this
    exact this
  have hπn : π n = 1 := MonoidHom.mem_ker.mp hn
  have hπw : π w = π (n⁻¹ * w) := by
    rw [show π (n⁻¹ * w) = π n⁻¹ * π w from map_mul _ _ _, map_inv, hπn, inv_one, one_mul]
  have hodd : Odd (orderOf (n⁻¹ * w)) :=
    Odd.of_dvd_nat (Nat.coprime_two_left.mp pPrimeCore_coprime_card)
      (Subgroup.orderOf_dvd_natCard _ hwn)
  have hwQ : w ∈ Q :=
    Q.mul_mem (Q.inv_mem hxQ) (((pCore_normal (p := 2) (G := Γ₀)).comap π).conj_mem x hxQ g)
  obtain ⟨k, hk⟩ := (pCore_isPGroup (p := 2) (G := Γ₀)) ⟨π w, hwQ⟩
  have hk' : π w ^ 2 ^ k = 1 := congrArg Subtype.val hk
  have ho : π w ^ orderOf (n⁻¹ * w) = 1 := by rw [hπw, ← map_pow, pow_orderOf_eq_one, map_one]
  have hcop : Nat.Coprime (orderOf (n⁻¹ * w)) (2 ^ k) :=
    Nat.Coprime.pow_right k hodd.coprime_two_right
  have hw1 : π w = 1 := (pow_eq_one_iff_of_coprime hcop).mp ⟨ho, hk'⟩
  have h2 : (π x)⁻¹ * (π g * π x * (π g)⁻¹) = 1 := by
    simpa [hw, map_mul, map_inv] using hw1
  have h3 : π g * π x = π x * π g :=
    calc π g * π x = π x * ((π x)⁻¹ * (π g * π x * (π g)⁻¹)) * π g := by group
      _ = π x * π g := by rw [h2, mul_one]
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact h3.symm

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT
