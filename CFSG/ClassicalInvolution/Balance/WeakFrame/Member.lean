module

public import CFSG.ClassicalInvolution.Generic.Frame
public import CFSG.ClassicalInvolution.Basic

public section

namespace CFSG.ClassicalInvolution.Balance

open CFSG.Open CFSG.ComponentClassification CFSG.ClassicalInvolution.Generic
open scoped MatrixGroups

section CentralInvolution

variable {G : Type*} [Group G]

structure IsCentralInvolution (K : Subgroup G) (z : G) : Prop where
  mem : z ∈ K
  ne_one : z ≠ 1
  sq : z * z = 1
  central : ∀ k ∈ K, z * k = k * z

namespace IsCentralInvolution

variable {K : Subgroup G} {z : G}

theorem conj (h : IsCentralInvolution K z) (n : G) :
    IsCentralInvolution (conjSub n K) (n * z * n⁻¹) where
  mem := conj_mem_conjSub h.mem
  ne_one := by
    intro h1
    apply h.ne_one
    have := congrArg (fun t => n⁻¹ * t * n) h1
    simpa [mul_assoc] using this
  sq := by
    calc n * z * n⁻¹ * (n * z * n⁻¹) = n * (z * z) * n⁻¹ := by group
      _ = 1 := by rw [h.sq]; group
  central := by
    intro k hk
    rw [mem_conjSub_iff] at hk
    have := h.central _ hk
    calc n * z * n⁻¹ * k = n * (z * (n⁻¹ * k * n)) * n⁻¹ := by group
      _ = n * ((n⁻¹ * k * n) * z) * n⁻¹ := by rw [this]
      _ = k * (n * z * n⁻¹) := by group

end IsCentralInvolution

theorem conjSub_centralizer_singleton (n z : G) :
    conjSub n (Subgroup.centralizer ({z} : Set G)) =
      Subgroup.centralizer ({n * z * n⁻¹} : Set G) := by
  ext x
  rw [mem_conjSub_iff, Subgroup.mem_centralizer_singleton_iff,
    Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    calc x * (n * z * n⁻¹) = n * ((n⁻¹ * x * n) * z) * n⁻¹ := by group
      _ = n * (z * (n⁻¹ * x * n)) * n⁻¹ := by rw [h]
      _ = n * z * n⁻¹ * x := by group
  · intro h
    calc n⁻¹ * x * n * z = n⁻¹ * (x * (n * z * n⁻¹)) * n := by group
      _ = n⁻¹ * ((n * z * n⁻¹) * x) * n := by rw [h]
      _ = z * (n⁻¹ * x * n) := by group

end CentralInvolution

section WeakMember

variable {F : Type*} [Field F] {G : Type*} [Group G]

structure WeakMember (F : Type*) [Field F] (K : Subgroup G) (z : G) : Prop where
  orderOf_eq_two : orderOf z = 2
  mem : z ∈ K
  perfect : Group.IsPerfect ↥K
  subnormal : IsSubnormal K (Subgroup.centralizer ({z} : Set G))
  nonempty_equiv : Nonempty (↥K ⧸ componentClassificationOddCore ↥K ≃* SL(2, F))

namespace WeakMember

variable {K : Subgroup G} {z : G}

theorem isCentralInvolution (h : WeakMember F K z) : IsCentralInvolution K z where
  mem := h.mem
  ne_one := by
    intro h1
    have := h.orderOf_eq_two
    rw [h1, orderOf_one] at this
    omega
  sq := by
    rw [← pow_two]
    exact orderOf_dvd_iff_pow_eq_one.mp (by rw [h.orderOf_eq_two])
  central := by
    intro k hk
    have := CFSG.ClassicalInvolution.isSubnormal_le h.subnormal hk
    exact (Subgroup.mem_centralizer_singleton_iff.mp this).symm

theorem conj (h : WeakMember F K z) (n : G) :
    WeakMember F (conjSub n K) (n * z * n⁻¹) where
  orderOf_eq_two := by
    have := orderOf_injective (MulAut.conj n).toMonoidHom (MulAut.conj n).injective z
    simpa [h.orderOf_eq_two] using this
  mem := conj_mem_conjSub h.mem
  perfect := by
    let e : ↥K ≃* ↥(conjSub n K) :=
      Subgroup.equivMapOfInjective K (MulAut.conj n).toMonoidHom (MulAut.conj n).injective
    have := h.perfect
    exact Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
  subnormal := by
    have h1 := CFSG.ClassicalInvolution.isSubnormal_map_mulEquiv (MulAut.conj n) h.subnormal
    have h2 : (Subgroup.centralizer ({z} : Set G)).map (MulAut.conj n).toMonoidHom =
        Subgroup.centralizer ({n * z * n⁻¹} : Set G) := conjSub_centralizer_singleton n z
    rw [h2] at h1
    exact h1
  nonempty_equiv := by
    obtain ⟨ψ⟩ := h.nonempty_equiv
    let e : ↥K ≃* ↥(conjSub n K) :=
      Subgroup.equivMapOfInjective K (MulAut.conj n).toMonoidHom (MulAut.conj n).injective
    have hO : (componentClassificationOddCore ↥K).map e.toMonoidHom =
        componentClassificationOddCore ↥(conjSub n K) := OddCore.equiv_invariant e
    exact ⟨(QuotientGroup.congr _ _ e hO).symm.trans ψ⟩

end WeakMember

end WeakMember


section Chart

variable {F : Type*} [Field F] {G : Type*} [Group G] {K : Subgroup G}

omit [Field F] in
theorem finite_of_odd_card {F : Type*} (h : Odd (Nat.card F)) : Finite F :=
  Nat.finite_of_card_ne_zero (by
    intro h0
    rw [h0] at h
    exact absurd h (by decide))

theorem eq_one_of_mem_oddCore_of_sq {X : Type*} [Group X] [Finite X] {x : X}
    (hx : x ∈ componentClassificationOddCore X) (hsq : x * x = 1) : x = 1 := by
  have hdvd := Subgroup.orderOf_dvd_natCard _ hx
  have h2 : orderOf x ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hsq)
  rcases (Nat.dvd_prime Nat.prime_two).mp h2 with h1 | h1
  · exact orderOf_eq_one_iff.mp h1
  · exfalso
    rw [h1] at hdvd
    exact (Nat.not_even_iff_odd.mpr (OddCore.odd_card X)) (even_iff_two_dvd.mpr hdvd)

structure IsChart (F : Type*) [Field F] (K : Subgroup G) (φ : ↥K →* SL(2, F)) : Prop where
  surjective : Function.Surjective φ
  ker_eq : φ.ker = componentClassificationOddCore ↥K

namespace IsChart

variable {φ : ↥K →* SL(2, F)} {z : G}

theorem map_central [Finite G] (hφ : IsChart F K φ) (hodd : Odd (Nat.card F))
    (hz : IsCentralInvolution K z) : φ ⟨z, hz.mem⟩ = -1 := by
  have hfin := finite_of_odd_card hodd
  have hz1 : (⟨z, hz.mem⟩ : ↥K) * ⟨z, hz.mem⟩ = 1 := Subtype.ext hz.sq
  have hsq : φ ⟨z, hz.mem⟩ * φ ⟨z, hz.mem⟩ = 1 := by rw [← map_mul, hz1, map_one]
  have hcen : φ ⟨z, hz.mem⟩ ∈ Subgroup.center SL(2, F) := by
    rw [Subgroup.mem_center_iff]
    intro y
    obtain ⟨k, rfl⟩ := hφ.surjective y
    rw [← map_mul, ← map_mul]
    exact congrArg φ (Subtype.ext (hz.central k k.2).symm)
  rcases (mem_center_sl2_iff _).mp hcen with h | h
  · exfalso
    have hmem : (⟨z, hz.mem⟩ : ↥K) ∈ componentClassificationOddCore ↥K := by
      rw [← hφ.ker_eq]
      exact h
    exact hz.ne_one (congrArg Subtype.val (eq_one_of_mem_oddCore_of_sq hmem hz1))
  · exact h

theorem eq_of_central [Finite G] (hφ : IsChart F K φ) (hodd : Odd (Nat.card F))
    {z' : G} (hz : IsCentralInvolution K z) (hz' : IsCentralInvolution K z') : z = z' := by
  have h1 := hφ.map_central hodd hz
  have h2 := hφ.map_central hodd hz'
  have hprod : φ (⟨z, hz.mem⟩ * ⟨z', hz'.mem⟩) = 1 := by
    rw [map_mul, h1, h2]
    have := mul_inv_cancel (-1 : SL(2, F))
    rwa [neg_one_inv] at this
  have hmem : (⟨z, hz.mem⟩ * ⟨z', hz'.mem⟩ : ↥K) ∈ componentClassificationOddCore ↥K := by
    rw [← hφ.ker_eq]
    exact hprod
  have hsq : (⟨z, hz.mem⟩ * ⟨z', hz'.mem⟩ : ↥K) * (⟨z, hz.mem⟩ * ⟨z', hz'.mem⟩) = 1 := by
    apply Subtype.ext
    show z * z' * (z * z') = 1
    calc z * z' * (z * z') = z * (z' * z) * z' := by group
      _ = z * (z * z') * z' := by rw [hz.central z' hz'.mem]
      _ = (z * z) * (z' * z') := by group
      _ = 1 := by rw [hz.sq, hz'.sq, one_mul]
  have h3 := eq_one_of_mem_oddCore_of_sq hmem hsq
  have h4 : z * z' = 1 := congrArg Subtype.val h3
  calc z = z * (z' * z') := by rw [hz'.sq, mul_one]
    _ = (z * z') * z' := (mul_assoc _ _ _).symm
    _ = z' := by rw [h4, one_mul]

theorem eq_one_or_eq_of_sq [Finite G] (hφ : IsChart F K φ) (hodd : Odd (Nat.card F))
    (hz : IsCentralInvolution K z) {x : G} (hx : x ∈ K) (hsq : x * x = 1) :
    x = 1 ∨ x = z := by
  have hfin := finite_of_odd_card hodd
  have h2 : (2 : F) ≠ 0 := CFSG.Semidihedral.OddFieldSL2.two_ne_zero_of_odd_card F hodd
  have hx1 : (⟨x, hx⟩ : ↥K) * ⟨x, hx⟩ = 1 := Subtype.ext hsq
  have hφsq : φ ⟨x, hx⟩ * φ ⟨x, hx⟩ = 1 := by rw [← map_mul, hx1, map_one]
  rcases sl2_sq_eq_one h2 hφsq with h | h
  · left
    have hmem : (⟨x, hx⟩ : ↥K) ∈ componentClassificationOddCore ↥K := by
      rw [← hφ.ker_eq]
      exact h
    exact congrArg Subtype.val (eq_one_of_mem_oddCore_of_sq hmem hx1)
  · right
    have hz1 := hφ.map_central hodd hz
    have hxz : x * z = z * x := (hz.central x hx).symm
    have hprod : φ (⟨x, hx⟩ * ⟨z, hz.mem⟩) = 1 := by
      rw [map_mul, h, hz1]
      have := mul_inv_cancel (-1 : SL(2, F))
      rwa [neg_one_inv] at this
    have hmem : (⟨x, hx⟩ * ⟨z, hz.mem⟩ : ↥K) ∈ componentClassificationOddCore ↥K := by
      rw [← hφ.ker_eq]
      exact hprod
    have hsq' : (⟨x, hx⟩ * ⟨z, hz.mem⟩ : ↥K) * (⟨x, hx⟩ * ⟨z, hz.mem⟩) = 1 := by
      apply Subtype.ext
      show x * z * (x * z) = 1
      calc x * z * (x * z) = x * (z * x) * z := by group
        _ = x * (x * z) * z := by rw [← hxz]
        _ = (x * x) * (z * z) := by group
        _ = 1 := by rw [hsq, hz.sq, one_mul]
    have h3 := eq_one_of_mem_oddCore_of_sq hmem hsq'
    have h4 : x * z = 1 := congrArg Subtype.val h3
    calc x = x * (z * z) := by rw [hz.sq, mul_one]
      _ = (x * z) * z := (mul_assoc _ _ _).symm
      _ = z := by rw [h4, one_mul]

end IsChart

end Chart

end CFSG.ClassicalInvolution.Balance
