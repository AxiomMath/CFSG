module

public import CFSG.GH74.Uniqueness.Setup

public section

namespace CFSG.GH74.Uniqueness

open Subgroup

variable {X : Type} [Group X] [Finite X] {Z : Set X} {M : Subgroup X}

theorem ZDSetup.exists_conj_centralizer_of_involution (S : ZDSetup X Z M) {t z : X} (ht : t ∈ Z)
    (htM : t ∉ M) (hz : z ∈ Z) (hzM : z ∈ M) {u : X} (hu : u ∈ M ⊓ conjugate M t)
    (hu2 : orderOf u = 2) :
    ∃ d ∈ M ⊓ conjugate M t, d⁻¹ * u * d ∈ centralizer ({z} : Set X) := by
  have huM : u ∈ M := (Subgroup.mem_inf.mp hu).1
  have hu1 : u * u = 1 := by
    have := pow_orderOf_eq_one u
    rwa [hu2, pow_two] at this
  have hui : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu1
  set A : Set X := Z ∩ (M : Set X) with hA
  have hmem : ∀ y ∈ A, u⁻¹ * y * u ∈ A := by
    intro y hy
    refine ⟨S.invariant.2 y hy.1 u, ?_⟩
    exact M.mul_mem (M.mul_mem (M.inv_mem huM) hy.2) huM
  let f : A → A := fun y => ⟨u⁻¹ * y * u, hmem y y.2⟩
  have hff : ∀ y, f (f y) = y := by
    intro y
    apply Subtype.ext
    show u⁻¹ * (u⁻¹ * (y : X) * u) * u = y
    rw [hui]
    calc u * (u * (y : X) * u) * u = (u * u) * (y : X) * (u * u) := by group
      _ = y := by rw [hu1]; group
  let σ : Equiv.Perm A := ⟨f, f, hff, hff⟩
  have hσ2 : σ ^ 2 ^ 1 = 1 := by
    rw [pow_one, pow_two]
    ext y
    exact congrArg Subtype.val (hff y)
  have hodd : Odd (Nat.card A) := S.odd_zNum
  have : Fintype A := Fintype.ofFinite A
  have hodd' : ¬ 2 ∣ Fintype.card A := by
    rw [← Nat.card_eq_fintype_card]
    exact hodd.not_two_dvd_nat
  obtain ⟨y, hy⟩ := Equiv.Perm.exists_fixed_point_of_prime hodd' hσ2
  have hyu : u⁻¹ * (y : X) * u = y := congrArg Subtype.val hy
  have hyc : (y : X) * u = u * y := by
    calc (y : X) * u = u * (u⁻¹ * y * u) := by group
      _ = u * y := by rw [hyu]
  obtain ⟨x, hxI, hxy⟩ := ((S.prodDisc.prop36c S.invariant ht htM).1 z ⟨hz, hzM⟩).surjOn y.2
  have hxD : x ∈ M ⊓ conjugate M t :=
    pPrimeCoreIn_le (M ⊓ conjugate M t) (CFSG.OddInversion.mem_invertedSet.mp hxI).1
  refine ⟨x⁻¹, Subgroup.inv_mem _ hxD, ?_⟩
  rw [Subgroup.mem_centralizer_singleton_iff, inv_inv]
  have hxy' : x⁻¹ * z * x = y := hxy
  have hz' : z = x * (y : X) * x⁻¹ := by rw [← hxy']; group
  rw [hz']
  calc x * u * x⁻¹ * (x * (y : X) * x⁻¹) = x * (u * y) * x⁻¹ := by group
    _ = x * (y * u) * x⁻¹ := by rw [hyc]
    _ = x * (y : X) * x⁻¹ * (x * u * x⁻¹) := by group

end CFSG.GH74.Uniqueness
