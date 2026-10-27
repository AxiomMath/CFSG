module

public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.Tactic.Group
public import Mathlib.Data.Finset.Attr

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup
open scoped commutatorElement

variable {G : Type} [Group G]

theorem y7b_comm_mem_of_sq_mem {V N : Subgroup G} (hNV : N ≤ V)
    (hnorm : ∀ v ∈ V, ∀ n ∈ N, v * n * v⁻¹ ∈ N) (hsq : ∀ v ∈ V, v ^ 2 ∈ N) :
    ∀ u ∈ V, ∀ v ∈ V, ⁅u, v⁆ ∈ N := by
  haveI hnorm' : (N.subgroupOf V).Normal :=
    (Subgroup.normal_subgroupOf_iff hNV).mpr fun h k hh hk => hnorm k hk h hh
  have hexp : ∀ g : (↥V ⧸ N.subgroupOf V), g ^ 2 = 1 := by
    intro g
    refine QuotientGroup.induction_on g fun y => ?_
    change (QuotientGroup.mk' (N.subgroupOf V) y) ^ 2 = 1
    rw [← map_pow]
    show ((y ^ 2 : ↥V) : ↥V ⧸ N.subgroupOf V) = 1
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    exact hsq (y : G) y.2
  have hcomm : IsMulCommutative (↥V ⧸ N.subgroupOf V) := by
    apply IsMulCommutative.of_comm
    intro g h
    have hgh : (g * h) ^ 2 = 1 := hexp (g * h)
    rw [pow_two] at hgh
    calc g * h = (g * h)⁻¹ := (inv_eq_of_mul_eq_one_right hgh).symm
      _ = h⁻¹ * g⁻¹ := mul_inv_rev g h
      _ = h * g := by
        have hg := hexp g
        have hh := hexp h
        rw [pow_two] at hg hh
        rw [inv_eq_of_mul_eq_one_right hg, inv_eq_of_mul_eq_one_right hh]
  have hcommle : _root_.commutator ↥V ≤ N.subgroupOf V :=
    (Subgroup.Normal.quotient_commutative_iff_commutator_le (G := ↥V)
      (N := N.subgroupOf V)).mp hcomm
  intro u hu v hv
  have hmem : ⁅(⟨u, hu⟩ : ↥V), (⟨v, hv⟩ : ↥V)⁆ ∈ _root_.commutator ↥V :=
    Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
  have hcoe : ((⁅(⟨u, hu⟩ : ↥V), (⟨v, hv⟩ : ↥V)⁆ : ↥V) : G) = ⁅u, v⁆ :=
    map_commutatorElement (f := V.subtype) _ _
  have hmem' := hcommle hmem
  rw [Subgroup.mem_subgroupOf] at hmem'
  simpa [hcoe] using hmem'

private theorem y7b_exp2_cube_aux {Q : Type*} [Group Q] [IsMulCommutative Q]
    (hexp : ∀ q : Q, q ^ 2 = 1)
    {A B2 B3 : Q} (hABC : A * B2 * B3 = 1) :
    A * B3 * (B2 * A)⁻¹ * A⁻¹ = 1 := by
  have hA : A⁻¹ = A := by
    have h := hexp A
    rw [pow_two] at h
    exact inv_eq_of_mul_eq_one_right h
  have hB2 : B2⁻¹ = B2 := by
    have h := hexp B2
    rw [pow_two] at h
    exact inv_eq_of_mul_eq_one_right h
  have hAA : A * A = 1 := by simpa [pow_two] using hexp A
  have hAB3 : B2 * B3 = A := by
    have h : A * (B2 * B3) = 1 := by rw [← mul_assoc]; exact hABC
    calc B2 * B3 = A⁻¹ * (A * (B2 * B3)) := (inv_mul_cancel_left A (B2 * B3)).symm
      _ = A⁻¹ * 1 := by rw [h]
      _ = A := by rw [mul_one, hA]
  rw [mul_inv_rev, hA, hB2]
  calc A * B3 * (A * B2) * A = A * A * A * (B2 * B3) := by ac_rfl
    _ = A * A * A * A := by rw [hAB3]
    _ = (A * A) * (A * A) := by ac_rfl
    _ = 1 := by rw [hAA, one_mul]

theorem y7b_exp2_cube {P Z : Subgroup G} (hZP : Z ≤ P)
    (hZn : ∀ y ∈ P, ∀ z ∈ Z, y * z * y⁻¹ ∈ Z) (hcomm : ∀ y ∈ P, ∀ y' ∈ P, ⁅y, y'⁆ ∈ Z)
    (hsq : ∀ y ∈ P, y ^ 2 ∈ Z) {k : G} (hk3 : k ^ 3 = 1) (hkP : ∀ y ∈ P, k * y * k⁻¹ ∈ P)
    (hkZ : ∀ z ∈ Z, k * z * k⁻¹ ∈ Z) {c : G} (hc : c ∈ P)
    (hsum : c * (k * c * k⁻¹) * (k ^ 2 * c * (k ^ 2)⁻¹) ∈ Z) :
    ∃ x ∈ P, ⁅x, k⁆ * c⁻¹ ∈ Z := by
  let c₂ : G := k * c * k⁻¹
  let c₃ : G := k ^ 2 * c * (k ^ 2)⁻¹
  have hc2eq : c₂ = k * c * k⁻¹ := rfl
  have hc3eq : c₃ = k ^ 2 * c * (k ^ 2)⁻¹ := rfl
  have hc2 : c₂ ∈ P := by
    rw [hc2eq]; exact hkP c hc
  have hc3 : c₃ ∈ P := by
    have h1 : c₃ = k * c₂ * k⁻¹ := by rw [hc3eq, hc2eq, pow_two]; group
    rw [h1]; exact hkP c₂ hc2
  have hc3conj : k * c₃ * k⁻¹ = c := by
    have h1 : k * c₃ * k⁻¹ = k ^ 3 * c * (k ^ 3)⁻¹ := by rw [hc3eq]; group
    rw [h1, hk3]; group
  have hsxeq : k * (c * c₃) * k⁻¹ = c₂ * c := by
    have h1 : k * (c * c₃) * k⁻¹ = (k * c * k⁻¹) * (k * c₃ * k⁻¹) := by group
    rw [h1, hc3conj, hc2eq]
  refine ⟨c * c₃, P.mul_mem hc hc3, ?_⟩
  let ZP : Subgroup ↥P := Z.subgroupOf P
  haveI hZPn : ZP.Normal :=
    (Subgroup.normal_subgroupOf_iff hZP).mpr fun h k hh hk => hZn k hk h hh
  have hexpQ : ∀ q : ↥P ⧸ ZP, q ^ 2 = 1 := by
    intro q
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective ZP q
    change (QuotientGroup.mk' ZP y) ^ 2 = 1
    rw [← map_pow]
    show ((y ^ 2 : ↥P) : ↥P ⧸ ZP) = 1
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    exact hsq (y : G) y.2
  have hQcomm : ∀ a b : ↥P ⧸ ZP, a * b = b * a := by
    intro g h
    have hgh : (g * h) ^ 2 = 1 := hexpQ (g * h)
    rw [pow_two] at hgh
    calc g * h = (g * h)⁻¹ := (inv_eq_of_mul_eq_one_right hgh).symm
      _ = h⁻¹ * g⁻¹ := mul_inv_rev g h
      _ = h * g := by
        have hg := hexpQ g
        have hh := hexpQ h
        rw [pow_two] at hg hh
        rw [inv_eq_of_mul_eq_one_right hg, inv_eq_of_mul_eq_one_right hh]
  haveI : IsMulCommutative (↥P ⧸ ZP) := IsMulCommutative.of_comm hQcomm
  let A : ↥P ⧸ ZP := QuotientGroup.mk' ZP (⟨c, hc⟩ : ↥P)
  let B2 : ↥P ⧸ ZP := QuotientGroup.mk' ZP (⟨c₂, hc2⟩ : ↥P)
  let B3 : ↥P ⧸ ZP := QuotientGroup.mk' ZP (⟨c₃, hc3⟩ : ↥P)
  have hABC : A * B2 * B3 = 1 := by
    change QuotientGroup.mk' ZP (⟨c, hc⟩ : ↥P) * QuotientGroup.mk' ZP (⟨c₂, hc2⟩ : ↥P)
      * QuotientGroup.mk' ZP (⟨c₃, hc3⟩ : ↥P) = 1
    rw [← map_mul, ← map_mul]
    exact (QuotientGroup.eq_one_iff (N := ZP) _).mpr (by
      rw [Subgroup.mem_subgroupOf]
      simpa [hc2eq, hc3eq] using hsum)
  have hxmem : c * c₃ ∈ P := P.mul_mem hc hc3
  have hsxmem : k * (c * c₃) * k⁻¹ ∈ P := hkP (c * c₃) hxmem
  have hcommx : ⁅c * c₃, k⁆ = (c * c₃) * (k * (c * c₃) * k⁻¹)⁻¹ := by
    rw [commutatorElement_def]; group
  have hcommxmem : ⁅c * c₃, k⁆ ∈ P := by
    rw [hcommx]; exact P.mul_mem hxmem (P.inv_mem hsxmem)
  have hyP : ⁅c * c₃, k⁆ * c⁻¹ ∈ P := P.mul_mem hcommxmem (P.inv_mem hc)
  suffices h1 : ((⟨⁅c * c₃, k⁆ * c⁻¹, hyP⟩ : ↥P) : ↥P ⧸ ZP) = 1 by
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h1
    exact h1
  have hX : QuotientGroup.mk' ZP (⟨c * c₃, hxmem⟩ : ↥P) = A * B3 := by
    change QuotientGroup.mk' ZP (⟨c * c₃, hxmem⟩ : ↥P)
      = QuotientGroup.mk' ZP (⟨c, hc⟩ : ↥P) * QuotientGroup.mk' ZP (⟨c₃, hc3⟩ : ↥P)
    rw [← map_mul]
    exact congrArg (QuotientGroup.mk' ZP) (Subtype.ext rfl)
  have hSX : QuotientGroup.mk' ZP (⟨k * (c * c₃) * k⁻¹, hsxmem⟩ : ↥P) = B2 * A := by
    change QuotientGroup.mk' ZP (⟨k * (c * c₃) * k⁻¹, hsxmem⟩ : ↥P)
      = QuotientGroup.mk' ZP (⟨c₂, hc2⟩ : ↥P) * QuotientGroup.mk' ZP (⟨c, hc⟩ : ↥P)
    rw [← map_mul]
    exact congrArg (QuotientGroup.mk' ZP) (Subtype.ext hsxeq)
  have hstep : ((⟨⁅c * c₃, k⁆ * c⁻¹, hyP⟩ : ↥P) : ↥P ⧸ ZP)
      = A * B3 * (B2 * A)⁻¹ * A⁻¹ := by
    have hsub : (⟨⁅c * c₃, k⁆ * c⁻¹, hyP⟩ : ↥P)
        = (⟨c * c₃, hxmem⟩ : ↥P) * (⟨k * (c * c₃) * k⁻¹, hsxmem⟩ : ↥P)⁻¹
          * (⟨c, hc⟩ : ↥P)⁻¹ := by
      apply Subtype.ext
      show ⁅c * c₃, k⁆ * c⁻¹ = (c * c₃) * (k * (c * c₃) * k⁻¹)⁻¹ * c⁻¹
      rw [hcommx]
    rw [hsub]
    change QuotientGroup.mk' ZP
        ((⟨c * c₃, hxmem⟩ : ↥P) * (⟨k * (c * c₃) * k⁻¹, hsxmem⟩ : ↥P)⁻¹
          * (⟨c, hc⟩ : ↥P)⁻¹) = A * B3 * (B2 * A)⁻¹ * A⁻¹
    rw [map_mul, map_mul, map_inv, map_inv, hX, hSX]
  rw [hstep]
  exact y7b_exp2_cube_aux hexpQ hABC

end CFSG.OddStandard.HigherRank.YamadaG23
