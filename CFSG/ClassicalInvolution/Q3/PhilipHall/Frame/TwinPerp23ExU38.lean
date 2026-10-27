module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Transport217
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDimTool
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscExitUAE5Cent
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpWz
public import CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge.GoodLift

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Q3.Q3NL CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge CFSG.ClassicalInvolution.Disconnected
open scoped commutatorElement

open CFSG.ClassicalInvolution.Balance

section U38

variable {n : ℕ}

theorem isSubnormal_of_cent_class {Y : Type} [Group Y] [Finite Y] {M : Subgroup Y} {u s : Y}
    (hM : Q3NL.IsSectionMember3 (Subgroup.centralizer ({u} : Set Y)) M s)
    (hc : ∀ c ∈ Subgroup.centralizer ({s} : Set Y), ∀ m ∈ M, m * (c * u * c⁻¹) = (c * u * c⁻¹) * m) :
    IsSubnormal M (Subgroup.centralizer ({s} : Set Y)) := by
  set C : Subgroup Y := Subgroup.centralizer ({s} : Set Y) with hC
  set X : Subgroup Y := Subgroup.closure {x : Y | ∃ c ∈ C, x = c * u * c⁻¹} with hX
  have hCX : C ≤ Subgroup.normalizer (X : Set Y) := by
    intro d hd
    have key : ∀ d ∈ C, ∀ x ∈ X, d * x * d⁻¹ ∈ X := by
      intro d hd x hx
      induction hx using Subgroup.closure_induction with
      | mem x hx =>
        obtain ⟨c, hc', rfl⟩ := hx
        exact Subgroup.subset_closure ⟨d * c, C.mul_mem hd hc', by group⟩
      | one => simpa using X.one_mem
      | mul x y _ _ hx hy =>
        have : d * (x * y) * d⁻¹ = (d * x * d⁻¹) * (d * y * d⁻¹) := by group
        rw [this]; exact X.mul_mem hx hy
      | inv x _ hx =>
        have : d * x⁻¹ * d⁻¹ = (d * x * d⁻¹)⁻¹ := by group
        rw [this]; exact X.inv_mem hx
    rw [Subgroup.mem_normalizer_iff]
    intro y
    refine ⟨fun hy => key d hd y hy, fun hy => ?_⟩
    have := key d⁻¹ (C.inv_mem hd) _ hy
    simpa [mul_assoc] using this
  have hMX : M ≤ Subgroup.centralizer (X : Set Y) := by
    intro m hm
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨c, hc', rfl⟩ := hx
      exact (hc c hc' m hm).symm
    | one => simp
    | mul x y _ _ hx hy =>
      rw [mul_assoc, hy, ← mul_assoc, hx, mul_assoc]
    | inv x _ hx =>
      have := Commute.inv_left (show Commute x m from hx)
      exact this.eq
  have huX : u ∈ X := Subgroup.subset_closure ⟨1, C.one_mem, by group⟩
  have hMC : M ≤ C := by
    have := hM.subnormal
    exact (isSubnormal_le this).trans inf_le_left
  have hNle : C ⊓ Subgroup.centralizer (X : Set Y) ≤ C ⊓ Subgroup.centralizer ({u} : Set Y) :=
    inf_le_inf_left _ (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr huX))
  have h1 : IsSubnormal M (C ⊓ Subgroup.centralizer (X : Set Y)) := by
    have := CFSG.ClassicalInvolution.isSubnormal_inf hM.subnormal (C ⊓ Subgroup.centralizer (X : Set Y))
    have e1 : M ⊓ (C ⊓ Subgroup.centralizer (X : Set Y)) = M := inf_eq_left.mpr (le_inf hMC hMX)
    have e2 : (C ⊓ Subgroup.centralizer ({u} : Set Y)) ⊓ (C ⊓ Subgroup.centralizer (X : Set Y)) =
        C ⊓ Subgroup.centralizer (X : Set Y) := inf_eq_right.mpr hNle
    rwa [e1, e2] at this
  exact isSubnormal_of_centralizer_inf hCX h1

end U38

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23
