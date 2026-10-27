module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscPf9Lie
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpWz

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Q3.Q3NL CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge
open scoped commutatorElement


section Y3

variable {X : Type} [Group X] [Finite X] {Φ : Set (Subgroup X)}

theorem exists_third_member (hS : Q8Section X Φ) (hno : NoExit X Φ) {A A' : Subgroup X} (hA : A ∈ Φ)
    {z : X} (hzA : IsUniqueInvolution A z) (hzA' : IsUniqueInvolution A' z) :
    ∃ M ∈ Φ, M ≠ A ∧ M ≠ A' := by
  by_contra hcon
  push_neg at hcon
  have hall : ∀ M ∈ Φ, M = A ∨ M = A' := fun M hM => by
    by_cases h : M = A
    · exact Or.inl h
    · exact Or.inr (hcon M hM h)
  have hcz : ∀ L ∈ Φ, L ≤ Subgroup.centralizer ({z} : Set X) := by
    intro L hL x hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    have key : ∀ {J : Subgroup X}, IsUniqueInvolution J z → x ∈ J → x * z = z * x := by
      intro J hJ hxJ
      have := hJ.conj_eq (conjSub_eq_self_of_mem hxJ)
      calc x * z = (x * z * x⁻¹) * x := by group
        _ = z * x := by rw [this]
    rcases hall L hL with rfl | rfl
    · exact key hzA hx
    · exact key hzA' hx
  have hzC : (⊤ : Subgroup X) ≤ Subgroup.centralizer ({z} : Set X) := by
    rw [← hS.gen]
    exact iSup₂_le hcz
  have hcentral : ∀ g : X, g * z * g⁻¹ = z := by
    intro g
    have := Subgroup.mem_centralizer_singleton_iff.mp (hzC (Subgroup.mem_top g))
    calc g * z * g⁻¹ = (g * z) * g⁻¹ := rfl
      _ = (z * g) * g⁻¹ := by rw [this]
      _ = z := by group
  refine (hno A hA z hzA).2.1 ⟨Subgroup.zpowers z, ⟨fun a ha g => ?_⟩, ?_, Subgroup.mem_zpowers z⟩
  · obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    rw [← conj_zpow, hcentral g]
    exact Subgroup.zpow_mem_zpowers z k
  · exact CFSG.ClassicalInvolution.Asc77.ExactLayer.isPGroup_zpowers_of_sq_eq_one hzA.sq

end Y3

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23
