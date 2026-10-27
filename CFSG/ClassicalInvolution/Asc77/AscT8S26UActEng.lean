module

public import CFSG.ClassicalInvolution.Asc77.AscP1SevenDihedral
public import CFSG.ClassicalInvolution.Asc77.WP2Thm8
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.Thompson
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem c26_2_u_of_actE {K J T W : Subgroup G} {S : Sylow 2 G} {t u : G} (hJ : J ∈ omegaNbr Ω K)
    (hTJ : T ≤ J) (hTS : T ≤ (S : Subgroup G)) (hWS : W ≤ (S : Subgroup G))
    (ht : IsUniqueInvolution J t) (huW : u ∈ W) (htW : t ∈ W)
    (hact0 : ∃ ε : ℕ, ε ≤ 1 ∧
      ∀ x ∈ omegaNbrGen Ω K, ⁅u * t ^ ε, x⁆ ∈ oddCoreOf (omegaNbrGen Ω K)) :
    ∀ x ∈ T, x * u = u * x := by
  obtain ⟨ε, hε, hact⟩ := hact0
  have hJX : J ≤ omegaNbrGen Ω K :=
    le_iSup₂ (f := fun M' (_ : M' ∈ omegaNbr Ω K) => M') J hJ
  have htε : t ^ ε ∈ (S : Subgroup G) := (S : Subgroup G).pow_mem (hWS htW) ε
  intro x hx
  have hxX : x ∈ omegaNbrGen Ω K := hJX (hTJ hx)
  have hc := hact x hxX
  have hvS : u * t ^ ε ∈ (S : Subgroup G) := (S : Subgroup G).mul_mem (hWS huW) htε
  have hcS : ⁅u * t ^ ε, x⁆ ∈ (S : Subgroup G) := by
    rw [commutatorElement_def]
    exact (S : Subgroup G).mul_mem ((S : Subgroup G).mul_mem
      ((S : Subgroup G).mul_mem hvS (hTS hx)) ((S : Subgroup G).inv_mem hvS))
      ((S : Subgroup G).inv_mem (hTS hx))
  have hc2 : IsPGroup 2 (Subgroup.zpowers ⁅u * t ^ ε, x⁆) :=
    (S.isPGroup').to_le ((Subgroup.zpowers_le).mpr hcS)
  have hc1 : ⁅u * t ^ ε, x⁆ = 1 :=
    eq_one_of_isPGroup_of_mem_odd (oddCoreOf_odd_natCard _) hc hc2
  have hcomm : (u * t ^ ε) * x = x * (u * t ^ ε) := by
    rw [commutatorElement_def] at hc1
    calc (u * t ^ ε) * x = (u * t ^ ε * x * (u * t ^ ε)⁻¹ * x⁻¹) * (x * (u * t ^ ε)) := by
          group
      _ = x * (u * t ^ ε) := by rw [hc1, one_mul]
  have htx : t ^ ε * x = x * t ^ ε := by
    interval_cases ε
    · simp
    · rw [pow_one]
      exact ht.commute_of_mem (hTJ hx)
  have h2 : (u * x) * t ^ ε = (x * u) * t ^ ε := by
    calc (u * x) * t ^ ε = u * (x * t ^ ε) := by rw [mul_assoc]
      _ = u * (t ^ ε * x) := by rw [htx]
      _ = (u * t ^ ε) * x := by rw [mul_assoc]
      _ = x * (u * t ^ ε) := hcomm
      _ = (x * u) * t ^ ε := by rw [mul_assoc]
  exact (mul_right_cancel h2).symm

end CFSG.ClassicalInvolution.Asc77
