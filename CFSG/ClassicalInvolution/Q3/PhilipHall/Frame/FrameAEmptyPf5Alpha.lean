module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf3SAlpha

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf

open CFSG.ClassicalInvolution.Q3.PhilipHall.InductionBridge (FrameSimple)

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Asc77.T3CII CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight CFSG.ClassicalInvolution.Q3.Q3T6D
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]
  {K K' J : Subgroup G} {S : Sylow 2 G} {R R' W V : Subgroup G} {z t : G} {a : G}

namespace AlphaCfgF

variable (d : Std20Frame K K' J S R R' W V z t) (h : AlphaCfgF S K K' J z t a)
include d h

theorem mem_normalizer_alpha_of_comm {c : G} (hc : c ∈ Subgroup.centralizer ({z} : Set G))
    (hcomm : a * c * a⁻¹ * c⁻¹ ∈ oddCoreOf (Subgroup.centralizer ({z} : Set G))) :
    c ∈ Subgroup.normalizer (alphaOf (Subgroup.closure ({t, z} : Set G)) : Set G) := by
  have haC : a ∈ Subgroup.centralizer ({z} : Set G) := h.B_le_Cz d
    (Subgroup.subset_closure (by simp))
  obtain ⟨o, hoO, hfix⟩ := T7A.exists_fixed_mul_of_odd
    (oddCoreOf_odd_natCard (Subgroup.centralizer ({z} : Set G))) h.ha2
    (mem_normalizer_oddCore_of_mem_normalizer (Subgroup.le_normalizer haC))
    (mem_normalizer_oddCore_of_mem_normalizer (Subgroup.le_normalizer hc)) hcomm
  have hoC : o ∈ Subgroup.centralizer ({z} : Set G) := oddCoreOf_le_self _ hoO
  have hcoC : c * o ∈ Subgroup.centralizer ({z} : Set G) := Subgroup.mul_mem _ hc hoC
  have hfix' : a * (c * o) = (c * o) * a := mul_inv_eq_iff_eq_mul.mp hfix
  have hz : z * (c * o) = (c * o) * z :=
    (Subgroup.mem_centralizer_singleton_iff.mp hcoC).symm
  have hmem : c * o ∈
      Subgroup.centralizer ((Subgroup.closure ({z, a} : Set G) : Subgroup G) : Set G) :=
    mem_centralizer_closure_pair hz hfix'
  have h1 := h.cent_le d (h.isElemAbelian2_za d) (h.za_le_B d) hmem
  have h2 := h.oddCore_Cz_le d hoO
  have h3 := Subgroup.mul_mem _ h1 (Subgroup.inv_mem _ h2)
  rwa [mul_inv_cancel_right] at h3

theorem sec20X_le_normalizer_alpha
    (hX : ∀ x ∈ sec20X (CoreAssembly.conjClass K) z K K',
      a * x * a⁻¹ * x⁻¹ ∈ oddCoreOf (Subgroup.centralizer ({z} : Set G))) :
    sec20X (CoreAssembly.conjClass K) z K K' ≤
      Subgroup.normalizer (alphaOf (Subgroup.closure ({t, z} : Set G)) : Set G) := by
  have hCz := d.sup_le_centralizer_z
  have hXz : sec20X (CoreAssembly.conjClass K) z K K' ≤ Subgroup.centralizer ({z} : Set G) :=
    sec20X_le_centralizer (le_sup_left.trans hCz) (le_sup_right.trans hCz)
  intro x hx
  exact h.mem_normalizer_alpha_of_comm d (hXz hx) (hX x hx)

end AlphaCfgF

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf
