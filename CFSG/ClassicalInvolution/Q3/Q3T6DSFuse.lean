module

public import CFSG.ClassicalInvolution.Q3.Q3T6DSConf

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T6D

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Asc77.T3CII CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight
open scoped commutatorElement

section Std


variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K K' J : Subgroup G} {S : Sylow 2 G} {R R' W V : Subgroup G} {z t : G}

structure AConf3 (S : Sylow 2 G) (K K' J : Subgroup G) (z a : G) : Prop where
  hA : a ∈ centralizerModOdd (centralizerModOdd (S : Subgroup G) (K ⊔ K')) J
  ha1 : a ≠ 1
  ha2 : a * a = 1
  c4 : Concl20_4 S K K' J z

namespace Std20Three

variable (d : Std20Three K K' J S R R' W V z t) {a : G} (h : AConf3 S K K' J z a)
include d h

theorem s_exists_x1 :
    ∃ x ∈ J, a * x = x * a ∧ x * z * x⁻¹ = z * t ∧ x * t * x⁻¹ = t := by
  obtain ⟨u, r, v, t₀, T, hh⟩ := d.late_exists_hex
  exact CFSG.ClassicalInvolution.Asc77.T3CII.s_exists_x1_of ⟨t₀, hh.hd'.r_memK, hh.htz, hh.ht₀t⟩
    d.viol.hzJ h.hA h.ha2 (d.s_comm_z h.hA.1.1) (d.s_comm_t h.hA)

theorem s_exists_rho_a :
    ∃ ρ : G, a * ρ = ρ * a ∧ ρ * z * ρ⁻¹ = z * t ∧ ρ * t * ρ⁻¹ = z ∧
      ρ ∈ Subgroup.normalizer ((Subgroup.closure ({z, t, a} : Set G) : Subgroup G) : Set G) := by
  obtain ⟨r, hr, r', hr', -, hrt⟩ := d.late_tor d.late_JW d.late_hW
  exact CFSG.ClassicalInvolution.Asc77.T3CII.s_exists_rho_a_of (d.s_exists_x1 h)
    ⟨r, d.hR.1 hr, d.hRS hr, hrt⟩ d.viol.hzK d.viol.hzJ.sq h.hA.1

end Std20Three

end Std

end CFSG.ClassicalInvolution.Q3.Q3T6D
