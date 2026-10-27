module

public import CFSG.ClassicalInvolution.Q3.Q3T7P24Ctx8Frame

public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

namespace CFSG.ClassicalInvolution.Q3.Q3T8

namespace Asc77
namespace S24B
namespace Ctx8Frame

section
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected
open CFSG.ClassicalInvolution.Disconnected.AschTight (HypOmegaGen)
open CFSG.ClassicalInvolution.Asc77.S24B
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem rep_mul_self {W : Subgroup G} (c : Q3CL.Thompson.Ctx Ω W) (ρ : Thompson.Rep Ω W) {z₀ : G}
    (hz : IsUniqueInvolution ρ.K z₀) : ρ.r * ρ.r = z₀ := by
  obtain ⟨hRW, -, hcyc, -, hcard⟩ :=
    Q3CL.Thompson.inf_W_of_mem_D c.hΩ c.hW ρ.hR ρ.hK ρ.hRK
  have hzKW := Q3CL.Thompson.uniqueInvolution_mem_W c.hΩ c.hW ρ.hK ρ.hR ρ.hRK hz
  have hzR : z₀ ∈ ρ.R := by
    have h : z₀ ∈ ρ.R ⊓ W := by rw [hRW]; exact hzKW
    exact h.1
  exact AscL62.sq_eq_of_not_mem (c.hΩ.isQuatSub_of_mem_RSet ρ.hR.1)
    (AscL62.isUniqueInvolution_of_le hz ρ.hRK.1 hzR) inf_le_left hcyc hcard ρ.hr
    (fun h => ρ.hrW h.2)

end

section
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected
open CFSG.ClassicalInvolution.Disconnected.AschTight (HypOmegaGen)
open CFSG.ClassicalInvolution.Asc77.S24B
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
open CFSG.ClassicalInvolution.Asc77.S24B.Ctx8
variable {K K' W : Subgroup G} {S : Sylow 2 G} {R R' : Subgroup G} {z u : G}
  (C : Asc77.S24B.Ctx8Frame Ω K K' W S R R' z u)

theorem m_eq_one : C.D.m = 1 := by
  have h1 := Q3CL.Thompson.D_card C.D.c.hΩ C.D.c.hW C.D.F.ρ.hR
  have h2 : Nat.card ↥(C.D.F.ρ.R ⊓ W) = 4 * C.D.m := by
    rw [← C.D.h₁, Nat.card_zpowers, C.D.o₁]
  have h3 : Nat.card ↥C.D.F.ρ.R = 8 := by rw [C.hR]; exact C.h8
  omega

theorem orderOf_x₁ : orderOf C.D.x₁ = 4 := by rw [C.D.o₁, C.m_eq_one]

theorem orderOf_x₃ : orderOf C.D.x₃ = 4 := by rw [C.D.o₃, C.m_eq_one]

include C in
theorem hzK' : IsUniqueInvolution K' z := isUniqueInvolution_of_mem_twinSet C.hzK C.hK'tw

theorem r_mul_self : C.D.F.ρ.r * C.D.F.ρ.r = z :=
  (rep_mul_self C.D.c C.D.F.ρ C.D.F.hz).trans C.hz

theorem t_mul_self : C.D.F.ρ'.r * C.D.F.ρ'.r = z :=
  (rep_mul_self C.D.c C.D.F.ρ' C.D.F.hz').trans C.hz

theorem r_mem_R : C.D.F.ρ.r ∈ R := (congrArg (fun X => C.D.F.ρ.r ∈ X) C.hR).mp C.D.F.ρ.hr

theorem t_mem_R' : C.D.F.ρ'.r ∈ R' := (congrArg (fun X => C.D.F.ρ'.r ∈ X) C.hR').mp C.D.F.ρ'.hr

theorem r_mem_K : C.D.F.ρ.r ∈ K := C.hd.hR.2.1 C.r_mem_R

theorem t_mem_K' : C.D.F.ρ'.r ∈ K' := C.hd.hR'.2.1 C.t_mem_R'

end
end Ctx8Frame
end S24B
end Asc77

end CFSG.ClassicalInvolution.Q3.Q3T8
