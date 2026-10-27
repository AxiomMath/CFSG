module

public import CFSG.ClassicalInvolution.Q3.Q3T7P24EngF04y

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
open CFSG.ClassicalInvolution.Asc77.S24B.Ctx8
variable {K K' W : Subgroup G} {S : Sylow 2 G} {R R' : Subgroup G} {z u : G}
  (C : Asc77.S24B.Ctx8Frame Ω K K' W S R R' z u)

theorem r_mul_mem_sup {w : G} (hw : w ∈ W) (h2 : C.D.F.ρ.r * w * (C.D.F.ρ.r * w) = 1) :
    C.D.F.ρ.r * w ∈ K ⊔ K' := by
  obtain ⟨a, b, rfl⟩ := C.exists_nf hw
  have hrr : C.D.F.ρ.r * C.D.F.ρ.r = C.D.x₁ ^ (2 : ℤ) * C.D.x₃ ^ (0 : ℤ) := by
    rw [zpow_zero, mul_one]
    exact C.r_mul_self.trans (by exact_mod_cast C.x₁_sq.symm)
  have e : C.D.F.ρ.r * (C.D.x₁ ^ a * C.D.x₃ ^ b) * (C.D.F.ρ.r * (C.D.x₁ ^ a * C.D.x₃ ^ b)) =
      C.D.F.ρ.r * (C.D.x₁ ^ a * C.D.x₃ ^ b) * C.D.F.ρ.r⁻¹ * (C.D.F.ρ.r * C.D.F.ρ.r) *
        (C.D.x₁ ^ a * C.D.x₃ ^ b) := by group
  rw [e, C.conj_r_nf, hrr, C.mul_nf, C.mul_nf] at h2
  have hb := C.four_dvd_of_x₃ (C.eq_one_of_nf _ _ h2).2
  have hev : Even b := by obtain ⟨k, hk⟩ := hb; exact ⟨k, by omega⟩
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left C.r_mem_K) (C.mem_sup_of_even hev)

theorem rt_mul_mem_sup {w : G} (hw : w ∈ W)
    (h2 : C.D.F.ρ.r * C.D.F.ρ'.r * w * (C.D.F.ρ.r * C.D.F.ρ'.r * w) = 1) :
    C.D.F.ρ.r * C.D.F.ρ'.r * w ∈ K ⊔ K' := by
  obtain ⟨a, b, rfl⟩ := C.exists_nf hw
  have hrt : C.D.F.ρ.r * C.D.F.ρ'.r * (C.D.F.ρ.r * C.D.F.ρ'.r) = 1 := by
    calc C.D.F.ρ.r * C.D.F.ρ'.r * (C.D.F.ρ.r * C.D.F.ρ'.r)
        = C.D.F.ρ.r * (C.D.F.ρ'.r * C.D.F.ρ.r) * C.D.F.ρ'.r := by group
      _ = C.D.F.ρ.r * (C.D.F.ρ.r * C.D.F.ρ'.r) * C.D.F.ρ'.r := by rw [C.commute_r_t.eq]
      _ = (C.D.F.ρ.r * C.D.F.ρ.r) * (C.D.F.ρ'.r * C.D.F.ρ'.r) := by group
      _ = 1 := by
        rw [C.r_mul_self, C.t_mul_self]
        exact (C.hzK.sq)
  have e : C.D.F.ρ.r * C.D.F.ρ'.r * (C.D.x₁ ^ a * C.D.x₃ ^ b) *
        (C.D.F.ρ.r * C.D.F.ρ'.r * (C.D.x₁ ^ a * C.D.x₃ ^ b)) =
      C.D.F.ρ.r * (C.D.F.ρ'.r * (C.D.x₁ ^ a * C.D.x₃ ^ b) * C.D.F.ρ'.r⁻¹) * C.D.F.ρ.r⁻¹ *
        (C.D.F.ρ.r * C.D.F.ρ'.r * (C.D.F.ρ.r * C.D.F.ρ'.r)) * (C.D.x₁ ^ a * C.D.x₃ ^ b) := by
    group
  rw [e, hrt, mul_one, C.conj_t_nf, C.conj_r_nf, C.mul_nf] at h2
  have hb := C.four_dvd_of_x₁ (C.eq_one_of_nf _ _ h2).1
  have hev : Even b := by obtain ⟨k, hk⟩ := hb; exact ⟨k, by omega⟩
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mem_sup_left C.r_mem_K)
    (Subgroup.mem_sup_right C.t_mem_K')) (C.mem_sup_of_even hev)

end
end Ctx8Frame
end S24B
end Asc77

end CFSG.ClassicalInvolution.Q3.Q3T8
