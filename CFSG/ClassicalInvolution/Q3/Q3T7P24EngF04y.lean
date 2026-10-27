module

public import CFSG.ClassicalInvolution.Q3.Q3T7P24EngF04x

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

theorem x₂_sq : C.D.x₂ ^ 2 = z := by
  have h := C.D.z₂
  rw [C.m_eq_one, C.hz] at h
  simpa using h

theorem conj_r_nf (a b : ℤ) :
    C.D.F.ρ.r * (C.D.x₁ ^ a * C.D.x₃ ^ b) * C.D.F.ρ.r⁻¹ = C.D.x₁ ^ (b - a) * C.D.x₃ ^ b := by
  have h := A3Mod.conj_nf_r C.D.comm12 C.D.comm13 C.D.r₁ C.D.r₂ C.D.r₃ a 0 b
  simpa using h

theorem conj_t_nf (a b : ℤ) :
    C.D.F.ρ'.r * (C.D.x₁ ^ a * C.D.x₃ ^ b) * C.D.F.ρ'.r⁻¹ =
      C.D.x₁ ^ (a + b) * C.D.x₃ ^ (3 * b) := by
  have h := A3Mod.conj_nf_t C.D.comm23 C.D.t₁ C.D.t₂ C.D.t₃ a 0 b
  simp only [zpow_zero, mul_one, sub_zero] at h
  rw [h, C.x₂_eq, (C.D.comm13.pow_right 2).mul_zpow, ← zpow_natCast C.D.x₃ 2, ← zpow_mul]
  have e := C.mul_nf a 0 b (↑(2 : ℕ) * b)
  simp only [zpow_zero, mul_one] at e
  calc C.D.x₁ ^ a * (C.D.x₁ ^ b * C.D.x₃ ^ ((↑(2 : ℕ) : ℤ) * b)) * C.D.x₃ ^ b
      = C.D.x₁ ^ a * C.D.x₁ ^ b * (C.D.x₃ ^ ((↑(2 : ℕ) : ℤ) * b) * C.D.x₃ ^ b) := by group
    _ = C.D.x₁ ^ (a + b) * C.D.x₃ ^ (3 * b) := by
      rw [← zpow_add, ← zpow_add]; congr 2; push_cast; ring

end
end Ctx8Frame
end S24B
end Asc77

end CFSG.ClassicalInvolution.Q3.Q3T8
