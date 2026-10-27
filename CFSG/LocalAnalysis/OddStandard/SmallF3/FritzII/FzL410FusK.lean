module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzL410FusKY

public section

namespace CFSG.OddStandard.SmallF3.FritzII

open Subgroup CFSG.OddStandard.SmallF3.HarrisU33

namespace Fz410Set

variable {G : Type} [Group G] [Finite G] {t : G} {L S T : Subgroup G}
  {x₁ x₂ lam rho tau s : G} {Z E W Q R P : Subgroup G}
  (D : Fz410Set t L S T x₁ x₂ lam rho tau s Z E W Q R P)

include D

theorem exists_k {e g : G} (he : e ∈ E) (hg : g * t * g⁻¹ = e * (t * s)) :
    ∃ k : G, k * t * k⁻¹ = e * (t * s) ∧ ∀ z : G, k * z * k⁻¹ ∈ Z ↔ z ∈ Z := by
  obtain ⟨k, hk, hkS⟩ := fz410x_fz410_fusk_sylow D he hg
  exact ⟨k, hk, fz410x_fz410_fusk_normalizes_Z D he hk hkS⟩

end Fz410Set

end CFSG.OddStandard.SmallF3.FritzII
