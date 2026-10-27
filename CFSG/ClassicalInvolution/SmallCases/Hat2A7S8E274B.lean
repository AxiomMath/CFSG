module

public import CFSG.ClassicalInvolution.SmallCases.Hat2A7S8C261
import CFSG.ClassicalInvolution.Q3.Q3CLFrame274

public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

namespace CFSG.ClassicalInvolution.Hat2A7S8

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.Thompson
    CFSG.GH74.Uniqueness CFSG.StronglyEmbedded.UniqueCoset CFSG.ClassicalInvolution.Asc77.AscP1Nine3
namespace T8
open CFSG.ClassicalInvolution.Asc77.T8
section Min
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem mem_H274_of_min {K J : Subgroup G} {S : Sylow 2 G} {R T W : Subgroup G} {z t : G}
    (hs : Std8 Ω K J S R T W z t) (hcomp : dComp Ω K = dstarComp Ω K)
    (hmin : ∀ S₂ : Sylow 2 G, R ≤ (S₂ : Subgroup G) →
      8 ≤ Nat.card {X : Subgroup G // X ∈ RSet Ω ∧ X ≤ (S₂ : Subgroup G)} →
        ∀ x : G, x ∈ (S₂ : Subgroup G) → x * x = 1 → x ≠ 1 →
          (∀ Y ∈ RSet Ω, Y ≤ (S₂ : Subgroup G) → ∀ y ∈ Y, x * y = y * x) →
            Subgroup.centralizer ({x} : Set G) ≤ H274 Ω K z)
    {g : G} (hgH : g⁻¹ * (z * t) * g ∈ H274 Ω K z) : g ∈ H274 Ω K z :=
  Q3.Q3CL.Frame.T8.mem_H274_of_min hs.toFrame hcomp hmin hgH
end Min
end T8
end Asc77

end

end CFSG.ClassicalInvolution.Hat2A7S8
