module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpPf5M4

public section

set_option linter.unusedSectionVars false
set_option autoImplicit false
namespace CFSG.ClassicalInvolution.Q8P

section
set_option linter.unusedSectionVars false
namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected
namespace T7Q
open CFSG.ClassicalInvolution.Asc77.T7Q
variable {G : Type} [Group G] [Finite G] [CoreLike G] {Ω : Set (Subgroup G)} {K K' W :
    Subgroup G} {S : Sylow 2 G} {R R' : Subgroup G}
  {z t u₁ u₂ : G}
open CFSG.ClassicalInvolution.Asc77.T7F2 CFSG.ClassicalInvolution.Asc77.T7G2

theorem twoSubgroupsFourGenerated_of_index_four (hyp : Hyp25 Ω K K' W S R R' z t u₁ u₂)
    (h11 : C25_11) (h16 : C25_16)
    (h4 : Nat.card ↥(S : Subgroup G) = 4 * Nat.card ↥(R ⊔ R')) : TwoSubgroupsFourGenerated G :=
  CFSG.ClassicalInvolution.T7F25.Asc77.T7Q.twoSubgroupsFourGenerated_of_index_four hyp.toF
    (h11 G Ω K K' W S R R' z t u₁ u₂ hyp) (h16 G Ω K K' W S R R' z t u₁ u₂ hyp) h4

theorem c25_21_of_11_16 (h11 : C25_11) (h16 : C25_16) : C25_21 := by
  intro G _ _ _ Ω K K' W S R R' z t u₁ u₂ hyp h4
  exact twoSubgroupsFourGenerated_of_index_four hyp h11 h16 h4
end T7Q
end Asc77
end
section
set_option linter.unusedSectionVars false
namespace Asc77
open CFSG.ClassicalInvolution.Asc77
namespace T7Q
open CFSG.ClassicalInvolution.Asc77.T7Q

theorem c25_E4_of_11_16 (h11 : C25_11) (h16 : C25_16) : C25_E4 :=
  c25_E4_of_exits (c25_19_of_sylow c25_2_t_proved (c25_17_idx_of_11_16 h11 h16))
    (c25_21_of_11_16 h11 h16)
end T7Q
end Asc77
end
end CFSG.ClassicalInvolution.Q8P
