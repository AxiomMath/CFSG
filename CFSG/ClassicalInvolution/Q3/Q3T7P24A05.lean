module

public import CFSG.ClassicalInvolution.Q3.Q3T7P24A04
import CFSG.ClassicalInvolution.Q3.Q3T7P24EngF05x
import CFSG.ClassicalInvolution.Q3.Q3T7P24EngF05y

public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

namespace CFSG.ClassicalInvolution.Q3.Q3T8

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected
namespace S24B
open CFSG.ClassicalInvolution.Asc77.S24B
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
namespace Ctx8
open CFSG.ClassicalInvolution.Asc77.S24B.Ctx8
variable {K K' W : Subgroup G} {S : Sylow 2 G} {R R' : Subgroup G} {z u : G}
  (C : Asc77.S24B.Ctx8 Ω K K' W S R R' z u)
include C in

theorem ne_conj_z {J T : Subgroup G} (hJ : J ∈ Ω) (hT : IsSylow2In T J) {zJ : G}
    (hzJ : IsUniqueInvolution J zJ) {t : G} (htT : T ≤ Subgroup.centralizer ({t} : Set G))
    (ht : t ≠ zJ) (g : G) : g * z * g⁻¹ ≠ t := by
  exact CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.S24B.Ctx8Frame.ne_conj_z C.toFrame hJ hT hzJ htT ht
    g
end Ctx8
end S24B
end Asc77

end

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected
namespace S24B
open CFSG.ClassicalInvolution.Asc77.S24B
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

namespace Ctx8
open CFSG.ClassicalInvolution.Asc77.S24B.Ctx8
variable {K K' W : Subgroup G} {S : Sylow 2 G} {R R' : Subgroup G} {z u : G}
  (C : Asc77.S24B.Ctx8 Ω K K' W S R R' z u)
include C in

theorem le_normalizer_W : (S : Subgroup G) ≤ Subgroup.normalizer (W : Set G) := by
  exact CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.S24B.Ctx8Frame.le_normalizer_W C.toFrame
include C in

theorem hRsyl : IsSylow2In R K :=
  T7C.isSylow2In_of_mem_RSet_of_le C.hs.stand.hyp C.hs.stand.mem C.hd.hR.1
    C.hd.hR.2.1
end Ctx8
end S24B
end Asc77

end

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected
namespace S24B
open CFSG.ClassicalInvolution.Asc77.S24B
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
namespace Ctx8
open CFSG.ClassicalInvolution.Asc77.S24B.Ctx8
variable {K K' W : Subgroup G} {S : Sylow 2 G} {R R' : Subgroup G} {z u : G}
  (C : Asc77.S24B.Ctx8 Ω K K' W S R R' z u)
include C in

theorem conjSub_K'_of_K {y : G} (h : conjSub y K = K) : conjSub y K' = K' := by
  exact CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.S24B.Ctx8Frame.conjSub_K'_of_K C.toFrame h
end Ctx8
end S24B
end Asc77

end

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected
namespace S24B
open CFSG.ClassicalInvolution.Asc77.S24B
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
namespace Ctx8
open CFSG.ClassicalInvolution.Asc77.S24B.Ctx8
variable {K K' W : Subgroup G} {S : Sylow 2 G} {R R' : Subgroup G} {z u : G}
  (C : Asc77.S24B.Ctx8 Ω K K' W S R R' z u)
include C in

theorem kc [IsSimpleGroup G] {t : G} (htS : t ∈ (S : Subgroup G)) (htM : t ∈ MGrp Ω W)
    (ht2 : t * t = 1) (ht1 : t ≠ 1) : ∃ g : G, g * z * g⁻¹ = t := by
  exact CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.S24B.Ctx8Frame.kc C.toFrame
    (T7C2.exists_g0 C.hs C.hd)
    (fun h₁ h₁1 h₁z h₁2 h₂ h₂1 h₂z h₂2 =>
      (T7K.exists_conj_of_involution C.hs h₁ h₁1 h₁z h₁2 h₂ h₂1 h₂z h₂2).imp fun c hc => hc.2)
    htS htM ht2 ht1
end Ctx8
end S24B
end Asc77

end

end CFSG.ClassicalInvolution.Q3.Q3T8
