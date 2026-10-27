module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpPf9A04
import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpPf9Ctx8Frame
import CFSG.ClassicalInvolution.Q3.Q3T7P24EngF05x

public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

namespace CFSG.ClassicalInvolution.Q8P

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected
namespace S24B
open CFSG.ClassicalInvolution.Asc77.S24B
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
namespace Ctx8F
open CFSG.ClassicalInvolution.Asc77.S24B.Ctx8
variable {K K' W : Subgroup G} {S : Sylow 2 G} {R R' : Subgroup G} {z u : G}
  (C : Asc77.S24B.Ctx8F Ω K K' W S R R' z u)
include C in

theorem ne_conj_z {J T : Subgroup G} (hJ : J ∈ Ω) (hT : IsSylow2In T J) {zJ : G}
    (hzJ : IsUniqueInvolution J zJ) {t : G} (htT : T ≤ Subgroup.centralizer ({t} : Set G))
    (ht : t ≠ zJ) (g : G) : g * z * g⁻¹ ≠ t := by
  exact CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.S24B.Ctx8Frame.ne_conj_z C.toFrame hJ hT hzJ htT ht
    g
end Ctx8F
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

namespace Ctx8F
open CFSG.ClassicalInvolution.Asc77.S24B.Ctx8
variable {K K' W : Subgroup G} {S : Sylow 2 G} {R R' : Subgroup G} {z u : G}
  (C : Asc77.S24B.Ctx8F Ω K K' W S R R' z u)
include C in

theorem le_normalizer_W : (S : Subgroup G) ≤ Subgroup.normalizer (W : Set G) := by
  exact CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.S24B.Ctx8Frame.le_normalizer_W C.toFrame
include C in

theorem hRsyl : IsSylow2In R K :=
  T7C.isSylow2In_of_mem_RSet_of_le C.hs.stand.hyp C.hs.stand.mem C.hd.hR.1
    C.hd.hR.2.1
include C in

theorem z_mem_R : z ∈ R :=
  T7C.mem_of_isSylow2In C.hs.stand.hyp C.hs.stand.mem C.hRsyl C.hzK
include C in

theorem le_centralizer_z : (S : Subgroup G) ≤ Subgroup.centralizer ({z} : Set G) := by
  exact CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.S24B.Ctx8Frame.le_centralizer_z C.toFrame
end Ctx8F
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
namespace Ctx8F
open CFSG.ClassicalInvolution.Asc77.S24B.Ctx8
variable {K K' W : Subgroup G} {S : Sylow 2 G} {R R' : Subgroup G} {z u : G}
  (C : Asc77.S24B.Ctx8F Ω K K' W S R R' z u)
theorem φ_imgQ_mem (ρ : Thompson.Rep Ω W) : C.D.φ (T7D.imgQ ρ) ∈ S4.swaps4 :=
  S4.mem_swaps4_of_isSwap ((C.D.hφ _).mp (T7D.imgQ_mem ρ))

end Ctx8F
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
namespace Ctx8F
open CFSG.ClassicalInvolution.Asc77.S24B.Ctx8
variable {K K' W : Subgroup G} {S : Sylow 2 G} {R R' : Subgroup G} {z u : G}
  (C : Asc77.S24B.Ctx8F Ω K K' W S R R' z u)
include C in

theorem conjSub_K'_of_K {y : G} (h : conjSub y K = K) : conjSub y K' = K' := by
  exact CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.S24B.Ctx8Frame.conjSub_K'_of_K C.toFrame h
end Ctx8F
end S24B
end Asc77

end

end CFSG.ClassicalInvolution.Q8P
