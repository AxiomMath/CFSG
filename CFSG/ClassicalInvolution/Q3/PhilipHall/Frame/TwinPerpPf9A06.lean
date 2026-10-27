module

import CFSG.ClassicalInvolution.Q3.Q3T7P24EngB
import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpPf9Ctx8Frame
import CFSG.ClassicalInvolution.Q3.Q3T7P24EngF06x
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpPf9A04

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

@[expose] def A : Subgroup G :=
  (S : Subgroup G) ⊓ Subgroup.centralizer (W : Set G) ⊓ Subgroup.centralizer (R : Set G) ⊓
    Subgroup.normalizer (K' : Set G) ⊓ Subgroup.normalizer (C.D.F.ρ₃.K : Set G)

@[expose] def Dg : Subgroup G := C.A ⊓ Subgroup.centralizer (R' : Set G)

theorem mem_A {a : G} : a ∈ C.A ↔ a ∈ (S : Subgroup G) ∧ a ∈ Subgroup.centralizer (W : Set G) ∧
    a ∈ Subgroup.centralizer (R : Set G) ∧ a ∈ Subgroup.normalizer (K' : Set G) ∧
    a ∈ Subgroup.normalizer (C.D.F.ρ₃.K : Set G) := by
  simp only [A, Subgroup.mem_inf, and_assoc]

theorem A_le_S : C.A ≤ (S : Subgroup G) := fun _ h => ((C.mem_A).mp h).1

theorem Dg_le_A : C.Dg ≤ C.A := inf_le_left
theorem card_R' : Nat.card ↥R' = 2 * Nat.card ↥(Subgroup.zpowers C.D.x₂) := by
  exact CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.S24B.Ctx8Frame.card_R' C.toFrame

theorem t_not_mem_zpowers : C.D.F.ρ'.r ∉ Subgroup.zpowers C.D.x₂ := fun h =>
  C.D.F.ρ'.hrW ((Subgroup.zpowers_le.mpr C.D.x₂_mem) h)

theorem A_le_centralizer_x₂ : C.A ≤ Subgroup.centralizer ({C.D.x₂} : Set G) := by
  exact CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.S24B.Ctx8Frame.A_le_centralizer_x₂ C.toFrame

include C in

theorem W_le_normalizer (L : Subgroup G) (hL : L ∈ Ω) {x : G} (hx : x ∈ L ⊓ W)
    (o : orderOf x = 4) : W ≤ Subgroup.normalizer (L : Set G) := by
  exact CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.S24B.Ctx8Frame.W_le_normalizer C.toFrame L hL hx o

theorem s_conj_z : C.D.F.ρ₃.r * z * C.D.F.ρ₃.r⁻¹ = z * C.D.F.j := by
  exact CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.S24B.Ctx8Frame.s_conj_z C.toFrame

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

theorem fix_of_trivMu {t : G} (htN : t ∈ Subgroup.normalizer (W : Set G)) (hT : TrivMu Ω W t)
    (ρ : Thompson.Rep Ω W) : conjSub t ρ.K = ρ.K := by
  exact CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.S24B.fix_of_trivMu_of C.D.c htN hT ρ

include C in

theorem W_le_P : W ≤ (S : Subgroup G) ⊓ MGrp Ω W := by
  exact CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.S24B.Ctx8Frame.W_le_P C.toFrame

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

theorem z_mem_P : z ∈ (S : Subgroup G) ⊓ MGrp Ω W := C.W_le_P C.hd.hzW
include C in

theorem P_normal {g : G} (hg : g ∈ (S : Subgroup G)) {x : G}
    (hx : x ∈ (S : Subgroup G) ⊓ MGrp Ω W) : g * x * g⁻¹ ∈ (S : Subgroup G) ⊓ MGrp Ω W := by
  exact CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.S24B.Ctx8Frame.P_normal C.toFrame hg hx

theorem Dg_mem_P {d : G} (hd : d ∈ C.Dg) (hdP : d ∈ (S : Subgroup G) ⊓ MGrp Ω W) :
    d = 1 ∨ d = z := by
  exact CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.S24B.Ctx8Frame.Dg_mem_P C.toFrame hd hdP

end Ctx8F
end S24B
end Asc77

end

end CFSG.ClassicalInvolution.Q8P
