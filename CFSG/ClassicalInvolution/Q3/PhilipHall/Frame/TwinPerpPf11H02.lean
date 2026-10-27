module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpPf11H01
import CFSG.ClassicalInvolution.Q3.Q3T7P24EngH2
import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpPf9Ctx8Frame
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpPf9A06

public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

namespace CFSG.ClassicalInvolution.Q8P

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.ExactLayer
    CFSG.ClassicalInvolution.Balance.Bootstrap
namespace S24B
open CFSG.ClassicalInvolution.Asc77.S24B
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
namespace Ctx8F
open CFSG.ClassicalInvolution.Asc77.S24B.Ctx8
variable {K K' W : Subgroup G} {S : Sylow 2 G} {R R' : Subgroup G} {z u : G}
  (C : Asc77.S24B.Ctx8F Ω K K' W S R R' z u)

theorem mem_closure_of_mem_W {w : G} (hw : w ∈ W) (h2 : w * w = 1) :
    w ∈ Subgroup.closure ({C.D.F.j, z} : Set G) := by
  exact C.toFrame.mem_closure_of_mem_W hw h2

theorem u_cases : u = C.D.F.j ∨ u = C.D.F.j * z := by
  exact C.toFrame.u_cases

theorem r_conj_jz : C.D.F.ρ.r * (C.D.F.j * z) * C.D.F.ρ.r⁻¹ = C.D.F.j := by
  exact C.toFrame.r_conj_jz

theorem r_mem_centralizer_z : C.D.F.ρ.r ∈ Subgroup.centralizer ({z} : Set G) :=
  C.toFrame.r_mem_centralizer_z
end Ctx8F
namespace HCtx
open CFSG.ClassicalInvolution.Asc77.S24B.HCtx
variable {K K' W : Subgroup G} {S : Sylow 2 G} {R R' : Subgroup G} {z u : G}
  (H : Asc77.S24B.HCtx Ω K K' W S R R' z u)

private def toHFrame : CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.S24B.HFrame Ω K K' W S R R' z u where
  C := H.C.toFrame
  a := H.a
  T₃ := H.T₃
  ha2 := H.ha2
  ha1 := H.ha1
  haR := H.haR
  haR' := H.haR'
  hT := H.hT
  hTN := H.hTN
  hTa := H.hTa

theorem T_card : Nat.card ↥H.T₃ = 2 * Nat.card ↥(Subgroup.zpowers H.C.D.x₃) := by
  exact (toHFrame H).T_card

theorem exists_s : ∃ s ∈ H.T₃, s ∉ Subgroup.zpowers H.C.D.x₃ := by
  exact (toHFrame H).exists_s

theorem s_conj_z_cases {s : G} (hs : s ∈ H.T₃) (hsU : s ∉ Subgroup.zpowers H.C.D.x₃) :
    s * z * s⁻¹ = H.C.D.F.j ∨ s * z * s⁻¹ = H.C.D.F.j * z := by
  exact (toHFrame H).s_conj_z_cases hs hsU

theorem s_mem_normalizer_B {s : G} (hs : s ∈ H.T₃) (hsU : s ∉ Subgroup.zpowers H.C.D.x₃) :
    s ∈ Subgroup.normalizer (H.B : Set G) := by
  exact (toHFrame H).s_mem_normalizer_B hs hsU

theorem closure_jz_le_B : Subgroup.closure ({H.C.D.F.j, z} : Set G) ≤ H.B := by
  exact (toHFrame H).closure_jz_le_B

theorem closure_jz : IsElemAbelian2 (Subgroup.closure ({H.C.D.F.j, z} : Set G)) 2 :=
  (toHFrame H).closure_jz

end HCtx
end S24B
end Asc77

end

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.ExactLayer
    CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.Bootstrap
open scoped commutatorElement
namespace S24B
open CFSG.ClassicalInvolution.Asc77.S24B
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
namespace HCtx
open CFSG.ClassicalInvolution.Asc77.S24B.HCtx
variable {K K' W : Subgroup G} {S : Sylow 2 G} {R R' : Subgroup G} {z u : G}
  (H : Asc77.S24B.HCtx Ω K K' W S R R' z u)

theorem closure_za_le_B : Subgroup.closure ({z, H.a} : Set G) ≤ H.B := by
  exact (toHFrame H).closure_za_le_B

theorem closure_ja_le_B : Subgroup.closure ({H.C.D.F.j, H.a} : Set G) ≤ H.B := by
  exact (toHFrame H).closure_ja_le_B

theorem closure_za : IsElemAbelian2 (Subgroup.closure ({z, H.a} : Set G)) 2 :=
  (toHFrame H).closure_za

theorem closure_ja : IsElemAbelian2 (Subgroup.closure ({H.C.D.F.j, H.a} : Set G)) 2 :=
  (toHFrame H).closure_ja

end HCtx
end S24B
end Asc77

end

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.ExactLayer
    CFSG.ClassicalInvolution.Balance.Bootstrap
namespace S24B
open CFSG.ClassicalInvolution.Asc77.S24B
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
namespace HCtx
open CFSG.ClassicalInvolution.Asc77.S24B.HCtx
variable {K K' W : Subgroup G} {S : Sylow 2 G} {R R' : Subgroup G} {z u : G}
  (H : Asc77.S24B.HCtx Ω K K' W S R R' z u)
include H in

theorem centralizer_z_le_sigma :
    Subgroup.centralizer ({z} : Set G) ≤ sigmaStarNorm Ω K := by
  exact (toHFrame H).centralizer_z_le_sigma (fun hL =>
    CFSG.ClassicalInvolution.Q8P.P24.mem_dstarComp_of_twin H.C.hs.stand.hyp H.C.hs.stand.mem hL)

theorem J_mem_dstarComp : H.C.D.F.ρ₃.K ∈ dstarComp Ω K := by
  exact (toHFrame H).J_mem_dstarComp (H.C.W_le_normalizer K H.C.hs.stand.mem ⟨H.C.x₁_mem_K,
    H.C.D.x₁_mem⟩ H.C.orderOf_x₁)
include H in

theorem centralizer_u_le_sigma :
    Subgroup.centralizer ({u} : Set G) ≤ sigmaStarNorm Ω K := by
  exact (toHFrame H).centralizer_u_le_sigma H.centralizer_z_le_sigma H.J_mem_dstarComp
end HCtx

end S24B
end Asc77

end

end CFSG.ClassicalInvolution.Q8P
