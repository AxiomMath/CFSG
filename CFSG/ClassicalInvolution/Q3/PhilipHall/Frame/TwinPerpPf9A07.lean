module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpPf9A06
public import CFSG.ClassicalInvolution.Asc77.AscS24CGraph
import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpPf9Ctx8Frame
import CFSG.ClassicalInvolution.Q3.Q3T7P24EngF07h

public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

namespace CFSG.ClassicalInvolution.Q8P

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected
namespace S24
open CFSG.ClassicalInvolution.Asc77.S24
section Ctx
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
variable {K K' W : Subgroup G} {S : Sylow 2 G} {R R' : Subgroup G} {z u : G}
  (C : Asc77.S24B.Ctx8F Ω K K' W S R R' z u)
include C in

theorem acts_pm {y : G} (hyS : y ∈ (S : Subgroup G)) (hT : S24B.TrivMu Ω W y) :
    (∀ w ∈ W, y * w * y⁻¹ = w) ∨ (∀ w ∈ W, y * w * y⁻¹ = w⁻¹) := by
  exact CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.S24B.Ctx8Frame.acts_pm C.toFrame hyS hT
include C in

theorem exists_centralizes_r {y : G} (hyS : y ∈ (S : Subgroup G)) (hT : S24B.TrivMu Ω W y)
    (hinv : ∀ w ∈ W, y * w * y⁻¹ = w⁻¹) :
    ∃ k : ℤ, (y * C.D.x₃ ^ k) * C.D.F.ρ.r = C.D.F.ρ.r * (y * C.D.x₃ ^ k) := by
  exact CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.S24B.Ctx8Frame.exists_centralizes_r C.toFrame hyS
    hT hinv
include C in

theorem graph_sq [CoreLike G] [Fact (CFSG.ClassicalInvolution.Q8P.P24.Hyp51TwinInnerAt Ω)] (h3 : S24B.H3) {c : G} (hcS : c ∈ (S : Subgroup G))
    (hT : S24B.TrivMu Ω W c) (hinv : ∀ w ∈ W, c * w * c⁻¹ = w⁻¹) : c * c = 1 := by
  exact CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.S24B.Ctx8Frame.graph_sq C.toFrame
    (h3 G Ω K K' W S R R' z u C.hyp C.h8 C.D C.hK C.hK' C.hR C.hR') hcS hT hinv
include C in

theorem not_mem_sZero {c : G} (hinv : ∀ w ∈ W, c * w * c⁻¹ = w⁻¹) : c ∉ sZero Ω W S := by
  exact CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.S24B.Ctx8Frame.not_mem_sZero C.toFrame hinv
include C in

theorem mem_or_inv_mul_mem_sZero {c y : G} (hcS : c ∈ (S : Subgroup G))
    (hinv : ∀ w ∈ W, c * w * c⁻¹ = w⁻¹) (hyS : y ∈ (S : Subgroup G)) :
    y ∈ sZero Ω W S ∨ c⁻¹ * y ∈ sZero Ω W S := by
  exact CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.S24B.Ctx8Frame.mem_or_inv_mul_mem_sZero C.toFrame
    hcS hinv hyS
include C in

theorem commutator_mem_sZero {c : G} (hcS : c ∈ (S : Subgroup G))
    (hinv : ∀ w ∈ W, c * w * c⁻¹ = w⁻¹) :
    ∀ y₁ ∈ (S : Subgroup G), ∀ y₂ ∈ (S : Subgroup G), y₁ * y₂ * y₁⁻¹ * y₂⁻¹ ∈ sZero Ω W S := by
  exact CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.S24B.Ctx8Frame.commutator_mem_sZero C.toFrame hcS
    hinv
end Ctx
end S24
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

theorem exists_gen [CoreLike G] [Fact (CFSG.ClassicalInvolution.Q8P.P24.Hyp51TwinInnerAt Ω)] (h3 : H3) (hng : NoGraph)
    (hSP : ¬ (S : Subgroup G) ≤ MGrp Ω W) :
    ∃ g₀ ∈ (S : Subgroup G), g₀ ^ 4 ∈ (S : Subgroup G) ⊓ MGrp Ω W ∧
      (∀ y ∈ (S : Subgroup G), ∃ k : ℤ, (g₀ ^ k)⁻¹ * y ∈ (S : Subgroup G) ⊓ MGrp Ω W) ∧
      ∃ d ∈ C.Dg, d * d = z := by
  exact CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.S24B.Ctx8Frame.exists_gen C.toFrame
    (h3 G Ω K K' W S R R' z u C.hyp C.h8 C.D C.hK C.hK' C.hR C.hR')
    (hng G Ω K K' W S R R' z u C.hyp C.h8 hSP) hSP
end Ctx8F
end S24B
end Asc77

end

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected
namespace S24
open CFSG.ClassicalInvolution.Asc77.S24
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
variable {K K' W : Subgroup G} {S : Sylow 2 G} {R R' : Subgroup G} {z u : G}
  (C : Asc77.S24B.Ctx8F Ω K K' W S R R' z u)
theorem inv_W {w : G} (hw : w ∈ W) (h2 : w * w = 1) :
    w = 1 ∨ w = z ∨ w = C.D.F.j ∨ w = z * C.D.F.j := by
  exact CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.S24B.Ctx8Frame.inv_W C.toFrame hw h2
include C in

theorem twin_cases {h : G} (hh : h ∈ Subgroup.centralizer ({z} : Set G)) :
    (conjSub h K = K ∧ conjSub h K' = K') ∨ (conjSub h K = K' ∧ conjSub h K' = K) := by
  exact CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.S24B.Ctx8Frame.twin_cases C.toFrame hh
include C in

theorem exists_centralizer_conj_W {W₁ : Subgroup G} (hW₁ : W₁ ∈ WSet Ω) (hzW₁ : z ∈ W₁) :
    ∃ h ∈ Subgroup.centralizer ({z} : Set G), conjSub h W = W₁ := by
  exact CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.S24B.Ctx8Frame.exists_centralizer_conj_W C.toFrame
    hW₁ hzW₁
end S24
end Asc77

end

end CFSG.ClassicalInvolution.Q8P
