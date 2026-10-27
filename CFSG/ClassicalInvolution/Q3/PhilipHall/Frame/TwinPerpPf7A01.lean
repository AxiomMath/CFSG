module

public import CFSG.ClassicalInvolution.Q3.Q3T7P24A01
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpPf5M1

public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

namespace CFSG.ClassicalInvolution.Q8P

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected
variable {G : Type} [Group G]
section Transport
variable [Finite G] {Ω : Set (Subgroup G)} {K L : Subgroup G}

theorem AscStand.of_mem (h : AscStand Ω K) (hL : L ∈ Ω) : AscStand Ω L where
  hyp := h.hyp
  cls := h.cls
  aEmpty := h.aEmpty
  card8 := h.card8
  gen2 := h.gen2
  mem := hL
  trans := by
    obtain ⟨g₀, hg₀⟩ := h.trans L hL
    intro J hJ
    obtain ⟨g, hg⟩ := h.trans J hJ
    refine ⟨g * g₀⁻¹, ?_⟩
    rw [conjSub_mul, ← hg₀, conjSub_inv_conjSub, hg]
  gen := h.gen
end Transport
end Asc77

end

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected
open scoped commutatorElement

structure Hyp24 {G : Type} [Group G] [Finite G] (Ω : Set (Subgroup G)) (K K' W : Subgroup G)
    (S : Sylow 2 G) (R R' : Subgroup G) (z u : G) : Prop where
  std : Hyp23 Ω K K' z
  hW : W ∈ WSet Ω
  hzW : z ∈ W
  hS4 : MuIsoS4 Ω W
  hZ : W ⊓ Asc77.centerIn (Subgroup.normalizer (W : Set G)) = ⊥
  hWS : W ≤ (S : Subgroup G)
  hR : R ∈ RSet Ω ∧ R ≤ K ∧ R ≤ (S : Subgroup G)
  hR' : R' ∈ RSet Ω ∧ R' ≤ K' ∧ R' ≤ (S : Subgroup G)
  hu : u ∈ K ⊔ K' ∧ u ∈ W ∧ u * u = 1 ∧ u ≠ 1 ∧ u ≠ z
end Asc77

end

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Disconnected
    CFSG.ClassicalInvolution.Asc77.Thompson
namespace Thompson
variable {G : Type} [Group G] {Ω : Set (Subgroup G)} {W : Subgroup G}
section Generators
variable [Finite G]

theorem eq_closure_pair {Ω : Set (Subgroup G)} (hΩ : HypOmegaMod Ω) {W : Subgroup G} (hW : W ∈ WSet
    Ω) {R : Subgroup G}
    (hR : R ∈ DSet Ω W) {u r : G} (hu : Subgroup.zpowers u = R ⊓ W) (hr : r ∈ R) (hrW : r ∉ W) :
    R = Subgroup.closure {u, r} :=
  CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.Thompson.eq_closure_pair hΩ hW hR hu hr hrW
end Generators
end Thompson
end Asc77

end

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected
@[expose] def C23_1_clique : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [CoreLike G] (Ω : Set (Subgroup G)) (K K' : Subgroup G)
    (z : G), Hyp23Setting Ω K K' z → ∀ W ∈ WSet Ω,
      (Thompson.muDelta Ω W).Nonempty ∧ ∀ d ∈ Thompson.muDelta Ω W,
        (Star3T.cent (Thompson.muDelta Ω W) d).ncard = 2
end Asc77

end

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected
section Conversions
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {K K' W : Subgroup G}
  {S : Sylow 2 G} {R R' : Subgroup G} {z u t u₁ u₂ : G}

theorem Hyp24.data (h : Hyp24 Ω K K' W S R R' z u) : Hyp24Data Ω K K' W S R R' z u where
  hW := h.hW
  hzW := h.hzW
  hS4 := h.hS4
  hZ := h.hZ
  hWS := h.hWS
  hR := h.hR
  hR' := h.hR'
  hu := h.hu
end Conversions
end Asc77

end

end CFSG.ClassicalInvolution.Q8P
