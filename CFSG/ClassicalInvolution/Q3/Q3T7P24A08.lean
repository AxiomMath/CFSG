module

public import CFSG.ClassicalInvolution.Q3.Q3T7P24A05
public import CFSG.ClassicalInvolution.Q3.Q3T7P24A06
import CFSG.ClassicalInvolution.Q3.Q3T7P24EngF08h
public import CFSG.ClassicalInvolution.Asc77.AscS24CGraph
public import CFSG.ClassicalInvolution.Asc77.AscS24CQuat

public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

namespace CFSG.ClassicalInvolution.Q3.Q3T8

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected
open scoped Pointwise
namespace S24
open CFSG.ClassicalInvolution.Asc77.S24
section Ctx
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
variable {K K' W : Subgroup G} {S : Sylow 2 G} {R R' : Subgroup G} {z u : G}
  (C : Asc77.S24B.Ctx8 Ω K K' W S R R' z u)

include C in

theorem trivMu_of_mem_A {a : G} (ha : a ∈ C.A) : S24B.TrivMu Ω W a := by
  exact CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.S24B.Ctx8Frame.trivMu_of_mem_A C.toFrame ha
theorem conj_x₂_cases {y : G} (hyN : y ∈ Subgroup.normalizer (W : Set G))
    (hyK : conjSub y K' = K') :
    y * C.D.x₂ * y⁻¹ = C.D.x₂ ∨ y * C.D.x₂ * y⁻¹ = C.D.x₂⁻¹ := by
  exact CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.S24B.Ctx8Frame.conj_x₂_cases C.toFrame hyN hyK
include C in

theorem conj_mem_R' {y : G} (hyS : y ∈ (S : Subgroup G)) (hyK : conjSub y K' = K') :
    ∀ q ∈ R', y * q * y⁻¹ ∈ R' := by
  exact CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.S24B.Ctx8Frame.conj_mem_R' C.toFrame hyS hyK
include C in

theorem innerOn_R'_iff {y : G} (hyS : y ∈ (S : Subgroup G)) (hyK : conjSub y K' = K') {k : ℤ}
    (hk : y * C.D.F.ρ'.r * y⁻¹ = C.D.F.ρ'.r * C.D.x₂ ^ k) : InnerOn y R' ↔ Even k :=
  innerOn_iff_even (Subgroup.zpowers_le.mpr C.x₂_mem_R') C.card_R' C.orderOf_x₂ C.t_mem_R'
    C.t_not_mem_zpowers C.D.t₂ (conj_x₂_cases C (C.le_normalizer_W hyS) hyK) hk
include C in

theorem hfus_I [IsSimpleGroup G] (h3 : S24B.H3) {e : G} (heS₀ : e ∉ sZero Ω W S)
    (he2 : e * e = 1) (heR : ∀ v ∈ R, v * e = e * v) (heR' : ∀ v ∈ R', v * e = e * v) (g : G)
    (hg : ∀ y ∈ (S : Subgroup G) ⊓ Subgroup.centralizer {e}, g⁻¹ * y * g ∈ (S : Subgroup G)) :
    g⁻¹ * e * g ∉ sZero Ω W S := by
  exact CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.S24B.Ctx8Frame.hfus_I C.toFrame
    (h3 G Ω K K' W S R R' z u C.hs C.hd C.h8 C.D C.hK C.hK' C.hR C.hR') heS₀ he2 heR heR' g hg
include C in

theorem hfus_II {c : G} (hcS : c ∈ (S : Subgroup G)) (hc2 : c * c = 1)
    (hcr : c * C.D.F.ρ.r = C.D.F.ρ.r * c) (hcK : conjSub c K = K)
    (hcout : ¬ InnerOn c R') (hA : ∀ a ∈ C.A, InnerOn a R') (g : G)
    (hg : ∀ y ∈ (S : Subgroup G) ⊓ Subgroup.centralizer {c}, g⁻¹ * y * g ∈ (S : Subgroup G)) :
    g⁻¹ * c * g ∉ sZero Ω W S := by
  exact CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.S24B.Ctx8Frame.hfus_II C.toFrame hcS hc2 hcr hcK
    hcout hA g hg
end Ctx
end S24
end Asc77

end

end CFSG.ClassicalInvolution.Q3.Q3T8
