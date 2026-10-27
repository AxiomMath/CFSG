module

import CFSG.ClassicalInvolution.Asc77.AscT7U11Eng
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp25Nine
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpPf5M4
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpPf5M6

public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

namespace CFSG.ClassicalInvolution.Q8P.Asc77.P25S

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77
  CFSG.ClassicalInvolution.Asc77.T7U CFSG.ClassicalInvolution.Q8P.Asc77.P25R
  CFSG.ClassicalInvolution.Q8P.Asc77

variable {G : Type} [Group G] [Finite G] [CoreLike G] {Ω : Set (Subgroup G)} {K K' W : Subgroup G}
  {S : Sylow 2 G} {R R' : Subgroup G} {z t u₁ u₂ : G}

private theorem hyp25F_q8p (hyp : Hyp25 Ω K K' W S R R' z t u₁ u₂) :
    Hyp25F K S R R' z where
  hz2 := hyp.std.setting.hz.sq
  hz1 := hyp.std.setting.hz.ne_one
  hzS := hyp.hzS
  hRS := hyp.hR.2.2
  zA := (z_facts hyp).1
  swap_nf := T7G2.exists_swap_nonfused hyp
  hRne := T7ER.ne_of_hyp25 hyp
  cA := fun hs => cA_normal hyp hs
  twin_sq := fun hx =>
      T7T.twin_sq (show Hyp23Setting Ω K K' z from hyp.std.setting) hx
  not_norm := fun hg hzt hnf => T7G2.not_normalizes_of_nonfused hyp hg hzt hnf
  c25_5 := fun A hzA hAS hAn hall =>
      T7T.c25_5_proved G Ω K K' W S R R' z t u₁ u₂ hyp A hzA hAS hAn hall

theorem exists_normal_four_bad (hyp : Hyp25 Ω K K' W S R R' z t u₁ u₂)
    (hne : (S : Subgroup G) ⊓ Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G) ≠
      Subgroup.zpowers z) :
    ∃ a ∈ (S : Subgroup G) ⊓ Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G),
      a * a = 1 ∧ a ≠ 1 ∧ a ≠ z ∧
        (∀ s ∈ (S : Subgroup G), s * a * s⁻¹ = a ∨ s * a * s⁻¹ = a * z) ∧
        z ∉ zStarOf (Subgroup.centralizer ({a} : Set G)) := by
  exact CFSG.ClassicalInvolution.Asc77.T7U.exists_normal_four_badE (hyp25F_q8p hyp) hne

theorem comm_swap_of_normal_four (hyp : Hyp25 Ω K K' W S R R' z t u₁ u₂) {t' g : G}
    (ht'S : t' ∈ (S : Subgroup G)) (ht'2 : t' * t' = 1) (hg : g * z * g⁻¹ = t')
    (hnf : ¬ ∃ y : G, y * z * y⁻¹ = t' * z) {a : G} (haS : a ∈ (S : Subgroup G))
    (hconj : ∀ s ∈ (S : Subgroup G), s * a * s⁻¹ = a ∨ s * a * s⁻¹ = a * z) :
    t' * a = a * t' := by
  exact CFSG.ClassicalInvolution.Asc77.T7U.comm_swap_of_normal_fourE (hyp25F_q8p hyp) ht'S ht'2 hg
    hnf haS hconj
end CFSG.ClassicalInvolution.Q8P.Asc77.P25S
