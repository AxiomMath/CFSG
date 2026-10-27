module

import CFSG.ClassicalInvolution.Asc77.AscT8YAEng
public import CFSG.ClassicalInvolution.Asc77.AscT8YA1

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.Thompson
  CFSG.ClassicalInvolution.Asc77.MuTab CFSG.ClassicalInvolution.Asc77.AscP1Nine3
  CFSG.StronglyEmbedded.UniqueCoset CFSG.ClassicalInvolution.Balance.Theorem5

namespace T8YY


variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}
  {K J : Subgroup G} {S : Sylow 2 G} {R T W : Subgroup G} {z t : G}

namespace FrameData

@[expose] def vGroup (F : FrameData Ω W K J z t) : Subgroup G :=
  Subgroup.closure ({F.zz 0 * F.zz 1, F.zz 0 * F.zz 2} : Set G)

end FrameData

theorem mul_self_of_commute {x y : G} (hx : x * x = 1) (hy : y * y = 1) (h : x * y = y * x) :
    x * y * (x * y) = 1 := by
  calc x * y * (x * y) = x * (y * x) * y := by group
    _ = x * (x * y) * y := by rw [← h]
    _ = (x * x) * (y * y) := by group
    _ = 1 := by rw [hx, hy, one_mul]

theorem centralizer_le_normalizer_alpha_of_frattini [IsSimpleGroup G]
    (hs : Std8 p f Ω K J S R T W z t) (F : FrameData Ω W K J z t)
    (hfr : ∀ c ∈ Subgroup.centralizer ({z * t} : Set G),
      ∃ o ∈ oddCoreOf (T8.layerJoin Ω (z * t)), conjSub (o * c) F.vGroup = F.vGroup) :
    Subgroup.centralizer ({z * t} : Set G) ≤
      Subgroup.normalizer (alphaOf (Subgroup.closure ({t, z} : Set G)) : Set G) := by
  have hp : p ≠ 2 := hs.stand.odd
  have hΩ : HypOmegaMod p f Ω := hs.stand.hyp
  have hnt : ∀ M ∈ Ω, ∀ M' ∈ twinSet Ω M, M' = M := fun M hM =>
    T8.noTwins_of_mem hΩ.conjInvariant hs.stand.trans hs.noTwins hM
  obtain ⟨R₃, hF, hind⟩ := F.exists_triFrame hs
  have hHyp : Hyp51 (Subgroup.closure ({z, t, F.zz 2} : Set G)) :=
    T8T.hyp51Tri_proved p f G Ω ![K, J, (F.ρ 2).K] ![z, t, F.zz 2] R₃ hs.stand hnt hF
      (by simpa using hind)
  have hc01 : z * t = t * z := hF.comm hp hΩ 0 1
  have hc02 : z * F.zz 2 = F.zz 2 * z := hF.comm hp hΩ 0 2
  have hc12 : t * F.zz 2 = F.zz 2 * t := hF.comm hp hΩ 1 2
  exact centralizer_le_normalizer_alpha_of_frattiniE F hnt hF hind hHyp hc01 hc02 hc12
    F.vGroup rfl (T8T.oddCoreOf_layerJoin_le_oddCoreOf_centralizer hΩ (z * t)) hfr

end T8YY

end CFSG.ClassicalInvolution.Asc77
