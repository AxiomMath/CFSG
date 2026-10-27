module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.EscapingCaseOneQuotient

public section

namespace CFSG.ProperTwoGeneratedCore.Assembly

open CFSG.Open CFSG.BenderSuzuki CFSG.BenderSuzuki.PFchapter1section1

@[expose] def GeneralizedFittingUniqueInvolutionRankBound : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (t : X), pPrimeCore 2 X = ⊥ → t ∈ Subgroup.center X →
    orderOf t = 2 → layer X ≠ ⊥ → (∀ y ∈ generalizedFitting X, orderOf y = 2 → y = t) →
      CFSG.Open.twoRank X ≤ 2

theorem component_le_layer {X : Type*} [Group X] {L : Subgroup X} (hL : CFSG.IsComponent L) :
    L ≤ layer X :=
  le_sSup hL

theorem generalizedFitting_normal' (X : Type*) [Group X] : (generalizedFitting X).Normal := by
  have : (layer X).Normal := by
    rw [CFSG.layer_eq_componentClassification]
    exact CFSG.ComponentClassification.Layer.normal _
  exact Subgroup.sup_normal _ _

variable {G : Type} [Group G] [Finite G] {H : Subgroup G} {x : G}

namespace EscapingQuotientData

variable (hq : EscapingQuotientData H x)
include hq

theorem fitting_le_image : fittingSubgroup (EscapingQuotient x) ≤ escapingImage H x := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨U, hUH, -⟩ := hq.sylow
  have h2 : IsPGroup 2 (fittingSubgroup (EscapingQuotient x)) :=
    CFSG.isPGroup_of_nilpotent_normal _ inferInstance inferInstance hq.oddCore_eq_bot
  exact (h2.le_sylow_of_normal U).trans hUH

variable (hE : layer (EscapingQuotient x) ≤ escapingImage H x)
include hE

theorem generalizedFitting_le_image :
    generalizedFitting (EscapingQuotient x) ≤ escapingImage H x :=
  sup_le hq.fitting_le_image hE

theorem eq_bar_of_mem_generalizedFitting {y : EscapingQuotient x}
    (hy : y ∈ generalizedFitting (EscapingQuotient x)) (hy2 : orderOf y = 2) :
    y = escapingBar x := by
  have := generalizedFitting_normal' (EscapingQuotient x)
  obtain ⟨m, hm⟩ : ∃ m, m ∉ escapingImage H x := by
    by_contra h
    push Not at h
    exact hq.image_ne_top (eq_top_iff.mpr fun m _ => h m)
  exact hq.eq_bar_of_conj_mem hm (hq.generalizedFitting_le_image hE hy)
    (hq.generalizedFitting_le_image hE ((inferInstance : (generalizedFitting _).Normal).conj_mem
      y hy m)) hy2

theorem false_of_layer_le_image (h83 : GeneralizedFittingUniqueInvolutionRankBound) : False := by
  have h := h83 (EscapingQuotient x) (escapingBar x) hq.oddCore_eq_bot hq.bar_mem_center
    hq.bar_order hq.layer_ne_bot fun y hy hy2 => hq.eq_bar_of_mem_generalizedFitting hE hy hy2
  have := hq.rank
  omega

end EscapingQuotientData

theorem coreSetting_exists_component_not_le_image
    (h83 : GeneralizedFittingUniqueInvolutionRankBound) {S : Sylow 2 G} {z : G}
    (hset : CoreSetting G S H) (hz : IsCentralInvolution (S : Subgroup G) z)
    (hesc : ¬ Subgroup.centralizer ({z} : Set G) ≤ H) :
    ∃ J : Subgroup (EscapingQuotient z), CFSG.IsComponent J ∧ ¬ J ≤ escapingImage H z := by
  have hq := escapingQuotientData hset (hset.sylow_le hz.1) hz.2.1 hesc
  by_contra hcon
  push Not at hcon
  exact hq.false_of_layer_le_image (sSup_le fun J hJ => hcon J hJ) h83

end CFSG.ProperTwoGeneratedCore.Assembly
