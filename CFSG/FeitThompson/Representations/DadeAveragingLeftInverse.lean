module

public import CFSG.FeitThompson.Representations.DadeMapWellDefinedLinear
public import CFSG.FeitThompson.Representations.DadeAveragingClassFunction

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

variable {G : Type*} [Group G] {L : Subgroup G} {A : Set G} {H : G → Subgroup G}

section

variable [Fintype G]

theorem dadeAverage_dadeMap (hD : IsDadeData L A H) (f : dadeDomain L A) :
    dadeAverage A H ((dadeMap hD f : classFun G) : G → ℂ)
      = extendByZero L (f : ↥L → ℂ) := by
  funext x
  by_cases hx : x ∈ A
  ·
    refine dadeAverage_apply_of_eq_on hx fun u hu => ?_
    rw [dadeMap_apply_of_mem_dadeSupport hD f hx
      (dadeCoset_subset_dadeSupport H x (mul_mem_dadeCoset hu)),
      extendByZero_of_mem _ (hD.mem_of_mem hx)]
  · rw [dadeAverage_eq_zero_of_notMem hx]
    by_cases hxL : x ∈ L
    · rw [extendByZero_of_mem _ hxL, dadeDomain.apply_eq_zero f.2 hx]
    · rw [extendByZero_of_notMem L _ hxL]

theorem dadeAverage_dadeMap_apply (hD : IsDadeData L A H) (f : dadeDomain L A) (y : ↥L) :
    dadeAverage A H ((dadeMap hD f : classFun G) : G → ℂ) (y : G) = (f : ↥L → ℂ) y := by
  rw [dadeAverage_dadeMap hD f, extendByZero_apply_coe]

theorem dadeAverageCF_comp_dadeMap (hD : IsDadeData L A H) :
    (dadeAverageCF hD).comp (dadeMap hD) = Submodule.inclusion (dadeDomain_le_classFun L A) := by
  refine LinearMap.ext fun f => Subtype.ext ?_
  funext y
  simp only [LinearMap.comp_apply, dadeAverageCF_apply, Submodule.inclusion_apply]
  exact dadeAverage_dadeMap_apply hD f y

end

theorem dadeMap_injective [Finite G] (hD : IsDadeData L A H) :
    Function.Injective (dadeMap hD) := by
  have : Fintype G := Fintype.ofFinite G
  intro f g hfg
  refine Submodule.inclusion_injective (dadeDomain_le_classFun L A) ?_
  rw [← dadeAverageCF_comp_dadeMap hD, LinearMap.comp_apply, LinearMap.comp_apply, hfg]

end CFSG.FeitThompson
