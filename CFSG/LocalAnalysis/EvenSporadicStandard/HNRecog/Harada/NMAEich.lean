module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Harada.Rho
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Harada.ZStab

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Harada

open Subgroup CFSG.EvenSporadicStandard.HNRecog.HaradaLA

variable {G : Type} [Group G] {ι : Elem2 6 →* G} {w u u' : V6} {x y : G}

@[expose] def EichActs (ι : Elem2 6 →* G) (w : V6) (x : G) (u : V6) : Prop :=
  bil u w = 0 ∧ ∀ v : V6, x * coordElt ι v * x⁻¹ = coordElt ι (eichF w u v)

private lemma coordElt_injective (hι : Function.Injective ι) :
    Function.Injective (coordElt ι) := by
  intro u v huv
  have h : Multiplicative.ofAdd u = Multiplicative.ofAdd v := hι huv
  simpa using congrArg Multiplicative.toAdd h

theorem EichActs.one (w : V6) : EichActs ι w (1 : G) 0 := by
  refine ⟨bil_zero_left w, fun v => ?_⟩
  rw [eichF_zero]
  simp

theorem EichActs.of_mem_range {a : G} (ha : a ∈ ι.range) : EichActs ι w a 0 := by
  refine ⟨bil_zero_left w, fun v => ?_⟩
  rw [eichF_zero]
  exact acts_one_of_mem_range (ι := ι) ha v

theorem EichActs.mul (hx : EichActs ι w x u) (hy : EichActs ι w y u') :
    EichActs ι w (x * y) (u + u') := by
  refine ⟨?_, fun v => ?_⟩
  · rw [bil_add_left, hx.1, hy.1, add_zero]
  · have h1 : (x * y) * coordElt ι v * (x * y)⁻¹
        = x * (y * coordElt ι v * y⁻¹) * x⁻¹ := by group
    rw [h1, hy.2 v, hx.2 (eichF w u' v), eichF_comp hx.1 hy.1 v]

theorem EichActs.inv (hx : EichActs ι w x u) : EichActs ι w x⁻¹ u := by
  refine ⟨hx.1, fun v => ?_⟩
  have h := hx.2 (eichF w u v)
  rw [eichF_self hx.1 v] at h
  rw [← h]
  group

theorem EichActs.acts (hx : EichActs ι w x u) : Acts ι x (eichPerm w u hx.1) := by
  intro v
  rw [eichPerm_apply]
  exact hx.2 v

end CFSG.EvenSporadicStandard.HNRecog.Harada
