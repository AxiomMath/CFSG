module

public import CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.JSubgroup
public import CFSG.RankThree.FFModules.BinaryTransport
public import CFSG.Quasithin.Background.B15P4Layer2Final
public import CFSG.Quasithin.Background.B1MoreElevenD

public section

namespace CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF

open CFSG.RankThree.FFModules

section Component

variable {Y Z : Type*} [Group Y] [Group Z]

theorem openSubnormal_top_of_isSubnormal {H : Subgroup Y} (h : H.IsSubnormal) :
    CFSG.Open.IsSubnormal H ⊤ :=
  CFSG.Open.IsSubnormal.of_mathlib h

end Component

section Main

variable {X : Type} [Group X] {W : Type} [AddCommGroup W] [Module (ZMod 2) W]

theorem isComponentOf_map_repMulAut {ρ : Representation (ZMod 2) X W}
    (hρ : Function.Injective ρ) {C : Subgroup X} (hC : CFSG.IsComponent C) :
    CFSG.Open.IsComponentOf (C.map (repMulAut ρ)) ((⊤ : Subgroup X).map (repMulAut ρ)) := by
  have hinj := repMulAut_injective hρ
  exact ⟨Subgroup.map_mono le_top,
    isSubnormal_map (repMulAut ρ) (openSubnormal_top_of_isSubnormal hC.2),
    CFSG.ComponentClassification.Components.quasisimple_of_equiv
      (Subgroup.equivMapOfInjective C (repMulAut ρ) hinj).symm
      (CFSG.Quasithin.B1Red.isQuasisimple_to_open hC.1)⟩

theorem bestOffenderSub_le_normalizer_component [Finite X] [Finite W]
    (ρ : Representation (ZMod 2) X W) (hρ : Function.Injective ρ)
    {C : Subgroup X} (hC : CFSG.IsComponent C) :
    bestOffenderSub ρ ≤ Subgroup.normalizer (C : Set X) := by
  refine bestOffenderSub_le fun A hA hb => ?_
  by_cases hne : A = ⊥
  · subst hne
    exact bot_le
  have hinj := repMulAut_injective hρ
  have h := CFSG.Quasithin.B15P4.asB15Part4 (Multiplicative W) multiplicative_sq _ _
    ((isFFStarOffender_map_iff hρ (Subgroup.map_mono le_top)).2 ⟨hne, hA, hb⟩) _
    (isComponentOf_map_repMulAut hρ hC)
  intro a ha
  have h2 := h (Subgroup.mem_map_of_mem (repMulAut ρ) ha)
  rw [Subgroup.mem_set_normalizer_iff] at h2 ⊢
  intro x
  have h3 := h2 (repMulAut ρ x)
  rw [SetLike.mem_coe, SetLike.mem_coe, ← map_inv, ← map_mul, ← map_mul,
    Subgroup.mem_map_iff_mem hinj, Subgroup.mem_map_iff_mem hinj] at h3
  exact h3

end Main

end CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF
