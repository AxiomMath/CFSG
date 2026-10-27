module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryC1OuterGmsLocal

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.RankOne

open Subgroup CFSG.ABGLocalTools CFSG.Open

namespace U3C1OuterSwapHigh

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G}
  {T R₂ D : Subgroup G} {d : G} {V U U₁ : Subgroup G} {w s : G} {P : Subgroup G}
  (hW : U3C1OuterSwapHigh G L f t T R₂ D d V U U₁ w s P)
include hW

theorem gmg_oddCore_I :
    componentClassificationOddCore (centralizer ({t * w} : Set G)) = ⊥ := by
  have hne : t * w ≠ 1 := fun h => hW.tw_not_mem (by rw [h]; exact one_mem _)
  have hord : orderOf (t * w) = 2 := orderOf_eq_prime hW.tw_sq hne
  exact hW.step.start.setting.2.2.2.2.1 (t * w) hord

theorem gmg_oddCore_M (M : Subgroup (centralizer ({t * w} : Set G))) (hMn : M.Normal) :
    CFSG.oddCore M = ⊥ := by
  have := hMn
  exact CFSG.ComponentClassification.OddCore.subnormal_corefree hW.gmg_oddCore_I M
    (IsSubnormal.step le_top inferInstance (IsSubnormal.refl ⊤))

theorem gmg_goldschmidt (hTop : CFSG.Goldschmidt.TopStatement) {J : Subgroup G}
    (hS₀ : IsSylowOf 2 (swapS₂ P U T ⊓ centralizer ({t * w} : Set G))
      (centralizer ({t * w} : Set G)))
    (hJS : J ≤ swapS₂ P U T ⊓ centralizer ({t * w} : Set G))
    (hJab : ∀ a ∈ J, ∀ b ∈ J, a * b = b * a)
    (hJcl : ∀ a ∈ J, ∀ g ∈ centralizer ({t * w} : Set G),
      g⁻¹ * a * g ∈ swapS₂ P U T ⊓ centralizer ({t * w} : Set G) → g⁻¹ * a * g ∈ J)
    (M : Subgroup (centralizer ({t * w} : Set G)))
    (hM : Subgroup.normalClosure
      ((J.subgroupOf (centralizer ({t * w} : Set G)) : Subgroup (centralizer ({t * w} : Set G))) :
        Set (centralizer ({t * w} : Set G))) = M) :
    CFSG.oddCore M = ⊥ ∧
    ∃ Q : Sylow 2 (centralizer ({t * w} : Set G)),
      (Q : Subgroup (centralizer ({t * w} : Set G))).map (centralizer ({t * w} : Set G)).subtype =
        swapS₂ P U T ⊓ centralizer ({t * w} : Set G) ∧
      CFSG.Open.pCore 2 M ⊔ goldschmidtLayer M = ⊤ ∧
      (J.subgroupOf (centralizer ({t * w} : Set G))).subgroupOf M = CFSG.Open.pCore 2 M ⊔
        Subgroup.closure {x | x ∈ (Q : Subgroup (centralizer ({t * w} : Set G))).subgroupOf M ⊓
          goldschmidtLayer M ∧ x ^ 2 = 1} ∧
      ∀ K : Subgroup M, IsComponentOf K ⊤ → goldschmidtSimpleType (K ⧸ Subgroup.center K) := by
  have hMn : M.Normal := by
    rw [← hM]
    exact Subgroup.normalClosure_normal
  have hO := hW.gmg_oddCore_M M hMn
  refine ⟨hO, ?_⟩
  obtain ⟨Q, hQ⟩ := hS₀
  refine ⟨Q, hQ, ?_⟩
  have hAQ : J.subgroupOf (centralizer ({t * w} : Set G)) ≤
      (Q : Subgroup (centralizer ({t * w} : Set G))) := by
    intro a ha
    have haS : (a : G) ∈ swapS₂ P U T ⊓ centralizer ({t * w} : Set G) :=
      hJS (mem_subgroupOf.mp ha)
    rw [← hQ] at haS
    obtain ⟨q, hq, hqa⟩ := mem_map.mp haS
    have : q = a := Subtype.ext hqa
    exact this ▸ hq
  have hAab : IsMulCommutative (J.subgroupOf (centralizer ({t * w} : Set G))) :=
    ⟨⟨fun a b => Subtype.ext (Subtype.ext (hJab _ (mem_subgroupOf.mp a.2) _
      (mem_subgroupOf.mp b.2)))⟩⟩
  have hcl : ∀ a ∈ J.subgroupOf (centralizer ({t * w} : Set G)),
      ∀ x : centralizer ({t * w} : Set G),
        x⁻¹ * a * x ∈ (Q : Subgroup (centralizer ({t * w} : Set G))) →
          x⁻¹ * a * x ∈ J.subgroupOf (centralizer ({t * w} : Set G)) := by
    intro a ha x hx
    have hxS : ((x⁻¹ * a * x : centralizer ({t * w} : Set G)) : G) ∈
        swapS₂ P U T ⊓ centralizer ({t * w} : Set G) := by
      rw [← hQ]
      exact mem_map_of_mem _ hx
    have hmem := hJcl (a : G) (mem_subgroupOf.mp ha) (x : G) x.2 (by simpa using hxS)
    exact mem_subgroupOf.mpr (by simpa using hmem)
  exact CFSG.ComponentClassification.AschbacherTheorem3.goldschmidt_subgroup hTop Q hAQ hAab hcl
    hM hO

end U3C1OuterSwapHigh

end CFSG.SeitzReduction.RankOne
