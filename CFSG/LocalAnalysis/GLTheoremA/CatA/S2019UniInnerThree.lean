module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S2019ClassicalParts
import CFSG.LocalAnalysis.GLTheoremA.CatA.S2019UniThreeSelfDual
import all CFSG.HardMathSupport.Solomon.Coordinator.LieComp.UnitaryInnerExport
public import CFSG.RankThree.PartOne.KC.UnitaryCrossPrimeSpecial

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S2019

open Polynomial CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
  CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCUnitary
  CFSG.RankThree.PartOne.KCUnitaryModel CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp

theorem s2019UniInner_three : S2019UniInner (· = 3) := by
  intro p q hp hp2 hq hq2 hqp hq3 f K _ h n A c hA L hL T hT2 hLT
  classical
  change q = 3 at hq3
  subst hq3
  haveI := h.finite
  haveI : CharP K 3 := h.charP
  have hq' : 2 ≤ 3 ^ f := le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) h.one_le)
  have hpq : p ≠ 3 := Ne.symm hqp
  have hperf : ⁅L, L⁆ = L := glaPComponent_perfect hL
  have hle := perfectInLayer_primeFormConjHom h hp hpq A hA L hL.1 hperf
  obtain ⟨hcomp, -⟩ := glaPComponent_isComponent_of_le_layer hL hle
  have H := primaryData_toLin' h A.2 hp hpq hA
  obtain ⟨⟨a, hgood⟩, hLeq⟩ := exists_good_primaryFactor_of_component hq' A rfl H L hcomp
  set SB := specialBlock (idForm h n) (Matrix.GeneralLinearGroup.toLin (A : GL (Fin n) K))
    (a : K[X]) with hSB
  set F : Subgroup ↥(gramSU h (idGram K n)) := SB.comap (toLinSU h n) with hF
  have hSBle : SB ≤ (toLinSU h n).range := fun y hy =>
    mem_range_toLinSU (specialBlock_le_sesqSpecialUnitaryGroup_of_good H hq' a hgood hy)
  have hFmap : F.map (toLinSU h n) = SB := Subgroup.map_comap_eq_self hSBle
  have hfacts := specialBlockFacts_of_good H hq' a hgood
  have hFperf : ⁅F, F⁆ = F := by
    apply Subgroup.map_injective (toLinSU_injective (h := h) (n := n))
    rw [Subgroup.map_commutator, hFmap]
    exact Subgroup.isPerfect_iff.mp (hfacts.quasisimple hgood.1).1
  obtain ⟨P₀, hP₀SB, hP₀3, hP₀9, hP₀Z, hP₀q⟩ :=
    exists_pGroup_specialBlock_three H rfl a hgood hfacts
  set P : Subgroup ↥(gramSU h (idGram K n)) := P₀.comap (toLinSU h n) with hP
  have hP₀le : P₀ ≤ (toLinSU h n).range := hP₀SB.trans hSBle
  have hPmap : P.map (toLinSU h n) = P₀ := Subgroup.map_comap_eq_self hP₀le
  refine commutator_eq_bot_of_quadratic_lift_three hcomp.2.2 hLT hT2
    (QuotientGroup.mk' (normOneScalars h (gramSU h (idGram K n)) n))
    (QuotientGroup.mk'_surjective _)
    (by rw [QuotientGroup.ker_mk']; exact normOneScalars_le_center h _ n)
    (toLinSU h n) (toLinSU_injective (h := h) (n := n)) hFperf hLeq.symm
    (Subgroup.comap_mono hP₀SB) (hP₀3.comap_of_injective _ (toLinSU_injective (h := h) (n := n)))
    ?_ ?_ ?_
  ·
    rw [← Subgroup.card_map_of_injective (toLinSU_injective (h := h) (n := n)), hPmap]
    exact hP₀9
  ·
    intro u hu hcent
    apply toLinSU_injective (h := h) (n := n)
    rw [map_one]
    refine hP₀Z _ hu fun g hg => ?_
    obtain ⟨s, rfl⟩ := hSBle hg
    have hs : s ∈ F := by
      rw [hF, Subgroup.mem_comap]
      exact hg
    rw [← map_mul, ← map_mul, hcent s hs]
  ·
    intro u hu hcent _
    refine hP₀q _ hu fun w hw => ?_
    obtain ⟨s, rfl⟩ := hP₀le hw
    have hs : s ∈ P := by
      rw [hP, Subgroup.mem_comap]
      exact hw
    rw [← map_mul, ← map_mul, hcent s hs]

end CFSG.LocalAnalysis.GLTheoremA.S2019
