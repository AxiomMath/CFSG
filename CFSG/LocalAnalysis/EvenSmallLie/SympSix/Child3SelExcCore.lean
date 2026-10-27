module

public import CFSG.LocalAnalysis.ComponentClassification.ExcSelectorReduction
public import CFSG.LocalAnalysis.ComponentInitial.SteinbergBISp6EvenSymplecticCore

public section

namespace CFSG.EvenSmallLie.Child3.SelExc

open Subgroup CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.ExcSelector
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.LocalAnalysis.ComponentInitial.SteinbergBI
open CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix.FusionOrbits
  (isSimpleGroup_GL_three_two)

theorem isSimpleGroup_and_nonabelian_of_GL_three_two {X : Type} [Group X]
    (e : X ≃* GL (Fin 3) (ZMod 2)) : IsSimpleGroup X ∧ ∃ x y : X, x * y ≠ y * x := by
  have := isSimpleGroup_GL_three_two
  refine ⟨e.isSimpleGroup, ?_⟩
  obtain ⟨x, y, hxy⟩ := exists_mul_ne_mul_GL_three_two
  exact ⟨e.symm x, e.symm y, fun h => hxy (by simpa using congrArg e h)⟩

theorem smallType_of_GL_three_two {X : Type} [Group X] (e : X ≃* GL (Fin 3) (ZMod 2)) :
    SmallType X := by
  obtain ⟨hs, hnab⟩ := isSimpleGroup_and_nonabelian_of_GL_three_two e
  obtain ⟨-, hcen⟩ := isQuasisimple_and_center_eq_bot hnab
  have hsrc : StatedClassicalModel (X ⧸ center X) .PSL 2 7 1 :=
    classicalModel_PSL_two_seven_of_mulEquiv
      (((QuotientGroup.quotientMulEquivOfEq hcen).trans QuotientGroup.quotientBot).trans e)
  have hmem : (StatedLieTag.PSL) ∈ CFSG.Blueprint.classicalTags := by decide
  refine Or.inl ⟨7, 1, Nat.prime_seven, by norm_num, le_rfl, by norm_num, Or.inl ⟨hmem, hsrc⟩,
    ?_⟩
  rw [hcen, Subgroup.card_bot]
  exact odd_one

theorem false_of_noSmallComponent {Y : Type} [Group Y] {D : Subgroup Y} [D.Normal]
    (hCD : centralizer (D : Set Y) = ⊥) {a : Y} (ha : orderOf a = 2) {J : Subgroup Y}
    (hJD : J ≤ D) (hJa : J ≤ centralizer ({a} : Set Y))
    (hC : zpowers a ⊔ J = centralizer ({a} : Set Y))
    (hJ : Nonempty (J ≃* GL (Fin 3) (ZMod 2))) (h : NoSmallComponent D) : False := by
  obtain ⟨eJ⟩ := hJ
  set α : MulAut D := MulAut.conjNormal a with hα
  have hfix := fixedSubgroup_conjNormal (W := D) a
  have hα2 : α ^ 2 = 1 := by
    rw [hα, ← map_pow, ← ha, pow_orderOf_eq_one, map_one]
  have hα1 : α ≠ 1 := by
    intro h1
    have haC : a ∈ centralizer (D : Set Y) := by
      rw [mem_centralizer_iff]
      intro w hw
      have h2 := congrArg (fun φ : MulAut D => ((φ ⟨w, hw⟩ : D) : Y)) h1
      simp only [hα, MulAut.conjNormal_apply, MulAut.one_apply] at h2
      calc w * a = a * w * a⁻¹ * a := by rw [h2]
        _ = a * w := by group
    rw [hCD, mem_bot] at haC
    rw [haC, orderOf_one] at ha
    exact absurd ha (by norm_num)
  obtain ⟨hs, hnab⟩ := isSimpleGroup_and_nonabelian_of_GL_three_two eJ
  obtain ⟨hquasi, -⟩ := isQuasisimple_and_center_eq_bot hnab
  have hJn := normal_subgroupOf_centralizer_of_sup_eq hJa hC
  set K := J.subgroupOf D with hK
  have hKJ : K ≃* J := Subgroup.subgroupOfEquivOfLe hJD
  have hKc : Assembly.IsComponentOf K (fixedSubgroup α) := by
    rw [hfix]
    refine ⟨fun x hx => Subgroup.mem_subgroupOf.2 (hJa (Subgroup.mem_subgroupOf.1 hx)), ?_,
      assembly_isQuasisimple_of_equiv hKJ.symm hquasi⟩
    exact CFSG.LocalAnalysis.ComponentInitial.assembly_isSubnormal_comap D.subtype
      (Assembly.IsSubnormal.step hJa hJn (Assembly.IsSubnormal.refl _))
  have hKn : (K.subgroupOf (fixedSubgroup α)).Normal := by
    refine ⟨fun n hn g => ?_⟩
    have hg : ((g : D) : Y) ∈ centralizer ({a} : Set Y) := by
      have h1 : (g : D) ∈ (centralizer ({a} : Set Y)).subgroupOf D := hfix ▸ g.2
      exact Subgroup.mem_subgroupOf.1 h1
    have hn' : (((n : fixedSubgroup α) : D) : Y) ∈ J :=
      Subgroup.mem_subgroupOf.1 (Subgroup.mem_subgroupOf.1 hn)
    have h2 := hJn.conj_mem ⟨_, hJa hn'⟩ (Subgroup.mem_subgroupOf.2 hn') ⟨_, hg⟩
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    exact Subgroup.mem_subgroupOf.1 h2
  exact h α hα2 hα1 K hKc hKn (smallType_of_GL_three_two (hKJ.trans eJ))

end CFSG.EvenSmallLie.Child3.SelExc
