module

public import CFSG.ThirdParty.QiuzhenCFSG.Theory.Character.ClassFunction
public import Mathlib.Algebra.Group.ConjFinite
public import Mathlib.Combinatorics.Matroid.Init
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

public section

namespace CFSG

namespace Theory.Character

noncomputable section

open scoped BigOperators

attribute [local instance] Fintype.ofFinite

variable {G : Type*} [Group G] [Finite G]

@[expose] noncomputable def classSet (c : ConjClasses G) : Finset G :=
  letI : DecidableEq (ConjClasses G) := Classical.decEq (ConjClasses G)
  Finset.univ.filter fun g : G => ConjClasses.mk g = c

lemma mem_classSet_iff {c : ConjClasses G} {g : G} :
    g ∈ classSet (G := G) c ↔ ConjClasses.mk g = c := by
  classical
  simp [classSet]

@[expose] noncomputable def classSumComplex (c : ConjClasses G) : MonoidAlgebra ℂ G :=
  ∑ g ∈ classSet (G := G) c, MonoidAlgebra.single g (1 : ℂ)

private lemma classSumComplex_coeff [DecidableEq (ConjClasses G)] (c : ConjClasses G) (x : G) :
    (classSumComplex (G := G) c).coeff x =
      if ConjClasses.mk x = c then 1 else 0 := by
  rw [classSumComplex]
  simp only [MonoidAlgebra.coeff_sum, MonoidAlgebra.coeff_single]
  rw [Finset.sum_apply']
  by_cases hx : ConjClasses.mk x = c
  · rw [ite_eq_left hx]
    have hxmem : x ∈ classSet (G := G) c := (mem_classSet_iff (G := G)).2 hx
    rw [Finset.sum_eq_single x]
    · simp
    · intro y hy hyx
      simp [hyx]
    · intro hxnot
      exact False.elim (hxnot hxmem)
  · rw [ite_eq_right hx]
    refine Finset.sum_eq_zero ?_
    intro y hy
    have hyx : y ≠ x := by
      intro hyx
      apply hx
      simpa [hyx] using (mem_classSet_iff (G := G)).1 hy
    simp [hyx]

lemma classSumComplex_comm (c : ConjClasses G) (a : MonoidAlgebra ℂ G) :
    a * classSumComplex (G := G) c =
      classSumComplex (G := G) c * a := by
  classical
  induction a using MonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy => simp [add_mul, mul_add, hx, hy]
  | single g r =>
      ext x
      have hconj :
          ConjClasses.mk (g⁻¹ * x) = ConjClasses.mk (x * g⁻¹) := by
        rw [ConjClasses.mk_eq_mk_iff_isConj, isConj_iff]
        exact ⟨g, by group⟩
      simp only [MonoidAlgebra.coeff_single_mul_apply, MonoidAlgebra.coeff_mul_single_apply,
        classSumComplex_coeff]
      rw [hconj, mul_comm]

end

end Theory.Character

end CFSG
