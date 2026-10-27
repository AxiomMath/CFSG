module

public import CFSG.HardMathSupport.Solomon.Coordinator.LayerCentralFix
public import CFSG.RankThree.SteinbergR3ECALinearPrimaryBlocks
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBGeneralLinearSmall

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple

open Polynomial Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.ComponentClassification
open CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCUnitary
open CFSG.RankThree.CALinearPrimary

variable {n : ℕ} {k : Type*} [Field k]

noncomputable abbrev glA (A : GL (Fin n) k) : LinearMap.GeneralLinearGroup k (Fin n → k) :=
  Matrix.GeneralLinearGroup.toLin A

@[expose] def IsGoodFactor (A : GL (Fin n) k) (h : k[X]) : Prop :=
  3 ≤ primaryMultiplicity (glA A : Module.End k (Fin n → k)) h ∨
    (2 ≤ primaryMultiplicity (glA A : Module.End k (Fin n → k)) h ∧ 4 ≤ Nat.card (AdjoinRoot h))

@[expose] noncomputable def specialFactor (A : GL (Fin n) k) (h : k[X]) :
    Subgroup (SpecialLinearGroup (Fin n) k) :=
  (linearSpecialBlock (glA A) h).comap (slGL n k)

theorem squarefree_minpoly_glA {p : ℕ} (hpk : (p : k) ≠ 0) {A : GL (Fin n) k} {c : kˣ}
    (hA : A ^ p = Matrix.GeneralLinearGroup.scalar (Fin n) c) :
    Squarefree (minpoly k (glA A : Module.End k (Fin n → k))) := by
  refine squarefree_minpoly_of_aeval_eq_zero (p := X ^ p - C (c : k))
    (Polynomial.separable_X_pow_sub_C (c : k) hpk c.ne_zero).squarefree ?_
  have h1 : ((glA A : LinearMap.GeneralLinearGroup k (Fin n → k)) : Module.End k (Fin n → k)) =
      Matrix.toLin' (A : Matrix (Fin n) (Fin n) k) := rfl
  rw [map_sub, map_pow, aeval_X, aeval_C, h1, ← Matrix.toLin'_pow, ← Units.val_pow_eq_pow_val, hA]
  ext v i
  by_cases hi : i = v <;> simp [hi]

theorem mem_fixSubgroup_slConjugation_iff {A : GL (Fin n) k} {g : SpecialLinearGroup (Fin n) k} :
    g ∈ fixSubgroup (CatalogueBHigherLinearAction.slConjugation n k A) ↔
      slGL n k g ∈ gl_centralizer (glA A) := by
  rw [mem_fixSubgroup, mem_gl_centralizer, commute_iff_eq]
  have e1 : ((slGL n k g : LinearMap.GeneralLinearGroup k (Fin n → k)) :
      Module.End k (Fin n → k)) * ((glA A : LinearMap.GeneralLinearGroup k (Fin n → k)) :
        Module.End k (Fin n → k)) =
      Matrix.toLin' ((g : Matrix (Fin n) (Fin n) k) * (A : Matrix (Fin n) (Fin n) k)) := by
    rw [Matrix.toLin'_mul]
    rfl
  have e2 : ((glA A : LinearMap.GeneralLinearGroup k (Fin n → k)) : Module.End k (Fin n → k)) *
      ((slGL n k g : LinearMap.GeneralLinearGroup k (Fin n → k)) : Module.End k (Fin n → k)) =
      Matrix.toLin' ((A : Matrix (Fin n) (Fin n) k) * (g : Matrix (Fin n) (Fin n) k)) := by
    rw [Matrix.toLin'_mul]
    rfl
  rw [e1, e2, EmbeddingLike.apply_eq_iff_eq]
  constructor
  · intro h1
    have h2 : ((CatalogueBHigherLinearAction.slConjugation n k A g :
        SpecialLinearGroup (Fin n) k) : Matrix (Fin n) (Fin n) k) = g := congrArg Subtype.val h1
    rw [LinearFlag.coe_slConjugation, Units.mul_inv_eq_iff_eq_mul] at h2
    exact h2.symm
  · intro h1
    apply Subtype.ext
    rw [LinearFlag.coe_slConjugation, Units.mul_inv_eq_iff_eq_mul]
    exact h1.symm

theorem specialFactor_le_fixSubgroup (A : GL (Fin n) k) (h : k[X]) :
    specialFactor A h ≤ fixSubgroup (CatalogueBHigherLinearAction.slConjugation n k A) := by
  intro g hg
  rw [mem_fixSubgroup_slConjugation_iff]
  exact linearSpecialBlock_le_centralizer _ _ hg

theorem conj_mem_specialFactor {A : GL (Fin n) k} {h : k[X]} {c g : SpecialLinearGroup (Fin n) k}
    (hc : c ∈ fixSubgroup (CatalogueBHigherLinearAction.slConjugation n k A))
    (hg : g ∈ specialFactor A h) : c * g * c⁻¹ ∈ specialFactor A h := by
  have hc' : slGL n k c ∈ gl_centralizer (glA A) := mem_fixSubgroup_slConjugation_iff.mp hc
  rw [specialFactor, Subgroup.mem_comap, map_mul, map_mul, map_inv]
  exact conj_mem_linearSpecialBlock hc' hg

variable [Finite k]

theorem isQuasisimple_specialFactor {A : GL (Fin n) k}
    (hsq : Squarefree (minpoly k (glA A : Module.End k (Fin n → k)))) {h : k[X]}
    (hh : h ∈ primaryFactors (glA A : Module.End k (Fin n → k))) (hgood : IsGoodFactor A h) :
    CFSG.IsQuasisimple (specialFactor A h) := by
  have hle : linearSpecialBlock (glA A) h ≤ (slGL n k).range := fun _ hg =>
    mem_range_slGL (det_eq_one_of_mem_linearSpecialBlock hsq hh hg)
  have hmap : (specialFactor A h).map (slGL n k) = linearSpecialBlock (glA A) h := by
    rw [specialFactor, Subgroup.map_comap_eq, inf_eq_right]
    exact hle
  exact CFSG.LocalCores.isQuasisimple_of_mulEquiv
    ((Subgroup.equivMapOfInjective _ (slGL n k) slGL_injective).trans
      (MulEquiv.subgroupCongr hmap)).symm
    (isQuasisimple_linearSpecialBlock hsq hh hgood)

private theorem isSolvable_generalLinearGroup_of_small {E W : Type*} [Field E] [Finite E]
    [AddCommGroup W] [Module E W] [Module.Finite E W]
    (h : Module.finrank E W ≤ 1 ∨ (Module.finrank E W = 2 ∧ Nat.card E ≤ 3)) :
    Group.IsSolvable (LinearMap.GeneralLinearGroup E W) := by
  obtain ⟨m, hm⟩ : ∃ m, Module.finrank E W = m := ⟨_, rfl⟩
  let b : Module.Basis (Fin m) E W := Module.finBasisOfFinrankEq E W hm
  obtain ⟨e⟩ : Nonempty (LinearMap.GeneralLinearGroup E W ≃* Matrix.GeneralLinearGroup (Fin m) E) :=
    ⟨(LinearMap.GeneralLinearGroup.congrLinearEquiv b.equivFun).trans
      Matrix.GeneralLinearGroup.toLin.symm⟩
  have hsolv : Group.IsSolvable (Matrix.GeneralLinearGroup (Fin m) E) := by
    rw [hm] at h
    rcases h with h | ⟨rfl, h3⟩
    · rcases Nat.le_one_iff_eq_zero_or_eq_one.mp h with rfl | rfl
      · exact Group.isSolvable_of_comm fun u v => Units.ext (Subsingleton.elim _ _)
      · exact CFSG.ComponentClassification.CatalogueBGeneralLinear.generalLinear_one_solvable E
    · exact CFSG.ComponentClassification.CatalogueBGeneralLinear.generalLinear_two_small_solvable E
        (by have : 2 ≤ Nat.card E := Finite.one_lt_card; omega)
  exact Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective

theorem isSolvable_blockGL_of_not_good {A : GL (Fin n) k} {h : k[X]}
    (hh : h ∈ primaryFactors (glA A : Module.End k (Fin n → k))) (hbad : ¬ IsGoodFactor A h) :
    Group.IsSolvable (blockGL (glA A : Module.End k (Fin n → k)) h) := by
  have : Fact (Irreducible h) := ⟨irreducible_of_mem_primaryFactors hh⟩
  have : Finite (AdjoinRoot h) := Module.finite_of_finite k
  refine isSolvable_generalLinearGroup_of_small ?_
  unfold IsGoodFactor at hbad
  change primaryMultiplicity (glA A : Module.End k (Fin n → k)) h ≤ 1 ∨
    (primaryMultiplicity (glA A : Module.End k (Fin n → k)) h = 2 ∧ Nat.card (AdjoinRoot h) ≤ 3)
  omega

end CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
