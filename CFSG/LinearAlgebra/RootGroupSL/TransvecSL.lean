module

public import Mathlib.LinearAlgebra.SpecialLinearGroup
public import Mathlib.LinearAlgebra.Transvection.Basic
public import CFSG.ClassicalGroups.SpecialLinear.CyclicRootGroups

public section

namespace CFSG.LinearAlgebra.RootGroupSL

open scoped commutatorElement

variable {k V : Type} [Field k] [AddCommGroup V] [Module k V] [Module.Finite k V]

open scoped Classical in
@[expose] noncomputable def transvecSL (w : V) (f : Module.Dual k V) : SpecialLinearGroup k V :=
  if h : f w = 0 then ⟨LinearEquiv.transvection h, LinearEquiv.transvection.det_eq_one h⟩ else 1

private lemma add_self_eq_zero_module [CharP k 2] (y : V) : y + y = 0 := by
  have h2 : ((2 : ℕ) : k) = 0 := CharP.cast_eq_zero k 2
  calc y + y = (2 : k) • y := (two_smul k y).symm
    _ = ((2 : ℕ) : k) • y := by rw [← Nat.cast_ofNat (R := k)]
    _ = 0 := by rw [h2, zero_smul]

theorem transvecSL_apply {w : V} {f : Module.Dual k V} (h : f w = 0) (x : V) :
    transvecSL w f x = x + f x • w := by
  simp only [transvecSL, dif_pos h]
  exact LinearEquiv.transvection.apply h x

private lemma transvecSL_mul_self [CharP k 2] {w : V} {f : Module.Dual k V} (h : f w = 0) :
    transvecSL w f * transvecSL w f = 1 := by
  apply SpecialLinearGroup.ext
  intro x
  change transvecSL w f (transvecSL w f x) = x
  rw [transvecSL_apply h, transvecSL_apply h]
  rw [map_add, map_smul, smul_eq_mul, h, mul_zero, add_zero]
  rw [add_assoc, add_self_eq_zero_module (k := k) (f x • w), add_zero]

theorem transvecSL_conj (g : SpecialLinearGroup k V) {w : V} {f : Module.Dual k V}
    (h : f w = 0) :
    g * transvecSL w f * g⁻¹ =
      transvecSL (g w) (f ∘ₗ (SpecialLinearGroup.toLinearEquiv g⁻¹).toLinearMap) := by
  have h' : (f ∘ₗ (SpecialLinearGroup.toLinearEquiv g⁻¹).toLinearMap) (g w) = 0 := by
    simp [h]
  apply SpecialLinearGroup.ext
  intro x
  change (g : V ≃ₗ[k] V) (transvecSL w f ((g⁻¹ : V ≃ₗ[k] V) x)) =
    transvecSL (g w) (f ∘ₗ (SpecialLinearGroup.toLinearEquiv g⁻¹).toLinearMap) x
  rw [transvecSL_apply h, transvecSL_apply h']
  have hg : (g : V ≃ₗ[k] V) ((g⁻¹ : V ≃ₗ[k] V) x) = x :=
    LinearEquiv.apply_symm_apply (g : V ≃ₗ[k] V) x
  rw [map_add, map_smul, hg]
  rfl

theorem commutator_transvecSL [CharP k 2] {w v : V} {f f' : Module.Dual k V} (hw : f' w = 0)
    (hv : f v = 0) (hfw : f w = 0) (h1 : f' v = 1) :
    ⁅transvecSL w f', transvecSL v f⁆ = transvecSL w f := by
  have hA : transvecSL w f' * transvecSL w f' = 1 := transvecSL_mul_self hw
  have hB : transvecSL v f * transvecSL v f = 1 := transvecSL_mul_self hv
  rw [commutatorElement_def, inv_eq_of_mul_eq_one_left hA, inv_eq_of_mul_eq_one_left hB]
  apply SpecialLinearGroup.ext
  intro x
  change transvecSL w f' (transvecSL v f (transvecSL w f' (transvecSL v f x))) =
    transvecSL w f x
  simp only [transvecSL_apply hw, transvecSL_apply hv, transvecSL_apply hfw]
  have e1 : f' (x + f x • v) = f' x + f x := by
    simp only [map_add, map_smul, smul_eq_mul, h1, mul_one]
  have e2 : f ((x + f x • v) + f' (x + f x • v) • w) = f x := by
    simp only [e1, map_add, map_smul, smul_eq_mul, hfw, mul_zero, add_zero, hv]
  have e3 : f' (((x + f x • v) + f' (x + f x • v) • w) +
      f ((x + f x • v) + f' (x + f x • v) • w) • v) = f' x := by
    simp only [e2, e1, map_add, map_smul, smul_eq_mul, hfw, hw, hv, h1, mul_zero, mul_one,
      add_zero]
    rw [add_assoc, CharTwo.add_self_eq_zero (f x), add_zero]
  rw [e3, e2, e1, add_smul]
  have hrearr : (x + f x • v) + (f' x • w + f x • w) + f x • v + f' x • w =
      x + (f x • v + f x • v) + (f' x • w + f' x • w) + f x • w := by abel
  rw [hrearr, add_self_eq_zero_module (k := k) (f x • v),
    add_self_eq_zero_module (k := k) (f' x • w)]
  simp

private lemma toLin_transvection_apply {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι k V) (i j : ι) (c : k) (v : V) :
    Matrix.toLin b b (Matrix.transvection i j c) v = v + c • (b.coord j v • b i) := by
  have hmv : Matrix.mulVec (Matrix.transvection i j c) ((b.repr v : ι → k)) =
      (b.repr v : ι → k) + (c * b.repr v j) • Pi.single i (1 : k) := by
    rw [Matrix.transvection, Matrix.add_mulVec, Matrix.one_mulVec, Matrix.single_mulVec_eq]
  rw [Matrix.toLin_apply, hmv]
  simp only [Pi.add_apply, add_smul]
  rw [Finset.sum_add_distrib, Module.Basis.sum_repr]
  congr 1
  rw [Finset.sum_eq_single i]
  · simp [smul_smul, Module.Basis.coord_apply]
  · intro j' _ hj'; simp [Pi.single_apply, hj']
  · intro hi; exact absurd (Finset.mem_univ i) hi

private lemma toLin_equiv_transvection {n : ℕ} (b : Module.Basis (Fin n) k V) {i j : Fin n}
    (hij : i ≠ j) (c : k) :
    Matrix.SpecialLinearGroup.toLin_equiv b (Matrix.SpecialLinearGroup.transvection hij c) =
      transvecSL (b i) (c • b.coord j) := by
  have hcond : (c • b.coord j) (b i) = 0 := by
    rw [LinearMap.smul_apply, smul_eq_mul, Module.Basis.coord_apply, Module.Basis.repr_self,
      Finsupp.single_eq_of_ne (Ne.symm hij), mul_zero]
  apply SpecialLinearGroup.ext
  intro x
  rw [transvecSL_apply hcond]
  change Matrix.toLin b b (Matrix.transvection i j c) x = x + (c * b.coord j x) • b i
  rw [toLin_transvection_apply]
  rw [smul_smul]

theorem eq_top_of_transvecSL_mem (H : Subgroup (SpecialLinearGroup k V))
    (h : ∀ (w : V) (f : Module.Dual k V), f w = 0 → transvecSL w f ∈ H) : H = ⊤ := by
  classical
  by_cases hn : Module.finrank k V ≤ 1
  · haveI : Subsingleton (SpecialLinearGroup k V) := by
      rcases (by omega : Module.finrank k V = 0 ∨ Module.finrank k V = 1) with h0 | h1
      · haveI : Subsingleton V := (Module.finrank_eq_zero_iff_of_free (R := k) V).mp h0
        exact ⟨fun a b => Subtype.ext (LinearEquiv.ext fun x => Subsingleton.elim _ _)⟩
      · exact SpecialLinearGroup.subsingleton_of_finrank_eq_one h1
    exact le_antisymm le_top fun x _ => by
      rw [Subsingleton.elim x 1]; exact H.one_mem
  · have hn2 : 2 ≤ Module.finrank k V := by omega
    let b : Module.Basis (Fin (Module.finrank k V)) k V := Module.finBasis k V
    let e : Matrix.SpecialLinearGroup (Fin (Module.finrank k V)) k ≃* SpecialLinearGroup k V :=
      Matrix.SpecialLinearGroup.toLin_equiv b
    haveI : Nontrivial (Fin (Module.finrank k V)) :=
      Fin.nontrivial_iff_two_le.mpr hn2
    have hmap : H.map e.symm.toMonoidHom = ⊤ := by
      apply CFSG.ClassicalGroups.SpecialLinear.eq_top_of_forall_transvection_mem
      intro i j hij c
      rw [Subgroup.mem_map]
      refine ⟨e (Matrix.SpecialLinearGroup.transvection hij c), ?_, ?_⟩
      · rw [toLin_equiv_transvection b hij c]
        exact h (b i) (c • b.coord j) (by
          rw [LinearMap.smul_apply, smul_eq_mul, Module.Basis.coord_apply, Module.Basis.repr_self,
            Finsupp.single_eq_of_ne (Ne.symm hij), mul_zero])
      · simp
    exact Subgroup.map_injective (f := e.symm.toMonoidHom) e.symm.injective
      (hmap.trans (Subgroup.map_top_of_surjective e.symm.toMonoidHom e.symm.surjective).symm)

end CFSG.LinearAlgebra.RootGroupSL
