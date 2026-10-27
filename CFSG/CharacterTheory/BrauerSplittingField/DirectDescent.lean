module

public import CFSG.CharacterTheory.BrauerSplittingField.Descent
public import Mathlib.Algebra.Module.StablyFree.Basic
public import Mathlib.Algebra.MvPolynomial.Funext
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.TensorProduct.IsBaseChangeHom

public section

namespace CFSG

open scoped TensorProduct BigOperators

namespace BrauerSplittingField.Helpers

noncomputable section

universe u v

private lemma exists_eval_comp_ne_zero
    {K C ι : Type*} [Field K] [Field C] [Infinite K]
    (φ : K →+* C) {p : MvPolynomial ι C} (hp : p ≠ 0) :
    ∃ d : ι → K, MvPolynomial.eval (φ ∘ d) p ≠ 0 := by
  by_contra h
  simp only [not_exists, not_ne_iff] at h
  apply hp
  apply MvPolynomial.funext_set (fun _ ↦ Set.range φ)
    (fun _ ↦ Set.infinite_range_of_injective φ.injective)
  intro x hx
  choose d hd using fun i ↦ hx i (Set.mem_univ i)
  have hxd : x = φ ∘ d := funext fun i ↦ (hd i).symm
  subst x
  simpa using h d

private lemma exists_injective_eval_combination
    {K L ι V W : Type*}
    [Field K] [Field L] [Infinite K] [Fintype ι]
    [AddCommGroup V] [Module L V] [FiniteDimensional L V]
    [AddCommGroup W] [Module L W]
    (φ : K →+* L) (F : ι → V →ₗ[L] W) (c : ι → L)
    (hc : Function.Injective ⇑(∑ i, c i • F i)) :
    ∃ d : ι → K, Function.Injective ⇑(∑ i, φ (d i) • F i) := by
  let T : V →ₗ[L] W := ∑ i, c i • F i
  obtain ⟨l, hl⟩ := LinearMap.exists_leftInverse_of_injective T
    (LinearMap.ker_eq_bot.mpr hc)
  let b := Module.finBasis L V
  let A : Matrix (Fin (Module.finrank L V)) (Fin (Module.finrank L V))
      (MvPolynomial ι L) :=
    ∑ i, (MvPolynomial.X i : MvPolynomial ι L) •
      ((LinearMap.toMatrix b b) (l.comp (F i))).map MvPolynomial.C
  let p : MvPolynomial ι L := A.det
  have hA (d : ι → L) :
      (MvPolynomial.eval d).mapMatrix A =
        (LinearMap.toMatrix b b) (l.comp (∑ i, d i • F i)) := by
    ext r s
    simp only [A, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.sum_apply,
      Matrix.smul_apply, Finset.sum_apply', Finsupp.smul_apply, map_mul,
      MvPolynomial.eval_X, MvPolynomial.eval_C,
      LinearMap.toMatrix_apply, LinearMap.comp_apply, map_sum, LinearMap.sum_apply,
      LinearMap.smul_apply, map_smul, smul_eq_mul]
  have hp_eval : MvPolynomial.eval c p = 1 := by
    dsimp only [p]
    rw [RingHom.map_det, hA]
    rw [LinearMap.det_toMatrix b]
    change LinearMap.det (l.comp T) = 1
    rw [hl, LinearMap.det_id]
  have hp : p ≠ 0 := by
    intro hp
    rw [hp, map_zero] at hp_eval
    exact zero_ne_one hp_eval
  obtain ⟨d, hd⟩ := exists_eval_comp_ne_zero φ hp
  refine ⟨d, ?_⟩
  let S : V →ₗ[L] W := ∑ i, φ (d i) • F i
  have hdet : LinearMap.det (l.comp S) ≠ 0 := by
    dsimp only [S]
    have hAφ :
        (MvPolynomial.eval (φ ∘ d)).mapMatrix A =
          (LinearMap.toMatrix b b) (l.comp (∑ i, φ (d i) • F i)) := by
      simpa only [Function.comp_apply] using hA (φ ∘ d)
    rw [← LinearMap.det_toMatrix b, ← hAφ, ← RingHom.map_det]
    exact hd
  have hker : (l.comp S).ker = ⊥ := by
    by_contra h
    exact hdet (LinearMap.det_eq_zero_iff_ker_ne_bot.mpr h)
  intro x y hxy
  apply LinearMap.ker_eq_bot.mp hker
  exact congrArg l hxy

private def averagedIntertwiningMapLinear
    {K G N P : Type u}
    [CommRing K] [Group G] [Fintype G]
    [AddCommGroup N] [Module K N]
    [AddCommGroup P] [Module K P]
    (ρ : Representation K G N) (σ : Representation K G P) :
    (N →ₗ[K] P) →ₗ[K] ρ.IntertwiningMap σ where
  toFun f := averagedIntertwiningMap ρ σ f
  map_add' f f' := by
    ext x
    change averagedIntertwiningMap ρ σ (f + f') x =
      averagedIntertwiningMap ρ σ f x + averagedIntertwiningMap ρ σ f' x
    simp [averagedIntertwiningMap_apply, Finset.sum_add_distrib]
  map_smul' r f := by
    ext x
    change averagedIntertwiningMap ρ σ (r • f) x =
      r • averagedIntertwiningMap ρ σ f x
    simp [averagedIntertwiningMap_apply, Finset.smul_sum]

private lemma averagedIntertwiningMap_sum_smul
    {K G N P : Type u} {ι : Type v}
    [CommRing K] [Group G] [Fintype G] [Fintype ι]
    [AddCommGroup N] [Module K N]
    [AddCommGroup P] [Module K P]
    (ρ : Representation K G N) (σ : Representation K G P)
    (c : ι → K) (f : ι → N →ₗ[K] P) :
    averagedIntertwiningMap ρ σ (∑ i, c i • f i) =
      ∑ i, c i • averagedIntertwiningMap ρ σ (f i) := by
  change averagedIntertwiningMapLinear ρ σ (∑ i, c i • f i) =
    ∑ i, c i • averagedIntertwiningMapLinear ρ σ (f i)
  simp

private lemma canonical_linearMapLeftRightHom_eq_baseChange
    {K L N P : Type*}
    [CommSemiring K] [CommSemiring L] [Algebra K L]
    [AddCommMonoid N] [Module K N]
    [AddCommMonoid P] [Module K P]
    (f : N →ₗ[K] P) :
    IsBaseChange.linearMapLeftRightHom (TensorProduct.isBaseChange K N L)
        (TensorProduct.mk K L P 1) f = f.baseChange L := by
  apply (TensorProduct.isBaseChange K N L).algHom_ext
  intro x
  rw [IsBaseChange.linearMapLeftRightHom_comp_apply]
  change (1 ⊗ₜ[K] f x) = f.baseChange L (1 ⊗ₜ[K] x)
  rw [LinearMap.baseChange_tmul]

private lemma exists_baseChange_linear_decomposition
    {K L N P : Type u}
    [Field K] [Field L] [Algebra K L]
    [AddCommGroup N] [Module K N] [FiniteDimensional K N]
    [AddCommGroup P] [Module K P]
    (j : (L ⊗[K] N) →ₗ[L] (L ⊗[K] P)) :
    ∃ (k : ℕ) (c : Fin k → L) (f : Fin k → N →ₗ[K] P),
      j = ∑ i, c i • (f i).baseChange L := by
  let hN : IsBaseChange L (TensorProduct.mk K L N 1) :=
    TensorProduct.isBaseChange K N L
  let hP : IsBaseChange L (TensorProduct.mk K L P 1) :=
    TensorProduct.isBaseChange K P L
  let bcHom : (N →ₗ[K] P) →ₗ[K] ((L ⊗[K] N) →ₗ[L] (L ⊗[K] P)) :=
    IsBaseChange.linearMapLeftRightHom hN (TensorProduct.mk K L P 1)
  have hbc : IsBaseChange L bcHom := by
    exact IsBaseChange.linearMapLeftRight hN hP
  obtain ⟨k, c, f, hf⟩ :=
    TensorProduct.exists_sum_tmul_eq (hbc.equiv.symm j)
  refine ⟨k, c, f, ?_⟩
  calc
    j = hbc.equiv (hbc.equiv.symm j) := (hbc.equiv.apply_symm_apply j).symm
    _ = hbc.equiv (∑ i, c i ⊗ₜ[K] f i) := congrArg hbc.equiv hf
    _ = ∑ i, c i • bcHom (f i) := by
      simp only [map_sum, IsBaseChange.equiv_tmul]
    _ = ∑ i, c i • (f i).baseChange L := by
      apply Finset.sum_congr rfl
      intro i _
      rw [canonical_linearMapLeftRightHom_eq_baseChange]

private lemma injective_averaged_baseChange_combination
    {K L G N P : Type u}
    [Field K] [Field L] [Algebra K L] [CharZero L]
    [Group G] [Fintype G]
    [AddCommGroup N] [Module K N]
    [AddCommGroup P] [Module K P]
    (ρ : Representation K G N) (σ : Representation K G P)
    (j : (baseChangeRep (A := L) ρ).IntertwiningMap
      (baseChangeRep (A := L) σ))
    (hj : Function.Injective j)
    {k : ℕ} (c : Fin k → L) (f : Fin k → N →ₗ[K] P)
    (hdecomp : j.toLinearMap = ∑ i, c i • (f i).baseChange L) :
    Function.Injective ⇑(∑ i, c i •
      (averagedIntertwiningMap ρ σ (f i)).toLinearMap.baseChange L) := by
  have hcombo :
      (∑ i, c i •
        (averagedIntertwiningMap ρ σ (f i)).toLinearMap.baseChange L) =
        (Fintype.card G : L) • j.toLinearMap := by
    calc
      (∑ i, c i •
          (averagedIntertwiningMap ρ σ (f i)).toLinearMap.baseChange L) =
          ∑ i, c i •
            (averagedIntertwiningMap (baseChangeRep (A := L) ρ)
              (baseChangeRep (A := L) σ) ((f i).baseChange L)).toLinearMap := by
            apply Finset.sum_congr rfl
            intro i _
            rw [averagedIntertwiningMap_baseChange]
      _ = (∑ i, c i •
            averagedIntertwiningMap (baseChangeRep (A := L) ρ)
              (baseChangeRep (A := L) σ) ((f i).baseChange L)).toLinearMap := by
            ext x
            simp [Representation.IntertwiningMap.sum_apply]
      _ = (averagedIntertwiningMap (baseChangeRep (A := L) ρ)
            (baseChangeRep (A := L) σ)
            (∑ i, c i • (f i).baseChange L)).toLinearMap := by
            exact congrArg
              (fun q : (baseChangeRep (A := L) ρ).IntertwiningMap
                (baseChangeRep (A := L) σ) ↦ q.toLinearMap)
              (averagedIntertwiningMap_sum_smul
                (ι := Fin k)
                (baseChangeRep (A := L) ρ) (baseChangeRep (A := L) σ)
                c (fun i : Fin k ↦ (f i).baseChange L)).symm
      _ = (averagedIntertwiningMap (baseChangeRep (A := L) ρ)
            (baseChangeRep (A := L) σ) j.toLinearMap).toLinearMap := by
            rw [hdecomp]
      _ = ((Fintype.card G : L) • j).toLinearMap := by
            rw [averagedIntertwiningMap_of_intertwining]
      _ = (Fintype.card G : L) • j.toLinearMap := rfl
  rw [hcombo]
  intro x y hxy
  apply hj
  have hcard : (Fintype.card G : L) ≠ 0 :=
    Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  exact smul_right_injective (L ⊗[K] P) hcard hxy

theorem exists_injective_intertwiningMap_of_baseChange
    {K L G N P : Type u}
    [Field K] [Field L] [Algebra K L] [Infinite K] [CharZero L]
    [Group G] [Fintype G]
    [AddCommGroup N] [Module K N] [FiniteDimensional K N]
    [AddCommGroup P] [Module K P]
    (ρ : Representation K G N) (σ : Representation K G P)
    (j : (baseChangeRep (A := L) ρ).IntertwiningMap
      (baseChangeRep (A := L) σ))
    (hj : Function.Injective j) :
    ∃ q : ρ.IntertwiningMap σ, Function.Injective q := by
  obtain ⟨k, c, f, hdecomp⟩ :=
    exists_baseChange_linear_decomposition j.toLinearMap
  let a : Fin k → ρ.IntertwiningMap σ :=
    fun i ↦ averagedIntertwiningMap ρ σ (f i)
  have hc : Function.Injective ⇑(∑ i, c i •
      (a i).toLinearMap.baseChange L) := by
    exact injective_averaged_baseChange_combination ρ σ j hj c f hdecomp
  obtain ⟨d, hd⟩ := exists_injective_eval_combination
    (algebraMap K L) (fun i ↦ (a i).toLinearMap.baseChange L) c hc
  let q : ρ.IntertwiningMap σ := ∑ i, d i • a i
  refine ⟨q, ?_⟩
  have hq : q.toLinearMap = ∑ i, d i • (a i).toLinearMap := by
    ext x
    simp [q, Representation.IntertwiningMap.sum_apply]
  have hqbc : q.toLinearMap.baseChange L =
      ∑ i, algebraMap K L (d i) • (a i).toLinearMap.baseChange L := by
    rw [hq]
    change LinearMap.baseChangeHom K L N P
      (∑ i, d i • (a i).toLinearMap) = _
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [map_smul]
    ext x
    simp
  intro x y hxy
  apply Module.Flat.tensorProduct_mk_injective K N L
  apply hd
  rw [← hqbc]
  exact congrArg (fun z ↦ (1 : L) ⊗ₜ[K] z) hxy

end

end BrauerSplittingField.Helpers

end CFSG
