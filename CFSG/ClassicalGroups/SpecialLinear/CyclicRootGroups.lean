module

public import Mathlib.LinearAlgebra.Matrix.ElementaryRowOperations

public section

namespace CFSG.ClassicalGroups.SpecialLinear

open Matrix
open scoped commutatorElement

section Steinberg

variable {ι R : Type*} [DecidableEq ι] [Fintype ι] [CommRing R]

theorem steinberg_commutator {i j k : ι} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) (a b : R) :
    ⁅SpecialLinearGroup.transvection hij a, SpecialLinearGroup.transvection hjk b⁆ =
      SpecialLinearGroup.transvection hik (a * b) := by
  rw [commutatorElement_def, SpecialLinearGroup.transvection_inv,
    SpecialLinearGroup.transvection_inv]
  refine Subtype.ext ?_
  simp [SpecialLinearGroup.transvection_coe, mul_add, add_mul, hij, hjk, hik, hij.symm, hjk.symm,
    hik.symm, ← single_neg]
  abel

theorem transvection_mem_of_steinberg {H : Subgroup (SpecialLinearGroup ι R)} {i j k : ι}
    (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k)
    (h₁ : ∀ a : R, SpecialLinearGroup.transvection hij a ∈ H)
    (h₂ : SpecialLinearGroup.transvection hjk (1 : R) ∈ H) (a : R) :
    SpecialLinearGroup.transvection hik a ∈ H := by
  have h := steinberg_commutator hij hjk hik a 1
  rw [mul_one] at h
  rw [← h, commutatorElement_def]
  exact H.mul_mem (H.mul_mem (H.mul_mem (h₁ a) h₂) (H.inv_mem (h₁ a))) (H.inv_mem h₂)

end Steinberg

section Generation

variable {ι K : Type*} [DecidableEq ι] [Fintype ι] [Field K]

theorem diag2n_eq_transvection_prod {i j : ι} (hij : i ≠ j) {c : K} (hc : c ≠ 0) :
    SpecialLinearGroup.diag2n hij c hc =
      SpecialLinearGroup.transvection hij (1 : K) *
        SpecialLinearGroup.transvection hij.symm (c - 1) *
        SpecialLinearGroup.transvection hij (-c⁻¹) *
        SpecialLinearGroup.transvection hij.symm (c - c ^ 2) := by
  refine Subtype.ext ?_
  rw [SpecialLinearGroup.diag2n_coe]
  simp only [SpecialLinearGroup.coe_mul, SpecialLinearGroup.transvection_coe]
  simp [mul_add, add_mul, hij, hij.symm]
  ext p q
  simp only [Matrix.add_apply, Matrix.one_apply, Matrix.single_apply, Matrix.diagonal_apply]
  grind

theorem eq_top_of_forall_transvection_mem [Nontrivial ι] (H : Subgroup (SpecialLinearGroup ι K))
    (h : ∀ (i j : ι) (hij : i ≠ j) (c : K), SpecialLinearGroup.transvection hij c ∈ H) :
    H = ⊤ := by
  refine top_unique fun g _ => ?_
  refine SpecialLinearGroup.diagonal_transvection_induction' (fun g => g ∈ H) g ?_ h
    (fun _ _ => H.mul_mem)
  intro i j hij c hc
  rw [diag2n_eq_transvection_prod hij hc]
  exact H.mul_mem (H.mul_mem (H.mul_mem (h _ _ _ _) (h _ _ _ _)) (h _ _ _ _)) (h _ _ _ _)

theorem closure_transvection_eq_top [Nontrivial ι] :
    Subgroup.closure {g : SpecialLinearGroup ι K |
      ∃ (i j : ι) (hij : i ≠ j) (c : K), g = SpecialLinearGroup.transvection hij c} = ⊤ :=
  eq_top_of_forall_transvection_mem _ fun i j hij c =>
    Subgroup.subset_closure ⟨i, j, hij, c, rfl⟩

end Generation

section Cyclic

theorem finRotate_ne_self {m : ℕ} (hm : 2 ≤ m) (i : Fin m) : i ≠ finRotate m i := by
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 2 := ⟨m - 2, by omega⟩
  rw [finRotate_apply]
  simp

private theorem transvection_mem_of_cyclic_aux {n : ℕ} {K : Type*} [Field K]
    (hrot : ∀ i : Fin (n + 2), i ≠ finRotate (n + 2) i)
    {H : Subgroup (SpecialLinearGroup (Fin (n + 2)) K)}
    (hgen : ∀ (i : Fin (n + 2)) (c : K), SpecialLinearGroup.transvection (hrot i) c ∈ H)
    (k : Fin (n + 2)) :
    k ≠ 0 → ∀ (i j : Fin (n + 2)), j = i + k → ∀ (hij : i ≠ j) (c : K),
      SpecialLinearGroup.transvection hij c ∈ H := by
  induction k using Fin.induction with
  | zero => intro h; exact absurd rfl h
  | succ k ih =>
    intro _ i j hj hij c
    have hs : (k.succ : Fin (n + 2)) = k.castSucc + 1 := Fin.coeSucc_eq_succ.symm
    by_cases hk0 : k = 0
    · subst hk0
      have hj' : j = finRotate (n + 2) i := by
        rw [hj, finRotate_apply, hs]
        simp
      subst hj'
      exact hgen i c
    · have hk' : k.castSucc ≠ 0 := by simpa using hk0
      obtain ⟨l, hl⟩ : ∃ l, l = i + k.castSucc := ⟨_, rfl⟩
      have hil : i ≠ l := by
        intro h
        apply hk'
        simpa [hl] using h
      have hlj : j = finRotate (n + 2) l := by
        rw [hj, finRotate_apply, hl, hs]
        exact (add_assoc _ _ _).symm
      subst hlj
      exact transvection_mem_of_steinberg hil (hrot l) hij (fun a => ih hk' i l hl hil a)
        (hgen l 1) c

theorem transvection_mem_of_cyclic_mem {m : ℕ} (hm : 2 ≤ m) {K : Type*} [Field K]
    (hrot : ∀ i : Fin m, i ≠ finRotate m i) {H : Subgroup (SpecialLinearGroup (Fin m) K)}
    (hgen : ∀ (i : Fin m) (c : K), SpecialLinearGroup.transvection (hrot i) c ∈ H)
    {i j : Fin m} (hij : i ≠ j) (c : K) : SpecialLinearGroup.transvection hij c ∈ H := by
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 2 := ⟨m - 2, by omega⟩
  exact transvection_mem_of_cyclic_aux hrot hgen (j - i) (sub_ne_zero.2 hij.symm) i j
    (by simp) hij c

theorem eq_top_of_cyclic_transvection_mem {m : ℕ} (hm : 2 ≤ m) {K : Type*} [Field K]
    (hrot : ∀ i : Fin m, i ≠ finRotate m i) {H : Subgroup (SpecialLinearGroup (Fin m) K)}
    (hgen : ∀ (i : Fin m) (c : K), SpecialLinearGroup.transvection (hrot i) c ∈ H) : H = ⊤ := by
  have : Nontrivial (Fin m) := Fin.nontrivial_iff_two_le.2 hm
  exact eq_top_of_forall_transvection_mem H fun i j hij c =>
    transvection_mem_of_cyclic_mem hm hrot hgen hij c

theorem closure_cyclic_transvections {m : ℕ} (hm : 2 ≤ m) (K : Type*) [Field K]
    (hrot : ∀ i : Fin m, i ≠ finRotate m i) :
    Subgroup.closure {g : Matrix.SpecialLinearGroup (Fin m) K |
        ∃ (i : Fin m) (c : K), g = Matrix.SpecialLinearGroup.transvection (hrot i) c} = ⊤ :=
  eq_top_of_cyclic_transvection_mem hm hrot fun i c => Subgroup.subset_closure ⟨i, c, rfl⟩

end Cyclic

section RootGroups

variable {ι : Type*} [DecidableEq ι] [Fintype ι] (K : Type*) [CommRing K] {i j : ι}

@[expose] def rootHom (hij : i ≠ j) : Multiplicative K →* SpecialLinearGroup ι K where
  toFun c := SpecialLinearGroup.transvection hij c.toAdd
  map_one' := SpecialLinearGroup.transvection_coeff_zero hij
  map_mul' a b := SpecialLinearGroup.transvection_add hij a.toAdd b.toAdd

@[expose] def rootGroup (hij : i ≠ j) : Subgroup (SpecialLinearGroup ι K) :=
  (rootHom K hij).range

variable {K}

theorem mem_rootGroup {hij : i ≠ j} {g : SpecialLinearGroup ι K} :
    g ∈ rootGroup K hij ↔ ∃ c : K, SpecialLinearGroup.transvection hij c = g := by
  constructor
  · rintro ⟨c, rfl⟩
    exact ⟨c.toAdd, rfl⟩
  · rintro ⟨c, rfl⟩
    exact ⟨Multiplicative.ofAdd c, rfl⟩

theorem transvection_mem_rootGroup (hij : i ≠ j) (c : K) :
    SpecialLinearGroup.transvection hij c ∈ rootGroup K hij :=
  mem_rootGroup.2 ⟨c, rfl⟩

theorem rootHom_injective (hij : i ≠ j) : Function.Injective (rootHom K hij) := by
  intro a b h
  have := congrArg (fun g : SpecialLinearGroup ι K => (g : Matrix ι ι K) i j) h
  simpa [rootHom, SpecialLinearGroup.transvection_coe] using this

end RootGroups

section CyclicRootGroups

theorem closure_cyclic_transvections_GL {m : ℕ} (hm : 2 ≤ m) (K : Type*) [Field K]
    (hrot : ∀ i : Fin m, i ≠ finRotate m i) :
    Subgroup.closure {g : Matrix.GeneralLinearGroup (Fin m) K | ∃ (i : Fin m) (c : K),
        g = Matrix.GeneralLinearGroup.transvection i (finRotate m i) (hrot i) c} =
      Subgroup.closure {A : Matrix.GeneralLinearGroup (Fin m) K |
        (A : Matrix (Fin m) (Fin m) K).det = 1} := by
  have hS : {g : Matrix.GeneralLinearGroup (Fin m) K | ∃ (i : Fin m) (c : K),
        g = Matrix.GeneralLinearGroup.transvection i (finRotate m i) (hrot i) c} =
      SpecialLinearGroup.toGL '' {g : Matrix.SpecialLinearGroup (Fin m) K |
        ∃ (i : Fin m) (c : K), g = Matrix.SpecialLinearGroup.transvection (hrot i) c} := by
    ext g
    constructor
    · rintro ⟨i, c, rfl⟩
      exact ⟨_, ⟨i, c, rfl⟩, Units.ext rfl⟩
    · rintro ⟨_, ⟨i, c, rfl⟩, rfl⟩
      exact ⟨i, c, Units.ext rfl⟩
  have hdet : {A : Matrix.GeneralLinearGroup (Fin m) K |
        (A : Matrix (Fin m) (Fin m) K).det = 1} =
      ((Matrix.GeneralLinearGroup.det : Matrix.GeneralLinearGroup (Fin m) K →* Kˣ).ker :
        Set (Matrix.GeneralLinearGroup (Fin m) K)) := by
    ext A
    simp [Units.ext_iff]
  rw [hS, ← MonoidHom.map_closure, closure_cyclic_transvections hm K hrot,
    ← MonoidHom.range_eq_map, SpecialLinearGroup.range_toGL_eq_ker_det, hdet,
    Subgroup.closure_eq]

end CyclicRootGroups

end CFSG.ClassicalGroups.SpecialLinear
