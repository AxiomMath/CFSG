module

public import CFSG.LieType.RootSystem.Parabolic

public section

namespace CFSG.LieType.RootSystem.Restrict

open CFSG.LieType.RootSystem

variable {I : Type} [Fintype I] [DecidableEq I] {C : Type} [Fintype C] [DecidableEq C]

@[expose] noncomputable def ext (e : C → I) (γ : C → ℤ) : I → ℤ :=
  Function.extend e γ 0

variable {e : C → I} (he : Function.Injective e)

include he in
theorem ext_apply (γ : C → ℤ) (i : C) : ext e γ (e i) = γ i :=
  he.extend_apply γ 0 i

theorem ext_apply_of_notMem_range (γ : C → ℤ) {k : I} (hk : k ∉ Set.range e) :
    ext e γ k = 0 := by
  rw [ext, Function.extend_apply' _ _ _ hk]
  rfl

include he in
theorem ext_injective : Function.Injective (ext e) := by
  intro γ δ h
  funext i
  have := congrFun h (e i)
  rwa [ext_apply he, ext_apply he] at this

include he in
theorem ext_add (γ δ : C → ℤ) : ext e (γ + δ) = ext e γ + ext e δ := by
  funext k
  by_cases hk : k ∈ Set.range e
  · obtain ⟨i, rfl⟩ := hk
    simp [ext_apply he]
  · simp [ext_apply_of_notMem_range _ hk]

include he in
theorem ext_sub (γ δ : C → ℤ) : ext e (γ - δ) = ext e γ - ext e δ := by
  funext k
  by_cases hk : k ∈ Set.range e
  · obtain ⟨i, rfl⟩ := hk
    simp [ext_apply he]
  · simp [ext_apply_of_notMem_range _ hk]

include he in
theorem ext_smul (a : ℤ) (γ : C → ℤ) : ext e (a • γ) = a • ext e γ := by
  funext k
  by_cases hk : k ∈ Set.range e
  · obtain ⟨i, rfl⟩ := hk
    simp [ext_apply he]
  · simp [ext_apply_of_notMem_range _ hk]

include he in
theorem ext_single (i : C) : ext e (Pi.single i 1) = Pi.single (e i) 1 := by
  funext k
  by_cases hk : k ∈ Set.range e
  · obtain ⟨j, rfl⟩ := hk
    rw [ext_apply he, Pi.single_apply, Pi.single_apply]
    simp only [he.eq_iff]
  · rw [ext_apply_of_notMem_range _ hk, Pi.single_apply, if_neg]
    rintro rfl
    exact hk ⟨i, rfl⟩

include he in
theorem sum_ext (γ : C → ℤ) : ∑ k, ext e γ k = ∑ i, γ i :=
  (Fintype.sum_of_injective e he γ (ext e γ) (fun _ hk => ext_apply_of_notMem_range γ hk)
    fun i => (ext_apply he γ i).symm).symm

variable {A : Matrix I I ℤ} (hA : TauCeti.IsFiniteType A)

include he in
theorem reflection_ext (i : C) (γ : C → ℤ) :
    reflection A (e i) (ext e γ) = ext e (reflection (A.submatrix e e) i γ) := by
  rw [reflection_apply, reflection_apply]
  have hsum : ∑ j, A (e i) j * ext e γ j = ∑ l, (A.submatrix e e) i l * γ l := by
    symm
    refine Fintype.sum_of_injective e he _ _ (fun k hk => ?_) (fun l => ?_)
    · rw [ext_apply_of_notMem_range γ hk, mul_zero]
    · simp [ext_apply he]
  rw [hsum, ext_sub he, ext_smul he, ext_single he]

theorem ext_weylAction (w : (coxeterMatrix (hA.submatrix he)).Group) :
    ∃ w' : (coxeterMatrix hA).Group, w' ∈ (coxeterMatrix hA).toCoxeterSystem.parabolic
        (Set.range e) ∧
      ∀ γ : C → ℤ, weylAction hA w' (ext e γ) = ext e (weylAction (hA.submatrix he) w γ) := by
  set cs := (coxeterMatrix hA).toCoxeterSystem
  set csC := (coxeterMatrix (hA.submatrix he)).toCoxeterSystem
  obtain ⟨L, rfl⟩ := csC.wordProd_surjective w
  induction L with
  | nil =>
    refine ⟨1, one_mem _, fun γ => ?_⟩
    simp
  | cons i L ih =>
    obtain ⟨w', hw', h⟩ := ih
    refine ⟨cs.simple (e i) * w', mul_mem (cs.simple_mem_parabolic ⟨i, rfl⟩) hw', fun γ => ?_⟩
    rw [CoxeterSystem.wordProd_cons, weylAction_mul_apply, weylAction_mul_apply, h,
      weylAction_simple, weylAction_simple, reflection_ext he]

theorem exists_weylAction_ext_of_mem_parabolic {z : (coxeterMatrix hA).Group}
    (hz : z ∈ (coxeterMatrix hA).toCoxeterSystem.parabolic (Set.range e)) :
    ∃ z' : (coxeterMatrix (hA.submatrix he)).Group, ∀ δ : C → ℤ,
      weylAction hA z (ext e δ) = ext e (weylAction (hA.submatrix he) z' δ) := by
  let S : Subgroup (coxeterMatrix hA).Group :=
    { carrier := {z | ∃ z' : (coxeterMatrix (hA.submatrix he)).Group, ∀ δ : C → ℤ,
        weylAction hA z (ext e δ) = ext e (weylAction (hA.submatrix he) z' δ)}
      mul_mem' := by
        rintro a b ⟨a', ha⟩ ⟨b', hb⟩
        exact ⟨a' * b', fun δ => by
          rw [weylAction_mul_apply, hb, ha, weylAction_mul_apply]⟩
      one_mem' := ⟨1, fun δ => by simp⟩
      inv_mem' := by
        rintro a ⟨a', ha⟩
        refine ⟨a'⁻¹, fun δ => ?_⟩
        have h : weylAction hA a (ext e (weylAction (hA.submatrix he) a'⁻¹ δ)) = ext e δ := by
          rw [ha, weylAction_apply_inv_apply]
        rw [← h, weylAction_inv_apply_apply] }
  have hle : (coxeterMatrix hA).toCoxeterSystem.parabolic (Set.range e) ≤ S := by
    rw [CoxeterSystem.parabolic_le_iff]
    rintro _ ⟨i, rfl⟩
    refine ⟨(coxeterMatrix (hA.submatrix he)).toCoxeterSystem.simple i, fun δ => ?_⟩
    rw [weylAction_simple, weylAction_simple, reflection_ext he]
  exact hle hz

theorem ext_mem_roots_iff (γ : C → ℤ) :
    ext e γ ∈ roots hA ∅ ↔ γ ∈ roots (hA.submatrix he) ∅ := by
  constructor
  · rintro (⟨w, k, hk⟩ | ⟨w, k, hk, -⟩)
    ·
      have hsupp : ∀ l ∉ Set.range e, weylAction hA w (Pi.single k 1) l = 0 := fun l hl => by
        rw [← hk]
        exact ext_apply_of_notMem_range γ hl
      obtain ⟨z, hz, m, hm, hzm⟩ := exists_parabolic_of_support hA (Set.range e) w k hsupp
      obtain ⟨m', rfl⟩ := hm
      obtain ⟨z', hz'⟩ := exists_weylAction_ext_of_mem_parabolic he hA (inv_mem hz)
      refine Or.inl ⟨z', m', ext_injective he ?_⟩
      rw [← hz', ext_single he, ← hzm, ← hk, weylAction_inv_apply_apply]
    · exact (Set.notMem_empty k hk).elim
  · rintro (⟨w, k, rfl⟩ | ⟨w, k, hk, -⟩)
    · obtain ⟨w', -, hw'⟩ := ext_weylAction he hA w
      exact Or.inl ⟨w', e k, by rw [← ext_single he, ← hw']⟩
    · exact (Set.notMem_empty k hk).elim

theorem coxeterMatrix_submatrix_apply (i j : C) :
    coxeterMatrix (hA.submatrix he) i j = coxeterMatrix hA (e i) (e j) := by
  simp only [coxeterMatrix, TauCeti.coxeterMatrixOfCartanMatrix_apply, Matrix.submatrix_apply]

end CFSG.LieType.RootSystem.Restrict
