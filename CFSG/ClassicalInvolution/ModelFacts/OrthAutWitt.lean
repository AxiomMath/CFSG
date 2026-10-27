module

public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalOrthConj

public section

namespace CFSG.ClassicalInvolution.ModelFacts.OrthAut

open QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin

section HypFam

variable {F V : Type} [Field F] [AddCommGroup V] [Module F V] {Q : QuadraticForm F V} {m : ℕ}

@[expose] def IsHypFam (Q : QuadraticForm F V) (v : Fin m → Bool → V) : Prop :=
  (∀ i s, Q (v i s) = 0) ∧ (∀ i j, i ≠ j → ∀ s t, polar Q (v i s) (v j t) = 0) ∧
    ∀ i s, polar Q (v i s) (v i (!s)) = 1

theorem IsHypFam.polar_eq {v : Fin m → Bool → V} (hv : IsHypFam Q v) (i j : Fin m) (s t : Bool) :
    polar Q (v i s) (v j t) = if i = j ∧ s = !t then 1 else 0 := by
  by_cases hij : i = j
  · subst hij
    by_cases hst : s = !t
    · rw [ite_eq_left ⟨rfl, hst⟩, hst]
      have := hv.2.2 i (!t)
      rwa [Bool.not_not] at this
    · have hst' : s = t := by cases s <;> cases t <;> simp_all
      rw [ite_eq_right (fun h => hst h.2), hst', QuadraticMap.polar_self, hv.1 i t]
      simp
  · rw [ite_eq_right (fun h => hij h.1)]
    exact hv.2.1 i j hij s t

@[expose] noncomputable def hypComb (v : Fin m → Bool → V) : (Fin m × Bool → F) →ₗ[F] V :=
  Fintype.linearCombination F (fun p : Fin m × Bool => v p.1 p.2)

theorem hypComb_apply (v : Fin m → Bool → V) (c : Fin m × Bool → F) :
    hypComb v c = ∑ p : Fin m × Bool, c p • v p.1 p.2 :=
  Fintype.linearCombination_apply F _ c

theorem hypComb_single (v : Fin m → Bool → V) (i : Fin m) (s : Bool) :
    hypComb v (Pi.single (i, s) (1 : F)) = v i s := by
  rw [hypComb, Fintype.linearCombination_apply_single, one_smul]

theorem polar_hypComb {v : Fin m → Bool → V} (hv : IsHypFam Q v) (c d : Fin m × Bool → F) :
    polar Q (hypComb v c) (hypComb v d) =
      ∑ i, (c (i, true) * d (i, false) + c (i, false) * d (i, true)) := by
  have h1 : polar Q (hypComb v c) (hypComb v d) =
      ∑ p : Fin m × Bool, ∑ q : Fin m × Bool,
        c p * d q * polar Q (v p.1 p.2) (v q.1 q.2) := by
    simp only [hypComb_apply, ← polarBilin_apply_apply, map_sum, map_smul, LinearMap.sum_apply,
      LinearMap.smul_apply, smul_eq_mul]
    conv_rhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    ring
  rw [h1]
  simp only [hv.polar_eq]
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Fintype.sum_bool]
  simp only [Fintype.sum_prod_type, Fintype.sum_bool]
  simp


theorem polar_hypComb_vec {v : Fin m → Bool → V} (hv : IsHypFam Q v) (c : Fin m × Bool → F)
    (i : Fin m) (s : Bool) : polar Q (hypComb v c) (v i s) = c (i, !s) := by
  rw [← hypComb_single (F := F) v i s, polar_hypComb hv]
  cases s
  · simp [Pi.single_apply]
  · simp [Pi.single_apply]

theorem map_hypComb [Invertible (2 : F)] {v : Fin m → Bool → V} (hv : IsHypFam Q v)
    (c : Fin m × Bool → F) : Q (hypComb v c) = ∑ i, c (i, true) * c (i, false) := by
  have h := QuadraticMap.polar_self Q (hypComb v c)
  rw [polar_hypComb hv, nsmul_eq_mul, Nat.cast_ofNat] at h
  have h2 : (2 : F) * Q (hypComb v c) = 2 * ∑ i, c (i, true) * c (i, false) := by
    rw [← h, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  exact mul_left_cancel₀ (Invertible.ne_zero (2 : F)) h2

theorem hypComb_injective {v : Fin m → Bool → V} (hv : IsHypFam Q v) :
    Function.Injective (hypComb (F := F) v) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro c hc
  funext ⟨i, s⟩
  have h := polar_hypComb_vec hv c i (!s)
  rw [hc, QuadraticMap.polar_zero_left, Bool.not_not] at h
  exact h.symm

theorem polarNondegOn_range_hypComb {v : Fin m → Bool → V} (hv : IsHypFam Q v) :
    PolarNondegOn Q (LinearMap.range (hypComb (F := F) v)) := by
  rintro x ⟨c, rfl⟩ hx
  have : c = 0 := by
    funext ⟨i, s⟩
    have h := hx (v i (!s)) ⟨Pi.single (i, !s) 1, hypComb_single v i (!s)⟩
    rw [polar_hypComb_vec hv c i (!s), Bool.not_not] at h
    exact h
  rw [this, map_zero]

end HypFam

section Witt

variable {F V : Type} [Field F] [AddCommGroup V] [Module F V] {Q : QuadraticForm F V} {m : ℕ}
  [Invertible (2 : F)] [FiniteDimensional F V]

theorem exists_isometry_of_isHypFam {v v' : Fin m → Bool → V} (hv : IsHypFam Q v)
    (hv' : IsHypFam Q v') :
    ∃ ω : V ≃ₗ[F] V, ω ∈ TauCeti.QuadraticMap.orthogonalGroup Q ∧ ∀ i s, ω (v i s) = v' i s := by
  let e := LinearEquiv.ofInjective (hypComb (F := F) v) (hypComb_injective hv)
  let e' := LinearEquiv.ofInjective (hypComb (F := F) v') (hypComb_injective hv')
  have hQ : ∀ c : Fin m × Bool → F, Q (hypComb v' c) = Q (hypComb v c) := fun c => by
    rw [map_hypComb hv', map_hypComb hv]
  let f : (Q.restrict (LinearMap.range (hypComb (F := F) v))).IsometryEquiv
      (Q.restrict (LinearMap.range (hypComb (F := F) v'))) :=
    { toLinearEquiv := e.symm.trans e'
      map_app' := fun x => by
        obtain ⟨c, rfl⟩ := e.surjective x
        change Q ((e' (e.symm (e c)) : LinearMap.range (hypComb (F := F) v')) : V) = Q (e c : V)
        rw [LinearEquiv.symm_apply_apply]
        exact hQ c }
  have hW : (Q.restrict (LinearMap.range (hypComb (F := F) v))).Nondegenerate :=
    QuadraticMap.nondegenerate_polar_iff.mp
      (nondegenerate_polarBilin_restrict (polarNondegOn_range_hypComb hv))
  obtain ⟨ω, hω⟩ := f.exists_extension hW
  refine ⟨ω.toLinearEquiv, TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr fun x => ω.map_app x,
    fun i s => ?_⟩
  have h := hω (e (Pi.single (i, s) 1))
  have h1 : ((e (Pi.single (i, s) 1) : LinearMap.range (hypComb (F := F) v)) : V) = v i s :=
    hypComb_single v i s
  have h2 : ((f (e (Pi.single (i, s) 1)) : LinearMap.range (hypComb (F := F) v')) : V) = v' i s := by
    change ((e' (e.symm (e (Pi.single (i, s) 1))) : LinearMap.range (hypComb (F := F) v')) : V) = _
    rw [LinearEquiv.symm_apply_apply]
    exact hypComb_single v' i s
  rw [h1, h2] at h
  exact h

end Witt


section Correction

variable {F V : Type} [Field F] [AddCommGroup V] [Module F V] {Q : QuadraticForm F V}
  [Invertible (2 : F)] [FiniteDimensional F V]

omit [Invertible (2 : F)] [FiniteDimensional F V] in
theorem isRefl_polarBilin (Q : QuadraticForm F V) : (polarBilin Q).IsRefl := fun x y h => by
  rw [polarBilin_apply_apply] at h ⊢
  rw [polar_comm]
  exact h

omit [Invertible (2 : F)] in
theorem mem_of_fixes_orthogonal (hQ : (polarBilin Q).Nondegenerate)
    {g : V ≃ₗ[F] V} (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (P : Submodule F V)
    (hfix : ∀ x ∈ LinearMap.BilinForm.orthogonal (polarBilin Q) P, g x = x) :
    ∀ y ∈ P, g y ∈ P := by
  intro y hy
  rw [← LinearMap.BilinForm.orthogonal_orthogonal hQ (isRefl_polarBilin Q) P,
    LinearMap.BilinForm.mem_orthogonal_iff]
  intro x hx
  have hx' : ∀ n ∈ P, polar Q n x = 0 := fun n hn => by
    simpa [polarBilin_apply_apply] using (LinearMap.BilinForm.mem_orthogonal_iff.mp hx) n hn
  have := TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp hg
  have h1 : polar Q (g y) (g x) = polar Q y x := by
    simp only [QuadraticMap.polar, ← map_add, this]
  rw [hfix x hx] at h1
  rw [polarBilin_apply_apply, polar_comm, h1]
  exact hx' y hy


omit [Invertible (2 : F)] in
theorem symm_mem_of_mem (h : V ≃ₗ[F] V) (P : Submodule F V) (hP : ∀ y ∈ P, h y ∈ P) :
    ∀ y ∈ P, h.symm y ∈ P := by
  have hle : P.map (h : V →ₗ[F] V) ≤ P := by
    rintro _ ⟨y, hy, rfl⟩
    exact hP y hy
  have heq : P.map (h : V →ₗ[F] V) = P :=
    Submodule.eq_of_le_of_finrank_eq hle (LinearEquiv.finrank_map_eq h P)
  intro y hy
  rw [← heq] at hy
  obtain ⟨x, hx, rfl⟩ := hy
  simpa using hx

theorem exists_spin_normalization [Finite F] [Nontrivial V] (hodd : Odd (Nat.card F))
    (hQ : Q.Nondegenerate) {m : ℕ} {v v' : Fin m → Bool → V} (hv : IsHypFam Q v)
    (hv' : IsHypFam Q v') {P : Submodule F V} (hP : (Q.restrict P).Nondegenerate)
    (hP2 : 2 ≤ Module.finrank F P) :
    ∃ (x : spinGroup Q) (h : V ≃ₗ[F] V),
      (∀ y ∈ P, h y ∈ P) ∧ (∀ z, (∀ y ∈ P, polar Q y z = 0) → h z = z) ∧
        ∀ i s, v' i s = spinAction Q x (h (v i s)) := by
  obtain ⟨ω, hω, hωv⟩ := exists_isometry_of_isHypFam hv hv'
  have hQ' : (polarBilin Q).Nondegenerate := QuadraticMap.nondegenerate_polar_iff.mpr hQ
  have hWP : ∀ x ∈ LinearMap.BilinForm.orthogonal (polarBilin Q) P, ∀ y ∈ P, polar Q y x = 0 :=
    fun x hx y hy => by
      have := (LinearMap.BilinForm.mem_orthogonal_iff.mp hx) y hy
      simpa [polarBilin_apply_apply] using this
  obtain ⟨h₁, hfix, hdet, hsn⟩ :=
    CFSG.ClassicalInvolution.ModelFacts.exists_reflection_correction hodd hQ hWP hP hP2 ⟨ω, hω⟩
  have hd : QuadraticMap.orthogonalDet Q (⟨ω, hω⟩ * h₁) = 1 := by
    rw [map_mul, hdet, ← pow_two]
    exact TauCeti.QuadraticMap.orthogonalDet_sq hQ'.1 ⟨ω, hω⟩
  have hs : CliffordAlgebra.orthogonalSpinorNorm Q hQ (⟨ω, hω⟩ * h₁) = 1 := by
    rw [map_mul, hsn]
    exact mul_inv_cancel _
  obtain ⟨x, hx⟩ := CFSG.ClassicalInvolution.ModelFacts.exists_spinAction_eq hQ _ hd hs
  have hfix' : ∀ z ∈ LinearMap.BilinForm.orthogonal (polarBilin Q) P, (h₁ : V ≃ₗ[F] V) z = z :=
    hfix
  have hpres := mem_of_fixes_orthogonal hQ' h₁.2 P hfix'
  refine ⟨x, (h₁ : V ≃ₗ[F] V).symm, symm_mem_of_mem _ P hpres, fun z hz => ?_, fun i s => ?_⟩
  · have hz' : z ∈ LinearMap.BilinForm.orthogonal (polarBilin Q) P :=
      LinearMap.BilinForm.mem_orthogonal_iff.mpr fun n hn => by
        simpa [polarBilin_apply_apply] using hz n hn
    rw [LinearEquiv.symm_apply_eq]
    exact (hfix' z hz').symm
  · rw [hx]
    change v' i s = ω ((h₁ : V ≃ₗ[F] V) ((h₁ : V ≃ₗ[F] V).symm (v i s)))
    rw [LinearEquiv.apply_symm_apply, hωv]

end Correction

end CFSG.ClassicalInvolution.ModelFacts.OrthAut
