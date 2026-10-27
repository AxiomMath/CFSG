module

public import CFSG.Open.StatedAPI

public section

namespace CFSG.ClassicalGroups.SpecialLinear

open CFSG.Open CFSG.Open.StatedAPI Matrix

variable {m : ℕ} {K : Type} [Field K]

theorem exists_statedSL_mulVec_eq_transvection {v : Fin m → K} (f : Module.Dual K (Fin m → K))
    (hfv : f v = 0) :
    ∃ A ∈ StatedSL m K, ∀ z : Fin m → K,
      (A : Matrix (Fin m) (Fin m) K) *ᵥ z = z + f z • v := by
  set T := LinearEquiv.transvection hfv with hT
  set A : GL (Fin m) K := Matrix.GeneralLinearGroup.toLin.symm
    ((LinearMap.GeneralLinearGroup.generalLinearEquiv K (Fin m → K)).symm T) with hA
  have hAz : ∀ z : Fin m → K, (A : Matrix (Fin m) (Fin m) K) *ᵥ z = T z := by
    intro z
    have := Matrix.GeneralLinearGroup.toLin_apply A z
    rw [hA, MulEquiv.apply_symm_apply] at this
    exact this.symm
  refine ⟨A, mem_statedSL_of_det ?_, fun z => (hAz z).trans rfl⟩
  have h1 : (A : Matrix (Fin m) (Fin m) K).det =
      LinearMap.det (T : (Fin m → K) →ₗ[K] Fin m → K) := by
    rw [← LinearMap.det_toLin']
    congr 1
    refine LinearMap.ext fun z => ?_
    exact (hAz z).trans rfl
  rw [h1]
  have := LinearEquiv.transvection.det_eq_one hfv
  rw [← Units.val_inj, LinearEquiv.coe_det, Units.val_one] at this
  exact this

theorem exists_statedSL_mulVec_eq_of_independent {x y : Fin m → K}
    (h : ∀ s t : K, s • x + t • y = 0 → s = 0 ∧ t = 0) :
    ∃ A ∈ StatedSL m K, (A : Matrix (Fin m) (Fin m) K) *ᵥ x = y := by
  have hli : LinearIndependent K ![x, y] := LinearIndependent.pair_iff.mpr h
  obtain ⟨f, hf⟩ := Module.exists_dual_forall_apply_eq_one (K := K)
    (v := ![x, y]) (s := Set.univ) hli.linearIndepOn_univ
  have hfx : f x = 1 := hf 0 (Set.mem_univ _)
  have hfy : f y = 1 := hf 1 (Set.mem_univ _)
  have hfv : f (y - x) = 0 := by rw [map_sub, hfx, hfy, sub_self]
  obtain ⟨A, hA, hAz⟩ := exists_statedSL_mulVec_eq_transvection f hfv
  refine ⟨A, hA, ?_⟩
  rw [hAz, hfx, one_smul]
  abel

theorem exists_statedSL_mulVec_eq (hm : 2 ≤ m) {x y : Fin m → K} (hx : x ≠ 0) (hy : y ≠ 0) :
    ∃ A ∈ StatedSL m K, (A : Matrix (Fin m) (Fin m) K) *ᵥ x = y := by
  have indep : ∀ a b : Fin m → K, a ≠ 0 → (∀ c : K, b ≠ c • a) →
      ∀ s t : K, s • a + t • b = 0 → s = 0 ∧ t = 0 := by
    intro a b ha hb s t hst
    by_cases ht : t = 0
    · subst ht
      rw [zero_smul, add_zero] at hst
      exact ⟨(smul_eq_zero.mp hst).resolve_right ha, rfl⟩
    · exfalso
      apply hb (-(t⁻¹ * s))
      have : t • b = -(s • a) := eq_neg_of_add_eq_zero_right hst
      calc b = t⁻¹ • (t • b) := by rw [smul_smul, inv_mul_cancel₀ ht, one_smul]
        _ = -(t⁻¹ * s) • a := by rw [this, smul_neg, smul_smul, neg_smul]
  by_cases hxy : ∀ c : K, y ≠ c • x
  · exact exists_statedSL_mulVec_eq_of_independent (indep x y hx hxy)
  · push Not at hxy
    obtain ⟨c, hc⟩ := hxy
    obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact hx (funext hcon)
    obtain ⟨j, hj⟩ : ∃ j : Fin m, j ≠ i := by
      by_contra hcon
      push Not at hcon
      have h0 : (⟨0, by omega⟩ : Fin m) = i := hcon _
      have h1 : (⟨1, by omega⟩ : Fin m) = i := hcon _
      have := h0.trans h1.symm
      simp [Fin.ext_iff] at this
    set w : Fin m → K := Pi.single j 1 with hw
    have hwx : ∀ c' : K, w ≠ c' • x := by
      intro c' h
      have := congrFun h i
      simp [hw, Pi.single_apply, hj.symm] at this
      rcases this with h' | h'
      · subst h'
        simp at h
        exact (Pi.single_ne_zero_iff.mpr one_ne_zero) h
      · exact hi h'
    have hwy : ∀ c' : K, w ≠ c' • y := by
      intro c' h
      have hc0 : c ≠ 0 := by
        rintro rfl
        simp at hc
        exact hy hc
      apply hwx (c' * c)
      rw [h, hc, smul_smul]
    obtain ⟨A₁, hA₁, hA₁x⟩ := exists_statedSL_mulVec_eq_of_independent (indep x w hx hwx)
    obtain ⟨A₂, hA₂, hA₂w⟩ := exists_statedSL_mulVec_eq_of_independent (indep y w hy hwy)
    refine ⟨A₂⁻¹ * A₁, mul_mem (inv_mem hA₂) hA₁, ?_⟩
    rw [Units.val_mul, ← Matrix.mulVec_mulVec, hA₁x]
    rw [← hA₂w, Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Matrix.one_mulVec]

@[expose] def statedSLElations (m : ℕ) (K : Type) [Field K] (u : Fin m → K) :
    Subgroup (GL (Fin m) K) where
  carrier := {A | A ∈ StatedSL m K ∧ (A : Matrix (Fin m) (Fin m) K) *ᵥ u = u ∧
    ∀ x : Fin m → K, ∃ c : K, (A : Matrix (Fin m) (Fin m) K) *ᵥ x - x = c • u}
  mul_mem' := by
    rintro A B ⟨hA, hAu, hAx⟩ ⟨hB, hBu, hBx⟩
    refine ⟨mul_mem hA hB, ?_, fun x => ?_⟩
    · rw [Units.val_mul, ← Matrix.mulVec_mulVec, hBu, hAu]
    · obtain ⟨c, hc⟩ := hAx x
      obtain ⟨d, hd⟩ := hBx x
      refine ⟨d + c, ?_⟩
      have hBx' : (B : Matrix (Fin m) (Fin m) K) *ᵥ x = x + d • u := by
        rw [← hd]; abel
      have hAx' : (A : Matrix (Fin m) (Fin m) K) *ᵥ x = x + c • u := by
        rw [← hc]; abel
      rw [Units.val_mul, ← Matrix.mulVec_mulVec, hBx', Matrix.mulVec_add, Matrix.mulVec_smul, hAu,
        hAx', add_smul]
      abel
  one_mem' := ⟨one_mem _, by simp, fun x => ⟨0, by simp⟩⟩
  inv_mem' := by
    rintro A ⟨hA, hAu, hAx⟩
    have hinv : ((A⁻¹ : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) *ᵥ u = u := by
      have := congrArg (fun v => ((A⁻¹ : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) *ᵥ v) hAu
      simpa [Matrix.mulVec_mulVec, ← Units.val_mul] using this.symm
    refine ⟨inv_mem hA, hinv, fun x => ?_⟩
    obtain ⟨c, hc⟩ := hAx ((A⁻¹ : GL (Fin m) K) *ᵥ x)
    refine ⟨-c, ?_⟩
    have h1 : (A : Matrix (Fin m) (Fin m) K) *ᵥ
        (((A⁻¹ : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) *ᵥ x) = x := by
      rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
    rw [h1] at hc
    have : ((A⁻¹ : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) *ᵥ x =
        x - c • u := by
      rw [← hc]
      abel
    rw [this, neg_smul]
    abel

theorem mem_statedSLElations_iff {u : Fin m → K} {A : GL (Fin m) K} :
    A ∈ statedSLElations m K u ↔ A ∈ StatedSL m K ∧ (A : Matrix (Fin m) (Fin m) K) *ᵥ u = u ∧
      ∀ x : Fin m → K, ∃ c : K, (A : Matrix (Fin m) (Fin m) K) *ᵥ x - x = c • u :=
  Iff.rfl

end CFSG.ClassicalGroups.SpecialLinear
