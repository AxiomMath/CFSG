module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P51QSplit
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P51QCov
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P51QLin
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P51QTrv

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.T1.P51Q

open CFSG Subgroup Matrix CatalogueBProjectiveInvolution CatalogueBProjectiveCoordinates

variable {K : Type} [Field K] {n : ℕ}

theorem split_block [Finite K] (htwo : (2 : K) ≠ 0) (h4 : 4 ≤ Nat.card K) (A : GL (Fin n) K)
    (b : Kˣ)
    (hsq : A ^ 2 = GeneralLinearGroup.scalar (Fin n) (b ^ 2))
    (hs : 2 ≤ negativeMatrixDimension A b.val) (g : SpecialLinearGroup (Fin n) K)
    (h₂ : ∀ m ∈ pullSL A (matrixCentralizerSplitEquiv A b htwo hsq) (sndSL _ _),
      g * m = m * g)
    (h₁ : 2 ≤ positiveMatrixDimension A b.val →
      ∀ m ∈ pullSL A (matrixCentralizerSplitEquiv A b htwo hsq) (fstSL _ _), g * m = m * g) :
    ∃ c₁ c₂ : K, ∀ v, splitCoord A b htwo hsq ((g : Matrix (Fin n) (Fin n) K) *ᵥ v) =
      (c₁ • (splitCoord A b htwo hsq v).1, c₂ • (splitCoord A b htwo hsq v).2) := by
  set r := positiveMatrixDimension A b.val
  set s := negativeMatrixDimension A b.val
  set e := matrixCentralizerSplitEquiv A b htwo hsq
  set β := splitCoord A b htwo hsq
  set gL : ((Fin r → K) × (Fin s → K)) →ₗ[K] ((Fin r → K) × (Fin s → K)) :=
    β.toLinearMap ∘ₗ (Matrix.mulVecLin (g : Matrix (Fin n) (Fin n) K)) ∘ₗ β.symm.toLinearMap
    with hgL
  have hgL_apply : ∀ w, gL w = β ((g : Matrix (Fin n) (Fin n) K) *ᵥ β.symm w) := fun _ => rfl
  have hrel : ∀ {m : SpecialLinearGroup (Fin n) K}, g * m = m * g →
      ∀ (hm : Matrix.SpecialLinearGroup.toGL m ∈ centralizer ({A} : Set (GL (Fin n) K)))
        {x₁ : GL (Fin r) K} {x₂ : GL (Fin s) K}, e ⟨_, hm⟩ = (x₁, x₂) →
      ∀ w, gL (x₁.val *ᵥ w.1, x₂.val *ᵥ w.2) = (x₁.val *ᵥ (gL w).1, x₂.val *ᵥ (gL w).2) := by
    intro m hgm hm x₁ x₂ hx w
    have h1 := splitCoord_pull A b htwo hsq hm hx (β.symm w)
    rw [LinearEquiv.apply_symm_apply] at h1
    have h2 := splitCoord_pull A b htwo hsq hm hx ((g : Matrix (Fin n) (Fin n) K) *ᵥ β.symm w)
    have hgm' : (g : Matrix (Fin n) (Fin n) K) * m = m * g := congrArg Subtype.val hgm
    rw [hgL_apply, hgL_apply, ← h1, LinearEquiv.symm_apply_apply, Matrix.mulVec_mulVec, hgm',
      ← Matrix.mulVec_mulVec, h2]
  have hsnd : ∀ i j : Fin s, i ≠ j → ∀ (t : K) (w : (Fin r → K) × (Fin s → K)),
      gL (w.1, transvection i j t *ᵥ w.2) = ((gL w).1, transvection i j t *ᵥ (gL w).2) := by
    intro i j hij t w
    have : Group.IsPerfect (sndSL (K := K) r s) := (isQuasisimple_sndSL h4 r hs).1
    set T : SpecialLinearGroup (Fin s) K := ⟨transvection i j t, det_transvection_of_ne i j hij t⟩
    obtain ⟨m, hm, hmA, hx⟩ := exists_pullSL_eq e (sndSL r s)
      (x := (1, Matrix.SpecialLinearGroup.toGL T)) ⟨T, rfl⟩
    have := hrel (h₂ m hm) hmA hx w
    simp only [Units.val_one, Matrix.one_mulVec] at this
    exact this
  obtain ⟨⟨c₂, hc₂⟩, hz₂⟩ := prod_transvection_commutant hs gL.toAddMonoidHom hsnd
  obtain ⟨c₁, hc₁⟩ : ∃ c₁ : K, ∀ u, gL (u, 0) = (c₁ • u, 0) := by
    rcases Nat.lt_or_ge r 2 with hr | hr
    · obtain ⟨c₁, hc⟩ := linear_fin_le_one (by omega : r ≤ 1)
        ((LinearMap.fst K _ _) ∘ₗ gL ∘ₗ (LinearMap.inl K _ _))
      exact ⟨c₁, fun u => Prod.ext (hc u) (hz₂ u)⟩
    · have hfst : ∀ i j : Fin r, i ≠ j → ∀ (t : K) (w : (Fin r → K) × (Fin s → K)),
          gL (transvection i j t *ᵥ w.1, w.2) = (transvection i j t *ᵥ (gL w).1, (gL w).2) := by
        intro i j hij t w
        have : Group.IsPerfect (fstSL (K := K) r s) := (isQuasisimple_fstSL h4 hr s).1
        set T : SpecialLinearGroup (Fin r) K :=
          ⟨transvection i j t, det_transvection_of_ne i j hij t⟩
        obtain ⟨m, hm, hmA, hx⟩ := exists_pullSL_eq e (fstSL r s)
          (x := (Matrix.SpecialLinearGroup.toGL T, 1)) ⟨T, rfl⟩
        have := hrel (h₁ hr m hm) hmA hx w
        simp only [Units.val_one, Matrix.one_mulVec] at this
        exact this
      exact (prod_transvection_commutant_fst hr gL.toAddMonoidHom hfst).1
  refine ⟨c₁, c₂, fun v => ?_⟩
  have h1 : β ((g : Matrix (Fin n) (Fin n) K) *ᵥ v) = gL (β v) := by
    rw [hgL_apply, LinearEquiv.symm_apply_apply]
  have h2 : β v = ((β v).1, 0) + (0, (β v).2) := by simp
  rw [h1, h2, map_add, hc₁]
  have h3 := hc₂ (β v).2
  simp only [LinearMap.toAddMonoidHom_coe] at h3
  rw [h3]
  simp

theorem split_ne_scalar (htwo : (2 : K) ≠ 0) (A : GL (Fin n) K) (b : Kˣ)
    (hsq : A ^ 2 = GeneralLinearGroup.scalar (Fin n) (b ^ 2))
    (hr : 1 ≤ positiveMatrixDimension A b.val) (hs : 1 ≤ negativeMatrixDimension A b.val)
    {x : GL (Fin (positiveMatrixDimension A b.val)) K ×
      GL (Fin (negativeMatrixDimension A b.val)) K}
    (hx : (x.1 = 1 ∧ x.2 ≠ 1) ∨ (x.2 = 1 ∧ x.1 ≠ 1)) (u : Kˣ)
    (h : GeneralLinearGroup.scalar (Fin n) u ∈ centralizer ({A} : Set (GL (Fin n) K))) :
    x ≠ matrixCentralizerSplitEquiv A b htwo hsq ⟨_, h⟩ := by
  intro hxe
  have h1 : (⟨_, h⟩ : centralizer ({A} : Set (GL (Fin n) K))) = ordinaryCentralizerScalar A u :=
    Subtype.ext rfl
  rw [h1, matrixCentralizerSplitEquiv_scalar] at hxe
  rcases hx with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · have hu := eq_one_of_scalar_eq_one hr (h1 ▸ (congrArg Prod.fst hxe).symm)
    exact h2 (by rw [congrArg Prod.snd hxe, hu]; simp)
  · have hu := eq_one_of_scalar_eq_one hs (h1 ▸ (congrArg Prod.snd hxe).symm)
    exact h2 (by rw [congrArg Prod.fst hxe, hu]; simp)

theorem toGL_diagSL_neg_ne_one (htwo : (2 : K) ≠ 0) {m : ℕ} (hm : 2 ≤ m) :
    Matrix.SpecialLinearGroup.toGL (diagSL hm (-1 : K) (-1) (by ring)) ≠ 1 := by
  intro h
  have h1 := congrArg (fun g : GL (Fin m) K => (g : Matrix (Fin m) (Fin m) K) ⟨0, by omega⟩
    ⟨0, by omega⟩) h
  simp only [Matrix.SpecialLinearGroup.coe_GL_coe_matrix, diagSL_apply_zero, Units.val_one,
    one_apply_eq] at h1
  exact htwo (by rw [show (2 : K) = 1 - (-1) by ring, h1, sub_self])

theorem toGL_diagSL_neg_pow_four {m : ℕ} (hm : 2 ≤ m) :
    Matrix.SpecialLinearGroup.toGL (diagSL hm (-1 : K) (-1) (by ring)) ^ 4 = 1 := by
  rw [← map_pow, diagSL_pow_four hm _ (by norm_num) (by norm_num), map_one]

theorem evenCent_split [Finite K] (htwo : (2 : K) ≠ 0) (h4 : 4 ≤ Nat.card K)
    {X : Type} [Group X] (π : SpecialLinearGroup (Fin n) K →* X) (hπ : Function.Surjective π)
    (hker : ∀ s, π s = 1 ↔ s ∈ center (SpecialLinearGroup (Fin n) K))
    (a : SpecialLinearGroup (Fin n) K) (b : Kˣ)
    (hsq : Matrix.SpecialLinearGroup.toGL a ^ 2 = GeneralLinearGroup.scalar (Fin n) (b ^ 2))
    (hr : 1 ≤ positiveMatrixDimension (Matrix.SpecialLinearGroup.toGL a) b.val)
    (hs : 2 ≤ negativeMatrixDimension (Matrix.SpecialLinearGroup.toGL a) b.val) :
    EvenCentComm X (π a) ∧ EvenCentInv X (π a) := by
  set A := Matrix.SpecialLinearGroup.toGL a with hAdef
  set r := positiveMatrixDimension A b.val
  set s := negativeMatrixDimension A b.val
  set e := matrixCentralizerSplitEquiv A b htwo hsq
  set β := splitCoord A b htwo hsq
  have hn : 0 < n := by
    have := splitMatrixDimension_sum A b htwo hsq
    rw [Fintype.card_fin] at this
    omega
  set 𝓜 : Set (Subgroup (SpecialLinearGroup (Fin n) K)) :=
    {M | M = pullSL A e (sndSL r s) ∨ (2 ≤ r ∧ M = pullSL A e (fstSL r s))} with h𝓜
  have hblock : ∀ g : SpecialLinearGroup (Fin n) K, (∀ M ∈ 𝓜, ∀ m ∈ M, g * m = m * g) →
      ∃ c₁ c₂ : K, ∀ v, β ((g : Matrix (Fin n) (Fin n) K) *ᵥ v) = (c₁ • (β v).1, c₂ • (β v).2) :=
    fun g hg => split_block htwo h4 A b hsq hs g (hg _ (Or.inl rfl))
      (fun hr2 => hg _ (Or.inr ⟨hr2, rfl⟩))
  have hC : ∀ M ∈ 𝓜, M ≤ centralizer ({a} : Set (SpecialLinearGroup (Fin n) K)) := by
    rintro M (rfl | ⟨-, rfl⟩) <;> exact pullSL_le_centralizer e _ rfl
  have hN : ∀ M ∈ 𝓜, ∀ x ∈ centralizer ({a} : Set (SpecialLinearGroup (Fin n) K)),
      ∀ m ∈ M, x * m * x⁻¹ ∈ M := by
    rintro M (rfl | ⟨-, rfl⟩) x hx m hm <;> exact conj_mem_pullSL e _ rfl hx hm
  have hQ : ∀ M ∈ 𝓜, IsQuasisimple M := by
    rintro M (rfl | ⟨hr2, rfl⟩)
    · exact isQuasisimple_pullSL e _ (isQuasisimple_sndSL h4 r hs)
    · exact isQuasisimple_pullSL e _ (isQuasisimple_fstSL h4 hr2 s)
  have hE : ∀ M ∈ 𝓜, ∃ m ∈ M, π m ≠ 1 ∧ m ^ 4 = 1 := by
    rintro M (rfl | ⟨hr2, rfl⟩)
    · have : Group.IsPerfect (sndSL (K := K) r s) := (isQuasisimple_sndSL h4 r hs).1
      obtain ⟨m, hm, hmc, hm4⟩ := exists_noncentral_pullSL e (sndSL r s) hn
        (x := (1, Matrix.SpecialLinearGroup.toGL (diagSL hs (-1 : K) (-1) (by ring)))) ⟨_, rfl⟩
        (Prod.ext (one_pow 4) (toGL_diagSL_neg_pow_four hs))
        (split_ne_scalar htwo A b hsq hr (by omega)
          (Or.inl ⟨rfl, toGL_diagSL_neg_ne_one htwo hs⟩))
      exact ⟨m, hm, fun h => hmc ((hker m).mp h), hm4⟩
    · have : Group.IsPerfect (fstSL (K := K) r s) := (isQuasisimple_fstSL h4 hr2 s).1
      obtain ⟨m, hm, hmc, hm4⟩ := exists_noncentral_pullSL e (fstSL r s) hn
        (x := (Matrix.SpecialLinearGroup.toGL (diagSL hr2 (-1 : K) (-1) (by ring)), 1)) ⟨_, rfl⟩
        (Prod.ext (toGL_diagSL_neg_pow_four hr2) (one_pow 4))
        (split_ne_scalar htwo A b hsq hr (by omega)
          (Or.inr ⟨rfl, toGL_diagSL_neg_ne_one htwo hr2⟩))
      exact ⟨m, hm, fun h => hmc ((hker m).mp h), hm4⟩
  have hcomm : ∀ g h : SpecialLinearGroup (Fin n) K, (∀ M ∈ 𝓜, ∀ m ∈ M, g * m = m * g) →
      (∀ M ∈ 𝓜, ∀ m ∈ M, h * m = m * h) → g * h = h * g := by
    intro g h hg hh
    obtain ⟨c₁, c₂, hgc⟩ := hblock g hg
    obtain ⟨d₁, d₂, hhc⟩ := hblock h hh
    refine Subtype.ext (Matrix.ext_iff_mulVec.mpr fun v => β.injective ?_)
    change β (((g : Matrix (Fin n) (Fin n) K) * (h : Matrix (Fin n) (Fin n) K)) *ᵥ v) =
      β (((h : Matrix (Fin n) (Fin n) K) * (g : Matrix (Fin n) (Fin n) K)) *ᵥ v)
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hgc, hhc, hhc, hgc]
    simp only [smul_smul, mul_comm]
  have hinv : ∀ g : SpecialLinearGroup (Fin n) K, (∀ M ∈ 𝓜, ∀ m ∈ M, g * m = m * g) →
      g * g ∈ center (SpecialLinearGroup (Fin n) K) →
      g ∈ center (SpecialLinearGroup (Fin n) K) ∨
        g * a⁻¹ ∈ center (SpecialLinearGroup (Fin n) K) := by
    intro g hg hgg
    obtain ⟨c₁, c₂, hgc⟩ := hblock g hg
    obtain ⟨ρ, -, hρ⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hgg
    have hgg' : ∀ v, β ((g : Matrix (Fin n) (Fin n) K) *ᵥ ((g : Matrix (Fin n) (Fin n) K) *ᵥ v))
        = ρ • β v := by
      intro v
      rw [Matrix.mulVec_mulVec]
      have h1 : (g : Matrix (Fin n) (Fin n) K) * g = scalar (Fin n) ρ := by
        rw [hρ]
        rfl
      rw [h1, scalar_apply, ← smul_one_eq_diagonal, Matrix.smul_mulVec, Matrix.one_mulVec,
        map_smul]
    have hsq₁ : c₁ * c₁ = ρ := by
      have h1 := hgg' (β.symm (Pi.single ⟨0, hr⟩ 1, 0))
      rw [hgc, LinearEquiv.apply_symm_apply, hgc, LinearEquiv.apply_symm_apply] at h1
      have h2 := congrArg (fun p => p.1 ⟨0, hr⟩) h1
      simpa [smul_smul] using h2
    have hsq₂ : c₂ * c₂ = ρ := by
      have h1 := hgg' (β.symm (0, Pi.single ⟨0, by omega⟩ 1))
      rw [hgc, LinearEquiv.apply_symm_apply, hgc, LinearEquiv.apply_symm_apply] at h1
      have h2 := congrArg (fun p => p.2 ⟨0, by omega⟩) h1
      simpa [smul_smul] using h2
    have h3 : (c₁ - c₂) * (c₁ + c₂) = 0 := by linear_combination hsq₁ - hsq₂
    rcases mul_eq_zero.mp h3 with h | h
    · left
      have hc : c₁ = c₂ := sub_eq_zero.mp h
      refine mem_center_of_mulVec_eq_smul (c := c₁) fun v => β.injective ?_
      rw [hgc, map_smul, hc]
      rfl
    · right
      have hc : c₁ = -c₂ := eq_neg_of_add_eq_zero_left h
      refine mem_center_of_mulVec_eq_smul (c := -c₂ / b.val) fun v => β.injective ?_
      have hAw : A.val *ᵥ (((a⁻¹ : SpecialLinearGroup (Fin n) K) :
          Matrix (Fin n) (Fin n) K) *ᵥ v) = v := by
        rw [Matrix.mulVec_mulVec]
        have h1 : A.val * ((a⁻¹ : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1 :=
          congrArg Subtype.val (mul_inv_cancel a)
        rw [h1, Matrix.one_mulVec]
      have h2 := splitCoord_A A b htwo hsq
        (((a⁻¹ : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ v)
      rw [hAw] at h2
      change β (((g : Matrix (Fin n) (Fin n) K) *
        ((a⁻¹ : Matrix.SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K)) *ᵥ v) =
          β ((-c₂ / b.val) • v)
      rw [← Matrix.mulVec_mulVec, hgc, map_smul, h2, hc]
      have hb := b.ne_zero
      refine Prod.ext ?_ ?_
      · simp only [Prod.smul_fst, smul_smul]
        congr 1
        field_simp
      · simp only [Prod.smul_snd, smul_smul]
        congr 1
        field_simp
  exact ⟨evenCentComm_of_cover π hπ (fun s h => (hker s).mp h) a 𝓜 hC hN hQ hE hcomm,
    evenCentInv_of_cover π hπ (fun s h => (hker s).mp h) (fun s h => (hker s).mpr h) a 𝓜 hC hN
      hQ hE hinv⟩

end CFSG.ComponentClassification.HarrisLit.T1.P51Q
