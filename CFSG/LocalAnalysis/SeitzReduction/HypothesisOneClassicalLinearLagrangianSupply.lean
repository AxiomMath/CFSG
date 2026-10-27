module

public import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneClassicalLinearLagrangianRigid

public noncomputable section

namespace CFSG.SeitzReduction

open Subgroup
open scoped commutatorElement

theorem mul_mul_inv_mem_closure_odd_fixed {C : Type*} [Group C] {x : MulAut C} {g d : C}
    (hg : x g = g) (hd : d ∈ closure {c : C | x c = c ∧ Odd (orderOf c)}) :
    g * d * g⁻¹ ∈ closure {c : C | x c = c ∧ Odd (orderOf c)} := by
  induction hd using closure_induction with
  | mem c hc =>
    refine subset_closure ⟨?_, ?_⟩
    · rw [map_mul, map_mul, map_inv, hg, hc.1]
    · rw [show g * c * g⁻¹ = MulAut.conj g c from rfl, MulEquiv.orderOf_eq]
      exact hc.2
  | one => rw [mul_one, mul_inv_cancel]; exact one_mem _
  | mul a c _ _ ha hc =>
    rw [show g * (a * c) * g⁻¹ = (g * a * g⁻¹) * (g * c * g⁻¹) by group]
    exact mul_mem ha hc
  | inv a _ ha =>
    rw [show g * a⁻¹ * g⁻¹ = (g * a * g⁻¹)⁻¹ by group]
    exact inv_mem ha

theorem commutatorElement_eq_mul_inv_of_mul_eq {G : Type*} [Group G] {u u' h : G}
    (hu : h * u = u' * h) : ⁅u, h⁆ = u * u'⁻¹ := by
  have hu' : u' = h * u * h⁻¹ := by rw [hu, mul_inv_cancel_right]
  rw [commutatorElement_def, hu']
  group

end CFSG.SeitzReduction

namespace CFSG.SeitzReduction.ClassicalLinear.Lagrangian

open Matrix Subgroup CFSG.LocalAnalysis.ComponentInitial LinearFlag
open CFSG.ComponentClassification.UnbalancedCatalog EvenLinearSL
open scoped commutatorElement

variable {K : Type*} [Field K] {n : ℕ}

theorem sl_ext_of_coe {g g' : SpecialLinearGroup (Fin n) K}
    (h : (g : Matrix (Fin n) (Fin n) K) = (g' : Matrix (Fin n) (Fin n) K)) : g = g' :=
  Subtype.ext h

theorem mul_rankOne_eq_rankOne_mul (g : SpecialLinearGroup (Fin n) K) {x a x' a' : Fin n → K}
    (h : a ⬝ᵥ x = 0) (h' : a' ⬝ᵥ x' = 0)
    (hg : vecMulVec ((g : Matrix (Fin n) (Fin n) K) *ᵥ x) a =
      vecMulVec x' (a' ᵥ* (g : Matrix (Fin n) (Fin n) K))) :
    g * rankOne x a h = rankOne x' a' h' * g := by
  refine sl_ext_of_coe ?_
  change (g : Matrix (Fin n) (Fin n) K) * (1 + vecMulVec x a) =
    (1 + vecMulVec x' a') * (g : Matrix (Fin n) (Fin n) K)
  rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul, mul_vecMulVec,
    vecMulVec_mul, hg]

theorem rankOne_smul_mul_inv (x a : Fin n → K) (c d : K) (hc : a ⬝ᵥ (c • x) = 0)
    (hd : a ⬝ᵥ (d • x) = 0) (h : a ⬝ᵥ ((c - d) • x) = 0) :
    rankOne (c • x) a hc * (rankOne (d • x) a hd)⁻¹ = rankOne ((c - d) • x) a h := by
  refine sl_ext_of_coe ?_
  change (1 + vecMulVec (c • x) a) *
    (((rankOne (d • x) a hd)⁻¹ : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      1 + vecMulVec ((c - d) • x) a
  rw [coe_rankOne_inv, Matrix.add_mul,
    Matrix.one_mul, Matrix.mul_sub, Matrix.mul_one, vecMulVec_mul_vecMulVec, hd, zero_smul,
    vecMulVec_zero, sub_zero, sub_smul, sub_vecMulVec]
  abel

section Supply

variable {ℓ : ℕ} (b : Module.Basis (Fin ℓ ⊕ (Fin ℓ ⊕ Fin 0)) K (Fin n → K))

@[expose] def offDiag : Set (SpecialLinearGroup (Fin n) K) :=
  {g | ∃ (i j : Fin ℓ) (c : K) (h : dualVec b (.inl i) ⬝ᵥ (c • b (.inr (.inl j))) = 0),
    i ≠ j ∧ g = rankOne (c • b (.inr (.inl j))) (dualVec b (.inl i)) h}

theorem rankOne_mem_offDiag {i j : Fin ℓ} (hij : i ≠ j) (c : K) (h) :
    rankOne (c • b (.inr (.inl j))) (dualVec b (.inl i)) h ∈ offDiag b :=
  ⟨i, j, c, h, hij, rfl⟩

variable {s : GL (Fin n) K}

theorem rankOne_inr_mem_comap_centralizer
    (hbX : ∀ i, ((s : Matrix (Fin n) (Fin n) K) - 1) *ᵥ b (.inl i) = b (.inr (.inl i)))
    (hbL : ∀ k, ((s : Matrix (Fin n) (Fin n) K) - 1) *ᵥ b (.inr k) = 0) (i j : Fin ℓ) (c : K)
    (h : dualVec b (.inl i) ⬝ᵥ (c • b (.inr (.inl j))) = 0) :
    rankOne (c • b (.inr (.inl j))) (dualVec b (.inl i)) h ∈
      (centralizer {s}).comap (SpecialLinearGroup.toGL :
        SpecialLinearGroup (Fin n) K →* GL (Fin n) K) :=
  rankOne_mem_comap_centralizer h (by rw [mulVec_smul, hbL, smul_zero])
    (dualVec_inl_vecMul b hbX hbL i)

theorem closure_offDiag_le
    (hbX : ∀ i, ((s : Matrix (Fin n) (Fin n) K) - 1) *ᵥ b (.inl i) = b (.inr (.inl i)))
    (hbL : ∀ k, ((s : Matrix (Fin n) (Fin n) K) - 1) *ᵥ b (.inr k) = 0) :
    closure (offDiag b) ≤ (centralizer {s}).comap (SpecialLinearGroup.toGL :
      SpecialLinearGroup (Fin n) K →* GL (Fin n) K) := by
  rw [closure_le]
  rintro _ ⟨i, j, c, h, -, rfl⟩
  exact rankOne_inr_mem_comap_centralizer b hbX hbL i j c h

theorem closure_offDiag_le_commutator
    (hbX : ∀ i, ((s : Matrix (Fin n) (Fin n) K) - 1) *ᵥ b (.inl i) = b (.inr (.inl i)))
    (hbL : ∀ k, ((s : Matrix (Fin n) (Fin n) K) - 1) *ᵥ b (.inr k) = 0) (hℓ : 3 ≤ ℓ) :
    closure (offDiag b) ≤ ⁅closure (offDiag b), (centralizer {s}).comap
      (SpecialLinearGroup.toGL : SpecialLinearGroup (Fin n) K →* GL (Fin n) K)⁆ := by
  classical
  rw [closure_le]
  rintro _ ⟨i, j, c, h, hij, rfl⟩
  obtain ⟨k, hki, hkj⟩ : ∃ k : Fin ℓ, k ≠ i ∧ k ≠ j := by
    by_contra hcon
    push Not at hcon
    have hsub : (Finset.univ : Finset (Fin ℓ)) ⊆ {i, j} := fun k _ => by
      by_cases hk : k = i
      · simp [hk]
      · simp [hcon k hk]
    have := (Finset.card_le_card hsub).trans Finset.card_le_two
    rw [Finset.card_univ, Fintype.card_fin] at this
    omega
  have h₁ : dualVec b (.inl k) ⬝ᵥ (c • b (.inr (.inl j))) = 0 := by
    rw [dotProduct_smul, dualVec_inl_dotProduct_inr, smul_zero]
  have e : ⁅rankOne (c • b (.inr (.inl j))) (dualVec b (.inl k)) h₁, leviElt b hki⁆ =
      rankOne (c • b (.inr (.inl j))) (dualVec b (.inl i)) h := by
    apply Subtype.ext
    rw [coe_commutator_of_mul_eq_zero' (coe_rankOne _ _ h₁) (coe_leviElt b hki)
      (vecMulVec_sq_eq_zero h₁) (leviQ_mul_self b hki) ?_, coe_rankOne]
    · simp [leviQ, Matrix.mul_add, vecMulVec_mul_vecMulVec, dualVec_dotProduct_basis]
    · simp [leviQ, Matrix.add_mul, vecMulVec_mul_vecMulVec, dualVec_dotProduct_basis,
        Ne.symm hij]
  rw [← e]
  exact commutator_mem_commutator (subset_closure (rankOne_mem_offDiag b hkj c h₁))
    (leviElt_mem b hbX hbL hki)

theorem offDiag_mem_closure_odd_fixed [Finite K]
    (hbX : ∀ i, ((s : Matrix (Fin n) (Fin n) K) - 1) *ᵥ b (.inl i) = b (.inr (.inl i)))
    (hbL : ∀ k, ((s : Matrix (Fin n) (Fin n) K) - 1) *ᵥ b (.inr k) = 0) (hℓ : 3 ≤ ℓ)
    {g : SpecialLinearGroup (Fin n) K} (hg : g ∈ offDiag b) :
    proj n K g ∈ closure {c : projectiveSL n K | conjAut n K s c = c ∧ Odd (orderOf c)} := by
  have hD : (closure (offDiag b)).map (proj n K) ≤
      closure {c : projectiveSL n K | conjAut n K s c = c ∧ Odd (orderOf c)} := by
    refine le_closure_odd_fixed_of_le_commutator (map_mono (closure_offDiag_le b hbX hbL)) ?_ ?_
    · rintro _ ⟨g, hg, rfl⟩
      exact conjAut_proj_eq_of_mem hg
    · rw [← map_commutator]
      exact map_mono (closure_offDiag_le_commutator b hbX hbL hℓ)
  exact hD (mem_map_of_mem _ (subset_closure hg))

theorem extra_mem_closure_odd_fixed
    (hbX : ∀ i, ((s : Matrix (Fin n) (Fin n) K) - 1) *ᵥ b (.inl i) = b (.inr (.inl i)))
    (hbL : ∀ k, ((s : Matrix (Fin n) (Fin n) K) - 1) *ᵥ b (.inr k) = 0) {i₀ i₁ : Fin ℓ}
    (h01 : i₀ ≠ i₁) (h₀ : dualVec b (.inl i₁) ⬝ᵥ b (.inr (.inl i₀)) = 0)
    (hD : proj n K (rankOne (b (.inr (.inl i₀))) (dualVec b (.inl i₁)) h₀) ∈
      closure {c : projectiveSL n K | conjAut n K s c = c ∧ Odd (orderOf c)})
    (h : (dualVec b (.inl i₁) - dualVec b (.inl i₀)) ⬝ᵥ
      (b (.inr (.inl i₀)) + b (.inr (.inl i₁))) = 0) :
    proj n K (rankOne (b (.inr (.inl i₀)) + b (.inr (.inl i₁)))
        (dualVec b (.inl i₁) - dualVec b (.inl i₀)) h) ∈
      closure {c : projectiveSL n K | conjAut n K s c = c ∧ Odd (orderOf c)} := by
  classical
  set d := leviElt b h01.symm with hd
  have hconj : d * rankOne (b (.inr (.inl i₀))) (dualVec b (.inl i₁)) h₀ * d⁻¹ =
      rankOne (b (.inr (.inl i₀)) + b (.inr (.inl i₁)))
        (dualVec b (.inl i₁) - dualVec b (.inl i₀)) h := by
    rw [mul_inv_eq_iff_eq_mul]
    refine mul_rankOne_eq_rankOne_mul d h₀ h ?_
    rw [hd, coe_leviElt]
    congr 1
    · simp [leviQ, add_mulVec, vecMulVec_mulVec', dualVec_dotProduct_basis]
    · simp [leviQ, vecMul_add, vecMul_vecMulVec, dualVec_dotProduct_basis, h01.symm,
        sub_dotProduct]
  have hfix : conjAut n K s (proj n K d) = proj n K d :=
    conjAut_proj_eq_of_mem (leviElt_mem b hbX hbL h01.symm)
  have := mul_mul_inv_mem_closure_odd_fixed hfix hD
  rwa [← map_mul, ← map_inv, ← map_mul, hconj] at this

section Torus

variable {ι : Type*} [DecidableEq ι] (b' : Module.Basis ι K (Fin n → K))

@[expose] def dilMat (k : ι) (c : K) : Matrix (Fin n) (Fin n) K :=
  1 + vecMulVec ((c - 1) • b' k) (dualVec b' k)

theorem dilMat_mulVec_basis (k m : ι) (c : K) :
    dilMat b' k c *ᵥ b' m = (if m = k then c else 1) • b' m := by
  rw [dilMat, add_mulVec, one_mulVec, vecMulVec_mulVec', dualVec_dotProduct_basis]
  split_ifs with hmk
  · subst hmk
    rw [one_smul, sub_smul, one_smul, add_sub_cancel]
  · rw [zero_smul, add_zero, one_smul]

theorem dualVec_vecMul_dilMat (m k : ι) (c : K) :
    dualVec b' m ᵥ* dilMat b' k c = (if m = k then c else 1) • dualVec b' m := by
  rw [dilMat, vecMul_add, vecMul_one, vecMul_vecMulVec, dotProduct_smul,
    dualVec_dotProduct_basis]
  split_ifs with hkm hmk hmk
  · subst hkm
    rw [smul_eq_mul, mul_one, sub_smul, one_smul, add_sub_cancel]
  · exact absurd hkm.symm hmk
  · exact absurd hmk.symm hkm
  · rw [smul_zero, zero_smul, add_zero, one_smul]

theorem det_dilMat (k : ι) (c : K) : det (dilMat b' k c) = c := by
  rw [dilMat, det_one_add_vecMulVec, dotProduct_smul, dualVec_dotProduct_basis, ite_eq_left rfl,
    smul_eq_mul, mul_one, add_sub_cancel]

end Torus

variable {i₀ i₁ : Fin ℓ}

@[expose] def torusMat (i₀ i₁ : Fin ℓ) (t : K) : Matrix (Fin n) (Fin n) K :=
  dilMat b (.inl i₀) t * dilMat b (.inr (.inl i₀)) t * dilMat b (.inl i₁) t⁻¹ *
    dilMat b (.inr (.inl i₁)) t⁻¹

@[expose] def torusCoeff (i₀ i₁ : Fin ℓ) (t : K) (i : Fin ℓ) : K :=
  (if i = i₀ then t else 1) * (if i = i₁ then t⁻¹ else 1)

theorem det_torusMat {t : K} (ht : t ≠ 0) : det (torusMat b i₀ i₁ t) = 1 := by
  rw [torusMat, det_mul, det_mul, det_mul, det_dilMat, det_dilMat, det_dilMat, det_dilMat]
  field_simp

@[expose] def torus (i₀ i₁ : Fin ℓ) {t : K} (ht : t ≠ 0) : SpecialLinearGroup (Fin n) K :=
  ⟨torusMat b i₀ i₁ t, det_torusMat b ht⟩

theorem coe_torus {t : K} (ht : t ≠ 0) :
    ((torus b i₀ i₁ ht : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      torusMat b i₀ i₁ t :=
  rfl

theorem torusMat_mulVec_inl (t : K) (i : Fin ℓ) :
    torusMat b i₀ i₁ t *ᵥ b (.inl i) = torusCoeff i₀ i₁ t i • b (.inl i) := by
  classical
  simp only [torusMat, ← mulVec_mulVec, dilMat_mulVec_basis, mulVec_smul, smul_smul,
    Sum.inl.injEq, reduceCtorEq, ite_false, one_mul, torusCoeff]
  congr 1
  ring

theorem torusMat_mulVec_inr (t : K) (i : Fin ℓ) :
    torusMat b i₀ i₁ t *ᵥ b (.inr (.inl i)) = torusCoeff i₀ i₁ t i • b (.inr (.inl i)) := by
  classical
  simp only [torusMat, ← mulVec_mulVec, dilMat_mulVec_basis, mulVec_smul, smul_smul,
    Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq, ite_false, mul_one, one_mul, torusCoeff]
  congr 1
  ring

theorem dualVec_inl_vecMul_torusMat (t : K) (i : Fin ℓ) :
    dualVec b (.inl i) ᵥ* torusMat b i₀ i₁ t = torusCoeff i₀ i₁ t i • dualVec b (.inl i) := by
  classical
  simp only [torusMat, ← vecMul_vecMul, dualVec_vecMul_dilMat, smul_vecMul, smul_smul,
    Sum.inl.injEq, reduceCtorEq, ite_false, mul_one, torusCoeff]

theorem dualVec_inr_vecMul_torusMat (t : K) (i : Fin ℓ) :
    dualVec b (.inr (.inl i)) ᵥ* torusMat b i₀ i₁ t =
      torusCoeff i₀ i₁ t i • dualVec b (.inr (.inl i)) := by
  classical
  simp only [torusMat, ← vecMul_vecMul, dualVec_vecMul_dilMat, smul_vecMul, smul_smul,
    Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq, ite_false, mul_one, one_mul, torusCoeff]

theorem torusCoeff_left (h01 : i₀ ≠ i₁) (t : K) : torusCoeff i₀ i₁ t i₀ = t := by
  simp [torusCoeff, h01]

theorem torusCoeff_right (h01 : i₀ ≠ i₁) (t : K) : torusCoeff i₀ i₁ t i₁ = t⁻¹ := by
  simp [torusCoeff, h01.symm]

theorem matrix_eq_of_mulVec_basis {ι : Type*} (b' : Module.Basis ι K (Fin n → K))
    {M M' : Matrix (Fin n) (Fin n) K} (h : ∀ m, M *ᵥ b' m = M' *ᵥ b' m) : M = M' :=
  Matrix.toLin'.injective (b'.ext fun m => by
    rw [Matrix.toLin'_apply, Matrix.toLin'_apply, h m])

variable {s : GL (Fin n) K}

theorem mem_comap_centralizer_of_mul_eq {g : SpecialLinearGroup (Fin n) K}
    (hg : (g : Matrix (Fin n) (Fin n) K) * ((s : Matrix (Fin n) (Fin n) K) - 1) =
      ((s : Matrix (Fin n) (Fin n) K) - 1) * (g : Matrix (Fin n) (Fin n) K)) :
    g ∈ (centralizer {s}).comap (SpecialLinearGroup.toGL :
      SpecialLinearGroup (Fin n) K →* GL (Fin n) K) := by
  have hQ : ((g : Matrix (Fin n) (Fin n) K) - 1) * ((s : Matrix (Fin n) (Fin n) K) - 1) =
      ((s : Matrix (Fin n) (Fin n) K) - 1) * ((g : Matrix (Fin n) (Fin n) K) - 1) := by
    rw [Matrix.sub_mul, Matrix.one_mul, hg, Matrix.mul_sub, Matrix.mul_one]
  exact mem_comap_centralizer_of_coe (by rw [add_sub_cancel]) hQ

theorem torus_mem_comap_centralizer
    (hbX : ∀ i, ((s : Matrix (Fin n) (Fin n) K) - 1) *ᵥ b (.inl i) = b (.inr (.inl i)))
    (hbL : ∀ k, ((s : Matrix (Fin n) (Fin n) K) - 1) *ᵥ b (.inr k) = 0) {t : K} (ht : t ≠ 0) :
    torus b i₀ i₁ ht ∈ (centralizer {s}).comap (SpecialLinearGroup.toGL :
      SpecialLinearGroup (Fin n) K →* GL (Fin n) K) := by
  refine mem_comap_centralizer_of_mul_eq (matrix_eq_of_mulVec_basis b fun m => ?_)
  rw [← mulVec_mulVec, ← mulVec_mulVec, coe_torus]
  rcases m with i | k | k
  · rw [hbX, torusMat_mulVec_inr, torusMat_mulVec_inl, mulVec_smul, hbX]
  · rw [hbL, mulVec_zero, torusMat_mulVec_inr, mulVec_smul, hbL, smul_zero]
  · exact k.elim0

@[expose] def leviT (h01 : i₀ ≠ i₁) (c : K) : SpecialLinearGroup (Fin n) K :=
  rankOne (c • b (.inl i₀)) (dualVec b (.inl i₁)) (by
      rw [dotProduct_smul, dualVec_inl_dotProduct_inl, ite_eq_right h01, smul_zero]) *
    rankOne (c • b (.inr (.inl i₀))) (dualVec b (.inr (.inl i₁))) (by
      rw [dotProduct_smul, dualVec_inr_dotProduct_inr, ite_eq_right h01, smul_zero])

theorem coe_leviT (h01 : i₀ ≠ i₁) (c : K) :
    ((leviT b h01 c : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      1 + c • leviQ b i₀ i₁ := by
  classical
  change (1 + vecMulVec (c • b (.inl i₀)) (dualVec b (.inl i₁))) *
    (1 + vecMulVec (c • b (.inr (.inl i₀))) (dualVec b (.inr (.inl i₁)))) = _
  rw [Matrix.add_mul, Matrix.one_mul, Matrix.mul_add, Matrix.mul_one, vecMulVec_mul_vecMulVec,
    dotProduct_smul, dualVec_inl_dotProduct_inr, smul_zero, zero_smul, vecMulVec_zero, add_zero]
  simp only [leviQ, smul_add, smul_vecMulVec]
  abel

theorem leviT_mul_inv (h01 : i₀ ≠ i₁) (c d : K) :
    leviT b h01 c * (leviT b h01 d)⁻¹ = leviT b h01 (c - d) := by
  rw [mul_inv_eq_iff_eq_mul]
  refine sl_ext_of_coe ?_
  change ((leviT b h01 c : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) =
    ((leviT b h01 (c - d) : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) *
      ((leviT b h01 d : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K)
  rw [coe_leviT, coe_leviT, coe_leviT, Matrix.add_mul,
    Matrix.one_mul, Matrix.mul_add, Matrix.mul_one, smul_mul_smul_comm, leviQ_mul_self b h01,
    smul_zero, add_zero, sub_smul]
  abel

theorem leviT_mem_comap_centralizer
    (hbX : ∀ i, ((s : Matrix (Fin n) (Fin n) K) - 1) *ᵥ b (.inl i) = b (.inr (.inl i)))
    (hbL : ∀ k, ((s : Matrix (Fin n) (Fin n) K) - 1) *ᵥ b (.inr k) = 0) (h01 : i₀ ≠ i₁)
    (c : K) :
    leviT b h01 c ∈ (centralizer {s}).comap (SpecialLinearGroup.toGL :
      SpecialLinearGroup (Fin n) K →* GL (Fin n) K) := by
  have hQ : leviQ b i₀ i₁ * ((s : Matrix (Fin n) (Fin n) K) - 1) =
      ((s : Matrix (Fin n) (Fin n) K) - 1) * leviQ b i₀ i₁ := by
    rw [leviQ, Matrix.add_mul, Matrix.mul_add, vecMulVec_mul, vecMulVec_mul, mul_vecMulVec,
      mul_vecMulVec, dualVec_inl_vecMul b hbX hbL, dualVec_inr_inl_vecMul b hbX hbL, hbX, hbL,
      vecMulVec_zero, zero_vecMulVec, zero_add, add_zero]
  exact mem_comap_centralizer_of_coe (coe_leviT b h01 c) (by
    rw [Matrix.smul_mul, Matrix.mul_smul, hQ])

theorem torus_mul_rankOne_left (h01 : i₀ ≠ i₁) {t : K} (ht : t ≠ 0) (c : K) (h h') :
    torus b i₀ i₁ ht * rankOne (c • b (.inr (.inl i₀))) (dualVec b (.inl i₁)) h =
      rankOne ((t ^ 2 * c) • b (.inr (.inl i₀))) (dualVec b (.inl i₁)) h' *
        torus b i₀ i₁ ht := by
  refine mul_rankOne_eq_rankOne_mul _ h h' ?_
  rw [coe_torus, mulVec_smul, torusMat_mulVec_inr, dualVec_inl_vecMul_torusMat,
    torusCoeff_left h01, torusCoeff_right h01]
  simp only [smul_vecMulVec, vecMulVec_smul, smul_smul]
  congr 1
  field_simp

theorem torus_mul_rankOne_right (h01 : i₀ ≠ i₁) {t : K} (ht : t ≠ 0) (c : K) (h h') :
    torus b i₀ i₁ ht * rankOne (c • b (.inr (.inl i₁))) (dualVec b (.inl i₀)) h =
      rankOne ((t⁻¹ ^ 2 * c) • b (.inr (.inl i₁))) (dualVec b (.inl i₀)) h' *
        torus b i₀ i₁ ht := by
  refine mul_rankOne_eq_rankOne_mul _ h h' ?_
  rw [coe_torus, mulVec_smul, torusMat_mulVec_inr, dualVec_inl_vecMul_torusMat,
    torusCoeff_left h01, torusCoeff_right h01]
  simp only [smul_vecMulVec, vecMulVec_smul, smul_smul]
  congr 1
  field_simp

theorem torus_mul_leviT (h01 : i₀ ≠ i₁) {t : K} (ht : t ≠ 0) (c : K) :
    torus b i₀ i₁ ht * leviT b h01 c = leviT b h01 (t ^ 2 * c) * torus b i₀ i₁ ht := by
  refine sl_ext_of_coe ?_
  change torusMat b i₀ i₁ t * ((leviT b h01 c : SpecialLinearGroup (Fin n) K) :
      Matrix (Fin n) (Fin n) K) =
    ((leviT b h01 (t ^ 2 * c) : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) *
      torusMat b i₀ i₁ t
  rw [coe_leviT, coe_leviT,
    Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul, Matrix.mul_smul,
    Matrix.smul_mul, leviQ, Matrix.mul_add, Matrix.add_mul, mul_vecMulVec, mul_vecMulVec,
    vecMulVec_mul, vecMulVec_mul, torusMat_mulVec_inl, torusMat_mulVec_inr,
    dualVec_inl_vecMul_torusMat, dualVec_inr_vecMul_torusMat, torusCoeff_left h01,
    torusCoeff_right h01]
  simp only [smul_vecMulVec, vecMulVec_smul, smul_add, smul_smul]
  congr 3 <;> field_simp

@[expose] def twoSet (h01 : i₀ ≠ i₁) : Set (SpecialLinearGroup (Fin n) K) :=
  {g | (∃ (c : K) (h : dualVec b (.inl i₁) ⬝ᵥ (c • b (.inr (.inl i₀))) = 0),
      g = rankOne (c • b (.inr (.inl i₀))) (dualVec b (.inl i₁)) h) ∨
    (∃ (c : K) (h : dualVec b (.inl i₀) ⬝ᵥ (c • b (.inr (.inl i₁))) = 0),
      g = rankOne (c • b (.inr (.inl i₁))) (dualVec b (.inl i₀)) h) ∨
    ∃ c : K, g = leviT b h01 c}

theorem closure_twoSet_le
    (hbX : ∀ i, ((s : Matrix (Fin n) (Fin n) K) - 1) *ᵥ b (.inl i) = b (.inr (.inl i)))
    (hbL : ∀ k, ((s : Matrix (Fin n) (Fin n) K) - 1) *ᵥ b (.inr k) = 0) (h01 : i₀ ≠ i₁) :
    closure (twoSet b h01) ≤ (centralizer {s}).comap (SpecialLinearGroup.toGL :
      SpecialLinearGroup (Fin n) K →* GL (Fin n) K) := by
  rw [closure_le]
  rintro _ (⟨c, h, rfl⟩ | ⟨c, h, rfl⟩ | ⟨c, rfl⟩)
  · exact rankOne_inr_mem_comap_centralizer b hbX hbL i₁ i₀ c h
  · exact rankOne_inr_mem_comap_centralizer b hbX hbL i₀ i₁ c h
  · exact leviT_mem_comap_centralizer b hbX hbL h01 c

theorem closure_twoSet_le_commutator
    (hbX : ∀ i, ((s : Matrix (Fin n) (Fin n) K) - 1) *ᵥ b (.inl i) = b (.inr (.inl i)))
    (hbL : ∀ k, ((s : Matrix (Fin n) (Fin n) K) - 1) *ᵥ b (.inr k) = 0) (h01 : i₀ ≠ i₁)
    {t : K} (ht : t ≠ 0) (ht2 : t ^ 2 ≠ 1) :
    closure (twoSet b h01) ≤ ⁅closure (twoSet b h01), (centralizer {s}).comap
      (SpecialLinearGroup.toGL : SpecialLinearGroup (Fin n) K →* GL (Fin n) K)⁆ := by
  have hT := torus_mem_comap_centralizer b (i₀ := i₀) (i₁ := i₁) hbX hbL ht
  have h1 : (1 : K) - t ^ 2 ≠ 0 := sub_ne_zero.mpr (Ne.symm ht2)
  have h2 : (1 : K) - t⁻¹ ^ 2 ≠ 0 := by
    rw [sub_ne_zero, ne_comm, inv_pow, Ne, inv_eq_one]
    exact ht2
  have hdot : ∀ i j : Fin ℓ, ∀ c : K, dualVec b (.inl i) ⬝ᵥ (c • b (.inr (.inl j))) = 0 :=
    fun i j c => by rw [dotProduct_smul, dualVec_inl_dotProduct_inr, smul_zero]
  rw [closure_le]
  rintro _ (⟨c, h, rfl⟩ | ⟨c, h, rfl⟩ | ⟨c, rfl⟩)
  · set c' := (1 - t ^ 2)⁻¹ * c with hc'
    have e : ⁅rankOne (c' • b (.inr (.inl i₀))) (dualVec b (.inl i₁)) (hdot _ _ _),
        torus b i₀ i₁ ht⁆ = rankOne (c • b (.inr (.inl i₀))) (dualVec b (.inl i₁)) h := by
      rw [commutatorElement_eq_mul_inv_of_mul_eq (torus_mul_rankOne_left b h01 ht c' _
        (hdot _ _ (t ^ 2 * c'))), rankOne_smul_mul_inv _ _ _ _ _ _ (hdot _ _ _)]
      exact rankOne_eq (by rw [hc']; congr 1; field_simp) rfl _ _
    rw [← e]
    exact commutator_mem_commutator (subset_closure (Or.inl ⟨c', hdot _ _ _, rfl⟩)) hT
  · set c' := (1 - t⁻¹ ^ 2)⁻¹ * c with hc'
    have e : ⁅rankOne (c' • b (.inr (.inl i₁))) (dualVec b (.inl i₀)) (hdot _ _ _),
        torus b i₀ i₁ ht⁆ = rankOne (c • b (.inr (.inl i₁))) (dualVec b (.inl i₀)) h := by
      rw [commutatorElement_eq_mul_inv_of_mul_eq (torus_mul_rankOne_right b h01 ht c' _
        (hdot _ _ (t⁻¹ ^ 2 * c'))), rankOne_smul_mul_inv _ _ _ _ _ _ (hdot _ _ _)]
      exact rankOne_eq (by rw [hc']; congr 1; field_simp) rfl _ _
    rw [← e]
    exact commutator_mem_commutator
      (subset_closure (Or.inr (Or.inl ⟨c', hdot _ _ _, rfl⟩))) hT
  · set c' := (1 - t ^ 2)⁻¹ * c with hc'
    have e : ⁅leviT b h01 c', torus b i₀ i₁ ht⁆ = leviT b h01 c := by
      rw [commutatorElement_eq_mul_inv_of_mul_eq (torus_mul_leviT b h01 ht c'), leviT_mul_inv]
      congr 1
      rw [hc']
      field_simp
    rw [← e]
    exact commutator_mem_commutator (subset_closure (Or.inr (Or.inr ⟨c', rfl⟩))) hT

theorem twoSet_mem_closure_odd_fixed [Finite K]
    (hbX : ∀ i, ((s : Matrix (Fin n) (Fin n) K) - 1) *ᵥ b (.inl i) = b (.inr (.inl i)))
    (hbL : ∀ k, ((s : Matrix (Fin n) (Fin n) K) - 1) *ᵥ b (.inr k) = 0) (h01 : i₀ ≠ i₁)
    {t : K} (ht : t ≠ 0) (ht2 : t ^ 2 ≠ 1) {g : SpecialLinearGroup (Fin n) K}
    (hg : g ∈ twoSet b h01) :
    proj n K g ∈ closure {c : projectiveSL n K | conjAut n K s c = c ∧ Odd (orderOf c)} := by
  have hD : (closure (twoSet b h01)).map (proj n K) ≤
      closure {c : projectiveSL n K | conjAut n K s c = c ∧ Odd (orderOf c)} := by
    refine le_closure_odd_fixed_of_le_commutator
      (map_mono (closure_twoSet_le b hbX hbL h01)) ?_ ?_
    · rintro _ ⟨g, hg, rfl⟩
      exact conjAut_proj_eq_of_mem hg
    · rw [← map_commutator]
      exact map_mono (closure_twoSet_le_commutator b hbX hbL h01 ht ht2)
  exact hD (mem_map_of_mem _ (subset_closure hg))

end Supply

end CFSG.SeitzReduction.ClassicalLinear.Lagrangian
