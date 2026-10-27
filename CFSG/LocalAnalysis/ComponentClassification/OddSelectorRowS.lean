module

public import CFSG.LocalAnalysis.ComponentClassification.OddSelectorRowSFacts
public import CFSG.LocalAnalysis.ComponentClassification.OddSelectorAut
public import CFSG.LocalAnalysis.ComponentClassification.OddSelectorInner

public noncomputable section

namespace CFSG.ComponentClassification.OddSelector

open Subgroup Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial LinearFlag
open CFSG.ComponentClassification.UnbalancedCatalog CFSG.ComponentClassification.OutcomeLocal
open CFSG.ComponentClassification.CatalogueBProjectiveQuadratic Polynomial

section Setup

variable {k : Type} [Field k] {m : ℕ} {B : GL (Fin m) k} {μ : kˣ} [Fact (¬ IsSquare (μ : k))]

@[expose] def rowSPsi (hsq : B ^ 2 = GeneralLinearGroup.scalar (Fin m) μ)
    (hd : letI := matrixModule B μ hsq; Module.finrank (extension (μ : k)) (Fin m → k) = 2) :
    (Fin 2 → extension (μ : k)) ≃ₗ[k] (Fin m → k) :=
  letI := matrixModule B μ hsq
  haveI := matrixModule_scalarTower B μ hsq
  haveI := matrixModule_finite B μ hsq
  ((Module.finBasisOfFinrankEq (extension (μ : k)) (Fin m → k) hd).equivFun.restrictScalars
    k).symm

theorem rowSPsi_smul (hsq : B ^ 2 = GeneralLinearGroup.scalar (Fin m) μ)
    (hd : letI := matrixModule B μ hsq; Module.finrank (extension (μ : k)) (Fin m → k) = 2)
    (e : extension (μ : k)) (x : Fin 2 → extension (μ : k)) :
    letI := matrixModule B μ hsq
    rowSPsi hsq hd (e • x) = e • rowSPsi hsq hd x := by
  let := matrixModule B μ hsq
  have := matrixModule_scalarTower B μ hsq
  have := matrixModule_finite B μ hsq
  exact (Module.finBasisOfFinrankEq (extension (μ : k)) (Fin m → k) hd).equivFun.symm.map_smul e x

theorem rowSU_rowSPsi (hsq : B ^ 2 = GeneralLinearGroup.scalar (Fin m) μ)
    (hd : letI := matrixModule B μ hsq; Module.finrank (extension (μ : k)) (Fin m → k) = 2) :
    rowSU μ (rowSPsi hsq hd) = B := by
  let := matrixModule B μ hsq
  apply eq_of_mulVec_eq
  intro v
  obtain ⟨x, rfl⟩ := (rowSPsi hsq hd).surjective v
  rw [rowSU, rowSPi_mulVec_apply, GeneralLinearGroup.coe_scalar, scalar_apply]
  have h1 : (diagonal fun _ => ((rootUnit μ : (extension (μ : k))ˣ) : extension (μ : k))) *ᵥ x =
      AdjoinRoot.root (quadraticPolynomial (μ : k)) • x := by
    ext i
    simp [mulVec_diagonal, coe_rootUnit]
  rw [h1, rowSPsi_smul, matrixModule_root_smul]

theorem range_rowSPi (hsq : B ^ 2 = GeneralLinearGroup.scalar (Fin m) μ)
    (hd : letI := matrixModule B μ hsq; Module.finrank (extension (μ : k)) (Fin m → k) = 2) :
    (rowSPi μ (rowSPsi hsq hd)).range = centralizer {B} := by
  ext X
  rw [mem_centralizer_singleton_iff]
  constructor
  · rintro ⟨g, rfl⟩
    have := rowSPi_commute_rowSU μ (rowSPsi hsq hd) g
    rw [rowSU_rowSPsi] at this
    exact this
  · intro hX
    have hX' : X * rowSU μ (rowSPsi hsq hd) = rowSU μ (rowSPsi hsq hd) * X := by
      rw [rowSU_rowSPsi]
      exact hX
    obtain ⟨g, rfl⟩ := exists_rowSPi_of_commute μ (rowSPsi hsq hd) hX'
    exact ⟨g, rfl⟩

@[expose] def rowSCentralizerEquiv (hsq : B ^ 2 = GeneralLinearGroup.scalar (Fin m) μ)
    (hd : letI := matrixModule B μ hsq; Module.finrank (extension (μ : k)) (Fin m → k) = 2) :
    centralizer {B} ≃* GL (Fin 2) (extension (μ : k)) :=
  ((MonoidHom.ofInjective (rowSPi_injective μ (rowSPsi hsq hd))).trans
    (MulEquiv.subgroupCongr (range_rowSPi hsq hd))).symm

theorem rowSCentralizerEquiv_symm_apply (hsq : B ^ 2 = GeneralLinearGroup.scalar (Fin m) μ)
    (hd : letI := matrixModule B μ hsq; Module.finrank (extension (μ : k)) (Fin m → k) = 2)
    (g : GL (Fin 2) (extension (μ : k))) :
    ((rowSCentralizerEquiv hsq hd).symm g : GL (Fin m) k) = rowSPi μ (rowSPsi hsq hd) g := rfl

end Setup

section Component

variable {k : Type} [Field k] [Finite k] {m : ℕ} {B : GL (Fin m) k} {μ : kˣ}
  [Fact (¬ IsSquare (μ : k))]

theorem card_extension (μ : kˣ) : Nat.card (extension (μ : k)) = Nat.card k ^ 2 := by
  have : Finite (extension (μ : k)) := CatalogueBProjectiveInvolution.quadraticExtension_finite _
  let : Fintype k := Fintype.ofFinite k
  let : Fintype (extension (μ : k)) := Fintype.ofFinite _
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := k),
    extension_finrank]

theorem rowS_lift_eq (htwo : (2 : k) ≠ 0) (hsq : B ^ 2 = GeneralLinearGroup.scalar (Fin m) μ)
    (hd : letI := matrixModule B μ hsq; Module.finrank (extension (μ : k)) (Fin m → k) = 2)
    {Xh : Subgroup (GL (Fin m) k)} (hXh : CFSG.Assembly.IsComponentOf Xh (centralizer {B})) :
    Xh = ((rowSPi μ (rowSPsi hsq hd)).comp SpecialLinearGroup.toGL).range := by
  have hL' : CFSG.IsComponent (Xh.subgroupOf (centralizer {B})) :=
    (isComponentOf_iff_isComponent_subgroupOf hXh.1).mp hXh
  set e := rowSCentralizerEquiv hsq hd with he
  have hL'' := isComponent_map_of_isComponent e hL'
  set L'' := (Xh.subgroupOf (centralizer {B})).map e.toMonoidHom with hL''def
  have : Group.IsPerfect L'' := hL''.1.1
  have : Nontrivial L'' := CFSG.LocalCores.isQuasisimple_nontrivial hL''.1
  have : Finite (extension (μ : k)) := CatalogueBProjectiveInvolution.quadraticExtension_finite _
  have hK3 := ProjectiveEigenspace.three_le_card_of_two_ne_zero htwo
  have hE9 : 9 ≤ Nat.card (extension (μ : k)) := by
    rw [card_extension]
    nlinarith
  have hSL : L'' = CatalogueBGeneralLinear.specialLinearRange 2 (extension (μ : k)) :=
    CatalogueBGeneralLinear.perfect_subnormal_eq_specialLinearRange 2 (extension (μ : k)) le_rfl
      (Or.inr (by omega)) (Or.inr (by omega)) L'' hL''.2
  ext x
  constructor
  · intro hx
    have hmem : e ⟨x, hXh.1 hx⟩ ∈ L'' := ⟨⟨x, hXh.1 hx⟩, hx, rfl⟩
    rw [hSL] at hmem
    obtain ⟨g, hg⟩ := hmem
    refine ⟨g, ?_⟩
    rw [MonoidHom.comp_apply, hg, ← rowSCentralizerEquiv_symm_apply hsq hd, ← he,
      MulEquiv.symm_apply_apply]
  · rintro ⟨g, rfl⟩
    have hmem : SpecialLinearGroup.toGL g ∈ L'' := by
      rw [hSL]
      exact ⟨g, rfl⟩
    obtain ⟨y, hy, hyg⟩ := hmem
    have : (e.symm (SpecialLinearGroup.toGL g) : GL (Fin m) k) ∈ Xh := by
      rw [← hyg]
      change ((e.symm (e y)) : GL (Fin m) k) ∈ Xh
      rw [MulEquiv.symm_apply_apply]
      exact hy
    rw [he, rowSCentralizerEquiv_symm_apply] at this
    exact this

end Component

theorem map_mulAut_one_eq {G : Type*} [Group G] (H : Subgroup G) :
    H.map (1 : MulAut G).toMonoidHom = H := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact hy
  · intro hx
    exact ⟨x, hx, rfl⟩

section Row

variable {k : Type} [Field k] [Finite k] {μ : kˣ} [Fact (¬ IsSquare (μ : k))]
  (Ψ : (Fin 2 → extension (μ : k)) ≃ₗ[k] (Fin 4 → k))

omit [Finite k] in
theorem map_conj_mem_normFourthPowers {g : GL (Fin 2) (extension (μ : k))}
    (hg : g ∈ normFourthPowers μ) :
    GeneralLinearGroup.map ((extensionConj μ : extension (μ : k) ≃ₐ[k] _) :
      extension (μ : k) →+* extension (μ : k)) g ∈ normFourthPowers μ := by
  rw [mem_normFourthPowers] at hg ⊢
  obtain ⟨c, hc⟩ := hg
  refine ⟨c, ?_⟩
  change Algebra.norm k (((g : Matrix (Fin 2) (Fin 2) (extension (μ : k))).map
    ((extensionConj μ : extension (μ : k) ≃ₐ[k] _) :
      extension (μ : k) →+* extension (μ : k))).det) = _
  have h := RingHom.map_det ((extensionConj μ : extension (μ : k) ≃ₐ[k] _) :
    extension (μ : k) →+* extension (μ : k)) (g : Matrix (Fin 2) (Fin 2) (extension (μ : k)))
  rw [RingHom.mapMatrix_apply] at h
  rw [← h]
  change Algebra.norm k (extensionConj μ _) = _
  rw [Algebra.norm_eq_of_algEquiv, hc]

theorem conjAut_rowSKappa_not_mem (htwo : (2 : k) ≠ 0) :
    conjAut 4 k (rowSKappa μ Ψ) ∉ rowST μ Ψ := by
  rintro ⟨g, -, hg⟩
  obtain ⟨c, hc⟩ := (conjAut_eq_conjAut_iff' (by norm_num) _ _).mp hg.symm
  have h1 : rowSKappa μ Ψ * rowSU μ Ψ = rowSU μ Ψ * rowSKappa μ Ψ := by
    rw [hc, mul_assoc, rowSPi_commute_rowSU, ← mul_assoc,
      GeneralLinearGroup.scalar_commute c (rowSU μ Ψ), mul_assoc]
  rw [rowSKappa_mul_rowSU, mul_assoc] at h1
  have h2 : GeneralLinearGroup.scalar (Fin 4) (-1 : kˣ) = 1 := by
    have h1' : GeneralLinearGroup.scalar (Fin 4) (-1 : kˣ) * (rowSU μ Ψ * rowSKappa μ Ψ) =
        1 * (rowSU μ Ψ * rowSKappa μ Ψ) := by rw [one_mul]; exact h1
    exact mul_right_cancel h1'
  have h3 := congrArg (fun X : GL (Fin 4) k => (X : Matrix (Fin 4) (Fin 4) k) 0 0) h2
  simp at h3
  apply htwo
  linear_combination -h3

theorem orderOf_conjAut_rowSKappa (htwo : (2 : k) ≠ 0) :
    orderOf (conjAut 4 k (rowSKappa μ Ψ)) = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine orderOf_eq_prime ?_ ?_
  · rw [← map_pow, sq, rowSKappa_mul_self, map_one]
  · intro h1
    apply conjAut_rowSKappa_not_mem Ψ htwo
    rw [h1]
    exact one_mem _

omit [Finite k] in
theorem conjAut_rowSKappa_mem_normalizer :
    conjAut 4 k (rowSKappa μ Ψ) ∈ normalizer (rowST μ Ψ : Set (MulAut (projectiveSL 4 k))) := by
  have hκ : (rowSKappa μ Ψ)⁻¹ = rowSKappa μ Ψ := inv_eq_of_mul_eq_one_right (rowSKappa_mul_self μ Ψ)
  have hfwd : ∀ y ∈ rowST μ Ψ, conjAut 4 k (rowSKappa μ Ψ) * y * (conjAut 4 k (rowSKappa μ Ψ))⁻¹ ∈
      rowST μ Ψ := by
    rintro _ ⟨g, hg, rfl⟩
    refine ⟨_, map_conj_mem_normFourthPowers hg, ?_⟩
    rw [MonoidHom.comp_apply, MonoidHom.comp_apply, ← rowSKappa_conj_rowSPi, ← map_inv, hκ,
      map_mul, map_mul]
  rw [mem_normalizer_iff]
  intro y
  refine ⟨hfwd y, fun hy => ?_⟩
  have := hfwd _ hy
  have hc2 : conjAut 4 k (rowSKappa μ Ψ) * conjAut 4 k (rowSKappa μ Ψ) = 1 := by
    rw [← map_mul, rowSKappa_mul_self, map_one]
  have hci : (conjAut 4 k (rowSKappa μ Ψ))⁻¹ = conjAut 4 k (rowSKappa μ Ψ) :=
    inv_eq_of_mul_eq_one_right hc2
  rw [hci] at this
  have e : conjAut 4 k (rowSKappa μ Ψ) * (conjAut 4 k (rowSKappa μ Ψ) * y *
      conjAut 4 k (rowSKappa μ Ψ)) * conjAut 4 k (rowSKappa μ Ψ) = y := by
    rw [← mul_assoc, ← mul_assoc, hc2, one_mul, mul_assoc, hc2, mul_one]
  rwa [e] at this

theorem rowST_inf_zpowers (htwo : (2 : k) ≠ 0) :
    rowST μ Ψ ⊓ zpowers (conjAut 4 k (rowSKappa μ Ψ)) = ⊥ := by
  rw [eq_bot_iff]
  rintro x ⟨hx, hxz⟩
  obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp hxz
  rw [mem_bot, ← zpow_mod_orderOf, orderOf_conjAut_rowSKappa Ψ htwo]
  rcases Int.emod_two_eq_zero_or_one n with h | h
  · rw [Nat.cast_ofNat, h, zpow_zero]
  · exfalso
    rw [← zpow_mod_orderOf, orderOf_conjAut_rowSKappa Ψ htwo, Nat.cast_ofNat, h, zpow_one] at hx
    exact conjAut_rowSKappa_not_mem Ψ htwo hx

omit [Finite k] in
theorem rowST_le : rowST μ Ψ ≤
    OuterAutomorphisms.inner (projectiveSL 4 k) ⊓ centralizer {conjAut 4 k (rowSU μ Ψ)} := by
  rintro _ ⟨g, hg, rfl⟩
  rw [SetLike.mem_coe, mem_normFourthPowers] at hg
  obtain ⟨c, hc⟩ := hg
  refine mem_inf.mpr ⟨conjAut_mem_inner (c := c) (Units.ext ?_), ?_⟩
  · rw [GeneralLinearGroup.val_det_apply, Units.val_pow_eq_pow_val, det_rowSPi, hc]
  · rw [MonoidHom.comp_apply, mem_centralizer_singleton_iff, ← map_mul, ← map_mul,
      rowSPi_commute_rowSU]

theorem inner_inf_centralizer_rowSU :
    OuterAutomorphisms.inner (projectiveSL 4 k) ⊓ centralizer {conjAut 4 k (rowSU μ Ψ)} =
      rowST μ Ψ ⊔ zpowers (conjAut 4 k (rowSKappa μ Ψ)) := by
  apply le_antisymm
  · intro α hα
    obtain ⟨hαI, hαC⟩ := mem_inf.mp hα
    obtain ⟨Y, rfl⟩ := exists_conjAut_of_mem_inner hαI
    set Y' := SpecialLinearGroup.toGL Y with hY'
    have hdet : GeneralLinearGroup.det Y' = 1 := Units.ext (by
      rw [GeneralLinearGroup.val_det_apply, hY', SpecialLinearGroup.coe_GL_coe_matrix, Y.2,
        Units.val_one])
    rw [mem_centralizer_singleton_iff_conj, ← map_inv, ← map_mul, ← map_mul,
      conjAut_eq_conjAut_iff' (by norm_num)] at hαC
    obtain ⟨c, hc⟩ := hαC
    have hs := rowSU_sq μ Ψ
    have hsc : ∀ X : GL (Fin 4) k, GeneralLinearGroup.scalar (Fin 4) c * X =
        X * GeneralLinearGroup.scalar (Fin 4) c := fun X => GeneralLinearGroup.scalar_commute c X
    have hμc : ∀ X : GL (Fin 4) k, GeneralLinearGroup.scalar (Fin 4) μ * X =
        X * GeneralLinearGroup.scalar (Fin 4) μ := fun X => GeneralLinearGroup.scalar_commute μ X
    have hc2 : c ^ 2 = 1 := by
      have h1 : GeneralLinearGroup.scalar (Fin 4) μ =
          GeneralLinearGroup.scalar (Fin 4) (c ^ 2) * GeneralLinearGroup.scalar (Fin 4) μ := by
        calc GeneralLinearGroup.scalar (Fin 4) μ =
              Y' * GeneralLinearGroup.scalar (Fin 4) μ * Y'⁻¹ := by rw [← hμc]; group
          _ = Y' * (rowSU μ Ψ * rowSU μ Ψ) * Y'⁻¹ := by rw [← sq, hs]
          _ = (Y' * rowSU μ Ψ * Y'⁻¹) * (Y' * rowSU μ Ψ * Y'⁻¹) := by group
          _ = (GeneralLinearGroup.scalar (Fin 4) c * rowSU μ Ψ) *
                (GeneralLinearGroup.scalar (Fin 4) c * rowSU μ Ψ) := by rw [hc]
          _ = GeneralLinearGroup.scalar (Fin 4) c * GeneralLinearGroup.scalar (Fin 4) c *
                (rowSU μ Ψ * rowSU μ Ψ) := by
              rw [mul_assoc (GeneralLinearGroup.scalar (Fin 4) c) (rowSU μ Ψ),
                ← mul_assoc (rowSU μ Ψ), ← hsc (rowSU μ Ψ)]
              group
          _ = _ := by rw [← sq, ← map_pow, ← sq, hs]
      have h2 : GeneralLinearGroup.scalar (Fin 4) (c ^ 2) = 1 := by
        have h1' : 1 * GeneralLinearGroup.scalar (Fin 4) μ =
            GeneralLinearGroup.scalar (Fin 4) (c ^ 2) * GeneralLinearGroup.scalar (Fin 4) μ := by
          rw [one_mul]; exact h1
        exact (mul_right_cancel h1').symm
      have h3 := congrArg (fun X : GL (Fin 4) k => (X : Matrix (Fin 4) (Fin 4) k) 0 0) h2
      simp only [GeneralLinearGroup.coe_scalar, scalar_apply, diagonal_apply_eq, Units.val_one,
        one_apply_eq] at h3
      exact Units.ext (by rw [Units.val_one]; exact h3)
    rcases Units.eq_or_eq_neg_of_sq_eq_sq c 1 (by rw [hc2, one_pow]) with rfl | rfl
    ·
      rw [map_one, one_mul] at hc
      have hYU : Y' * rowSU μ Ψ = rowSU μ Ψ * Y' := by
        calc Y' * rowSU μ Ψ = (Y' * rowSU μ Ψ * Y'⁻¹) * Y' := by group
          _ = rowSU μ Ψ * Y' := by rw [hc]
      obtain ⟨g, hg⟩ := exists_rowSPi_of_commute μ Ψ hYU
      refine mem_sup_left ⟨g, ?_, by rw [MonoidHom.comp_apply, ← hg]⟩
      rw [SetLike.mem_coe, mem_normFourthPowers]
      refine ⟨1, ?_⟩
      rw [← det_rowSPi μ Ψ, ← hg, ← GeneralLinearGroup.val_det_apply, hdet]
      simp
    ·
      have hYU : Y' * rowSU μ Ψ = GeneralLinearGroup.scalar (Fin 4) (-1) * rowSU μ Ψ * Y' := by
        calc Y' * rowSU μ Ψ = (Y' * rowSU μ Ψ * Y'⁻¹) * Y' := by group
          _ = _ := by rw [hc]
      obtain ⟨g, hg⟩ := exists_rowSPi_of_anticommute μ Ψ hYU
      rw [hg, map_mul]
      refine mul_mem (mem_sup_left ⟨g, ?_, rfl⟩) (mem_sup_right (mem_zpowers _))
      rw [SetLike.mem_coe, mem_normFourthPowers]
      refine ⟨1, ?_⟩
      have h1 := congrArg (fun X : GL (Fin 4) k => (X : Matrix (Fin 4) (Fin 4) k).det) hg
      simp only [Units.val_mul, det_mul, det_rowSKappa, mul_one, det_rowSPi] at h1
      rw [← h1, hY', SpecialLinearGroup.coe_GL_coe_matrix, Y.2]
      simp
  · refine sup_le (rowST_le Ψ) ?_
    rw [zpowers_le]
    refine ⟨conjAut_mem_inner (c := 1) (Units.ext ?_), conjAut_rowSKappa_mem_centralizer μ Ψ⟩
    rw [GeneralLinearGroup.val_det_apply, det_rowSKappa]
    simp

omit [Finite k] in
theorem toGL_neg_one :
    SpecialLinearGroup.toGL (-1 : SpecialLinearGroup (Fin 2) (extension (μ : k))) =
      GeneralLinearGroup.scalar (Fin 2)
        (Units.map (algebraMap k (extension (μ : k))).toMonoidHom (-1)) := by
  apply Units.ext
  ext i j
  rw [GeneralLinearGroup.coe_scalar, SpecialLinearGroup.coe_GL_coe_matrix]
  change -(1 : Matrix (Fin 2) (Fin 2) (extension (μ : k))) i j = _
  fin_cases i <;> fin_cases j <;> simp

theorem conjAut_rowSPi_sl_eq_one_iff (g : SpecialLinearGroup (Fin 2) (extension (μ : k))) :
    conjAut 4 k (rowSPi μ Ψ (SpecialLinearGroup.toGL g)) = 1 ↔ g = 1 ∨ g = -1 := by
  constructor
  · intro h1
    obtain ⟨c, hc⟩ := (conjAut_eq_one_iff (by norm_num) _).mp h1
    rw [← rowSPi_scalar μ Ψ c] at hc
    have hg := rowSPi_injective μ Ψ hc
    have hdet := congrArg GeneralLinearGroup.det hg
    rw [GeneralLinearGroup.det_scalar, Fintype.card_fin] at hdet
    have hdet1 : GeneralLinearGroup.det (SpecialLinearGroup.toGL g) = 1 := Units.ext (by
      rw [GeneralLinearGroup.val_det_apply, SpecialLinearGroup.coe_GL_coe_matrix, g.2,
        Units.val_one])
    rw [hdet1, ← map_pow] at hdet
    have hc2 : c ^ 2 = 1 := by
      have h3 : algebraMap k (extension (μ : k)) ((c ^ 2 : kˣ) : k) =
          algebraMap k (extension (μ : k)) 1 := by
        rw [map_one]
        simpa using congrArg Units.val hdet
      exact Units.ext ((algebraMap k (extension (μ : k))).injective h3)
    rcases Units.eq_or_eq_neg_of_sq_eq_sq c 1 (by rw [hc2, one_pow]) with rfl | rfl
    · left
      apply SpecialLinearGroup.toGL_injective
      rw [← hg, map_one, map_one, map_one]
    · right
      apply SpecialLinearGroup.toGL_injective
      rw [← hg, toGL_neg_one]
  · rintro (rfl | rfl)
    · rw [map_one, map_one, map_one]
    · rw [toGL_neg_one, rowSPi_scalar, conjAut_scalar]

omit [Finite k] in
theorem mem_scalars_two_iff (g : SpecialLinearGroup (Fin 2) (extension (μ : k))) :
    g ∈ scalars 2 (extension (μ : k)) ↔ g = 1 ∨ g = -1 := by
  rw [mem_scalars]
  constructor
  · rintro ⟨c, hc, hg⟩
    rcases Units.eq_or_eq_neg_of_sq_eq_sq c 1 (by rw [hc, one_pow]) with rfl | rfl
    · left
      ext i j
      have := congrFun (congrFun hg i) j
      fin_cases i <;> fin_cases j <;> simpa using this
    · right
      ext i j
      have := congrFun (congrFun hg i) j
      fin_cases i <;> fin_cases j <;> simpa using this
  · rintro (rfl | rfl)
    · refine ⟨1, one_pow 2, ?_⟩
      ext i j
      fin_cases i <;> fin_cases j <;> simp
    · refine ⟨-1, by rw [neg_one_sq], ?_⟩
      ext i j
      fin_cases i <;> fin_cases j <;> simp

end Row

theorem selectorRowS_of_inner {A : Type} [Group A] {W : Subgroup A} {a : A} {L : Subgroup A}
    {k : Type} [Field k] [Finite k] (htwo : (2 : k) ≠ 0)
    {ρ : A →* MulAut (projectiveSL 4 k)} (hinj : Function.Injective ρ)
    (hCA : (centralizer {a}).map ρ = ρ.range ⊓ centralizer {ρ a})
    (hCW : (W ⊓ centralizer {a}).map ρ =
      OuterAutomorphisms.inner (projectiveSL 4 k) ⊓ centralizer {ρ a})
    (hL₁ : CFSG.Assembly.IsComponentOf (L.map ρ)
      (OuterAutomorphisms.inner (projectiveSL 4 k) ⊓ centralizer {ρ a}))
    {B : GL (Fin 4) k} (hρa : ρ a = conjAut 4 k B) {μ : kˣ} (hμ : ¬ IsSquare (μ : k))
    (hsq : B ^ 2 = GeneralLinearGroup.scalar (Fin 4) μ) :
    SelectorRowS 4 k ρ W a L ∧
      ∃ (E : Type) (_ : Field E) (_ : Finite E), Nat.card E = Nat.card k ^ 2 ∧
        Nonempty (L ≃* projectiveSL 2 E) := by
  have : Fact (¬ IsSquare (μ : k)) := ⟨hμ⟩
  have hd : (letI := matrixModule B μ hsq;
      Module.finrank (extension (μ : k)) (Fin 4 → k) = 2) := by
    have h := matrixDimension_twice B μ hsq
    rw [Fintype.card_fin] at h
    change matrixDimension B μ hsq = 2
    omega
  set Ψ := rowSPsi hsq hd with hΨ
  have hU : rowSU μ Ψ = B := rowSU_rowSPsi hsq hd
  have hρa' : ρ a = conjAut 4 k (rowSU μ Ψ) := by rw [hU, hρa]
  have hid := map_mulAut_one_eq (G := MulAut (projectiveSL 4 k))
  have hc1 : MulAut.conj (conjAut 4 k 1) = 1 := by rw [map_one, map_one]
  have hcompEq : ∀ X, CFSG.Assembly.IsComponentOf X
      (OuterAutomorphisms.inner (projectiveSL 4 k) ⊓ centralizer {ρ a}) → X = rowSJ μ Ψ := by
    intro X hX
    rw [hρa] at hX
    obtain ⟨hXh, hmap, -⟩ := inner_component_lift (by norm_num) B hX
    rw [← hmap, rowS_lift_eq htwo hsq hd hXh, rowSJ]
    exact (MonoidHom.range_comp _ _).symm
  have hLJ : L.map ρ = rowSJ μ Ψ := hcompEq _ hL₁
  refine ⟨⟨μ, hμ, Ψ, 1, card_extension μ, ?_, ?_, rowST_inf_zpowers Ψ htwo,
    conjAut_rowSKappa_mem_normalizer Ψ, orderOf_conjAut_rowSKappa Ψ htwo, ?_, ?_, ?_,
    conjAut_rowSPi_sl_eq_one_iff Ψ, ?_, centralizer_conjAut_eq (by norm_num) (rowSU μ Ψ), ?_,
    ?_⟩, ?_⟩
  · rw [map_one, one_mul, inv_one, mul_one, hρa']
  · rw [hc1, hid, hρa', inner_inf_centralizer_rowSU]
  · intro g _
    constructor
    · intro h1
      obtain ⟨c, hc⟩ := (conjAut_eq_one_iff (by norm_num) _).mp h1
      rw [← rowSPi_scalar μ Ψ c] at hc
      exact ⟨c, (rowSPi_injective μ Ψ hc).symm⟩
    · rintro ⟨c, rfl⟩
      rw [rowSPi_scalar, conjAut_scalar]
  · intro X
    rw [hc1, hid]
    exact ⟨hcompEq X, fun h => h ▸ hLJ ▸ hL₁⟩
  · rw [hc1, hid, hLJ]
  · rw [hc1, hid, hρa']
  · rw [hc1, hid, hCA, hρa']
  · rw [hc1, hid, hCW, hρa']
  ·
    set θ := (conjAut 4 k).comp ((rowSPi μ Ψ).comp SpecialLinearGroup.toGL) with hθ
    have hker : θ.ker = scalars 2 (extension (μ : k)) := by
      ext g
      rw [MonoidHom.mem_ker, mem_scalars_two_iff]
      exact conjAut_rowSPi_sl_eq_one_iff Ψ g
    have : Finite (extension (μ : k)) :=
      CatalogueBProjectiveInvolution.quadraticExtension_finite _
    exact ⟨extension (μ : k), inferInstance, inferInstance, card_extension μ,
      ⟨(L.equivMapOfInjective ρ hinj).trans ((MulEquiv.subgroupCongr hLJ).trans
        ((QuotientGroup.quotientKerEquivRange θ).symm.trans
          (QuotientGroup.quotientMulEquivOfEq hker)))⟩⟩

end CFSG.ComponentClassification.OddSelector
