module

public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherOuterQuotients
public import CFSG.LocalAnalysis.ComponentInitial.LinearCoverModel
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4DiagUf
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog516CLift
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitAction

public section

namespace CFSG.ComponentClassification.HarrisLit.Q81

open CFSG Subgroup Matrix CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ComponentClassification.CatFactsL4U4 CFSG.ComponentClassification.CatFactsL4U4.DiagU
  CFSG.ComponentClassification.CatFactsL4U4.UnitaryOut
  CFSG.ComponentClassification.CatFactsL4U4.StabU CFSG.ClassicalGroups.UnitaryFlag
  CFSG.Assembly.LowTwoRank

section Linear

variable {F : Type} [Field F] [Finite F]

omit [Finite F] in
theorem ringEquiv_eq_refl_of_card_three (hF : Nat.card F = 3) (σ : F ≃+* F) :
    σ = RingEquiv.refl F := by
  obtain ⟨φ, -, -, -, hcard, -⟩ :=
    finite_field_automorphism_fixed_field_cardinality (F := F) Nat.prime_three le_rfl
      (by rw [hF, pow_one])
  have : Subsingleton (F ≃+* F) := (Nat.card_eq_one_iff_unique.mp hcard).1
  exact Subsingleton.elim _ _

theorem det_sq_eq_one (hF : Nat.card F = 3) (A : GL (Fin 4) F) :
    (A : Matrix (Fin 4) (Fin 4) F).det ^ 2 = 1 := by
  have := Fintype.ofFinite F
  have hd : (A : Matrix (Fin 4) (Fin 4) F).det ≠ 0 := A.isUnit.map Matrix.detMonoidHom |>.ne_zero
  have h1 := FiniteField.pow_card_sub_one_eq_one _ hd
  rwa [← Nat.card_eq_fintype_card, hF] at h1

theorem conjAut_sq_mem_range_conj (hF : Nat.card F = 3) (A : GL (Fin 4) F) :
    conjAut 4 F A ^ 2 ∈ (MulAut.conj : projectiveSL 4 F →* MulAut (projectiveSL 4 F)).range := by
  have hdet : ((A ^ 2 : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F).det = 1 := by
    rw [Units.val_pow_eq_pow_val, Matrix.det_pow, det_sq_eq_one hF]
  set s : SpecialLinearGroup (Fin 4) F := ⟨((A ^ 2 : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F),
    hdet⟩
  have hs : SpecialLinearGroup.toGL s = A ^ 2 := Units.ext rfl
  refine ⟨proj 4 F s, ?_⟩
  rw [← conjAut_toGL, hs, map_pow]

theorem exists_eq_conjAut (hF : Nat.card F = 3) (α : MulAut (projectiveSL 4 F)) :
    ∃ A : GL (Fin 4) F, α = conjAut 4 F A ∨ α = conjAut 4 F A * dualAut 4 F := by
  obtain ⟨-, hgen⟩ := automorphism_generation (K := F) (n := 4) (by norm_num)
  obtain ⟨A, σ, ε, hε, rfl⟩ := hgen α
  have hσ : fieldAut 4 F σ = 1 := by
    rw [ringEquiv_eq_refl_of_card_three hF σ]
    exact map_one _
  refine ⟨A, ?_⟩
  interval_cases ε
  · left
    rw [hσ, pow_zero, mul_one, mul_one]
  · right
    rw [hσ, pow_one, mul_one]

omit [Finite F] in
theorem dualAut_mul_conjAut_mul_dualAut (B : GL (Fin 4) F) :
    dualAut 4 F * conjAut 4 F B * dualAut 4 F =
      conjAut 4 F (GeneralLinearGroup.inverseTranspose B) :=
  (standard_automorphism_transport (K := F) (n := 4)).2.2.2.2.1 B

theorem mul_mem_range_conjAut (hF : Nat.card F = 3) {α β : MulAut (projectiveSL 4 F)}
    (hα : α ∉ (conjAut 4 F).range) (hβ : β ∉ (conjAut 4 F).range) :
    α * β ∈ (conjAut 4 F).range := by
  obtain ⟨A, rfl | rfl⟩ := exists_eq_conjAut hF α
  · exact absurd ⟨A, rfl⟩ hα
  obtain ⟨B, rfl | rfl⟩ := exists_eq_conjAut hF β
  · exact absurd ⟨B, rfl⟩ hβ
  refine ⟨A * GeneralLinearGroup.inverseTranspose B, ?_⟩
  rw [map_mul, ← dualAut_mul_conjAut_mul_dualAut]
  group

theorem pow_four_mem_range_conj_L (hF : Nat.card F = 3) (α : MulAut (projectiveSL 4 F)) :
    α ^ 4 ∈ (MulAut.conj : projectiveSL 4 F →* MulAut (projectiveSL 4 F)).range := by
  have hsq : α ^ 2 ∈ (conjAut 4 F).range := by
    by_cases hα : α ∈ (conjAut 4 F).range
    · exact pow_mem hα 2
    · rw [pow_two]
      exact mul_mem_range_conjAut hF hα hα
  obtain ⟨B, hB⟩ := hsq
  have h4 : α ^ 4 = (α ^ 2) ^ 2 := by rw [← pow_mul]
  rw [h4, ← hB]
  exact conjAut_sq_mem_range_conj hF B

end Linear

section Unitary

variable {K : Type} [Field K] (h : UnitaryFieldData 3 1 K)

include h in
theorem card_ringEquiv : Nat.card (K ≃+* K) = 2 := by
  obtain ⟨-, -, -, -, hcard, -⟩ :=
    finite_field_automorphism_fixed_field_cardinality (F := K) Nat.prime_three (by norm_num)
      h.card
  exact hcard

include h in
theorem ringEquiv_mul_self (σ : K ≃+* K) : σ * σ = 1 := by
  have : Finite (K ≃+* K) := Nat.finite_of_card_ne_zero (by rw [card_ringEquiv h]; norm_num)
  rw [← pow_two, ← card_ringEquiv h]
  exact pow_card_eq_one'

theorem eq_bar_of_ne_refl {σ : K ≃+* K} (hσ : σ ≠ RingEquiv.refl K) : ∀ c, σ c = h.bar c :=
  (ringEquiv_eq_refl_or_bar h (ringEquiv_mul_self h σ)).resolve_left hσ

include h in
theorem mul_eq_one_of_ne_refl {σ τ : K ≃+* K} (hσ : σ ≠ RingEquiv.refl K)
    (hτ : τ ≠ RingEquiv.refl K) : σ * τ = 1 := by
  have hστ : σ = τ := RingEquiv.ext fun c => by
    rw [eq_bar_of_ne_refl h hσ, eq_bar_of_ne_refl h hτ]
  rw [hστ]
  exact ringEquiv_mul_self h τ

include h in
theorem exists_lift (α : MulAut (StatedProj (StatedSU 4 (3 ^ 1) K))) :
    ∃ (A : GL (Fin 4) K) (φ : K ≃+* K)
      (hA : ∀ g : unitarySU 3 1 K 4, A * glAut φ (g : GL (Fin 4) K) * A⁻¹ ∈ unitarySU 3 1 K 4),
      A ∈ uMat h 4 ∧ ∀ g : unitarySU 3 1 K 4,
        thU 3 1 K (ClassicalInvolution.ModelFacts.UnitaryAut.unitaryConjHom A φ hA g) =
          α (thU 3 1 K g) := by
  have : Finite K := h.finite
  have hker : (thU 3 1 K).ker ≤ Subgroup.center (unitarySU 3 1 K 4) := by
    rw [QuotientGroup.ker_mk']
    intro z hz
    exact mem_center_of_mem_scal hz
  obtain ⟨A, φ, hA, hAu, hu, -⟩ := CFSG.GH74.Generic.S45.exists_lift_unitarySU' h (by norm_num)
    (d := 4) (by norm_num) (thU 3 1 K) thU_surjective hker α
  exact ⟨A, φ, hA, (mem_uMat h).2 hAu, hu⟩

theorem isCU_of_lift_refl {α : MulAut (StatedProj (StatedSU 4 (3 ^ 1) K))} {A : GL (Fin 4) K}
    (hA : ∀ g : unitarySU 3 1 K 4,
      A * glAut (RingEquiv.refl K) (g : GL (Fin 4) K) * A⁻¹ ∈ unitarySU 3 1 K 4)
    (hAU : A ∈ uMat h 4)
    (hu : ∀ g : unitarySU 3 1 K 4,
      thU 3 1 K (ClassicalInvolution.ModelFacts.UnitaryAut.unitaryConjHom A
        (RingEquiv.refl K) hA g) = α (thU 3 1 K g)) :
    IsCU h A α := by
  refine ⟨hAU, fun g g' hg => ?_⟩
  rw [← hu]
  congr 1
  apply Subtype.ext
  rw [ClassicalInvolution.ModelFacts.UnitaryAut.coe_unitaryConjHom, glAut_refl, hg]

theorem mul_mem_InnU {α β : MulAut (StatedProj (StatedSU 4 (3 ^ 1) K))}
    (hα : α ∉ InnU 3 1 K h) (hβ : β ∉ InnU 3 1 K h) : α * β ∈ InnU 3 1 K h := by
  have : Finite K := h.finite
  obtain ⟨A, φ, hA, hAU, hu⟩ := exists_lift h α
  obtain ⟨B, ψ, hB, hBU, hv⟩ := exists_lift h β
  have hφ : φ ≠ RingEquiv.refl K := by
    rintro rfl
    exact hα ⟨A, isCU_of_lift_refl h hA hAU hu⟩
  have hψ : ψ ≠ RingEquiv.refl K := by
    rintro rfl
    exact hβ ⟨B, isCU_of_lift_refl h hB hBU hv⟩
  have hφψ : ∀ g : GL (Fin 4) K, glAut φ (glAut ψ g) = g := by
    intro g
    have h1 : (glAut φ * glAut ψ : MulAut (GL (Fin 4) K)) = 1 := by
      rw [← map_mul, mul_eq_one_of_ne_refl h hφ hψ, map_one]
    exact congrArg (fun χ : MulAut (GL (Fin 4) K) => χ g) h1
  refine ⟨A * glAut φ B, mul_mem hAU (glAut_mem_uMat h φ hBU), fun g g' hg => ?_⟩
  rw [MulAut.mul_apply, ← hv, ← hu]
  congr 1
  apply Subtype.ext
  rw [ClassicalInvolution.ModelFacts.UnitaryAut.coe_unitaryConjHom,
    ClassicalInvolution.ModelFacts.UnitaryAut.coe_unitaryConjHom, map_mul, map_mul, map_inv,
    hφψ, hg]
  group

theorem det_pow_four_eq_one {A : GL (Fin 4) K} (hA : A ∈ uMat h 4) :
    (A : Matrix (Fin 4) (Fin 4) K).det ^ 4 = 1 := by
  have h1 := congrArg Matrix.det ((mem_uMat h).1 hA)
  rw [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] at h1
  have h2 : ((A : Matrix (Fin 4) (Fin 4) K).map h.bar).det =
      h.bar (A : Matrix (Fin 4) (Fin 4) K).det :=
    (RingHom.map_det h.bar _).symm
  rw [h2, UnitaryFieldData.bar_apply] at h1
  calc (A : Matrix (Fin 4) (Fin 4) K).det ^ 4
      = (A : Matrix (Fin 4) (Fin 4) K).det ^ 3 ^ 1 * (A : Matrix (Fin 4) (Fin 4) K).det := by
        ring
    _ = 1 := h1

theorem isCU_pow {A : GL (Fin 4) K} {α : MulAut (StatedProj (StatedSU 4 (3 ^ 1) K))}
    (hα : IsCU h A α) (n : ℕ) : IsCU h (A ^ n) (α ^ n) := by
  induction n with
  | zero =>
    rw [pow_zero, pow_zero]
    exact isCU_one h
  | succ n ih =>
    rw [pow_succ, pow_succ]
    exact ih.mul h hα

theorem pow_four_mem_range_conj_of_mem_InnU {α : MulAut (StatedProj (StatedSU 4 (3 ^ 1) K))}
    (hα : α ∈ InnU 3 1 K h) :
    α ^ 4 ∈ (MulAut.conj : StatedProj (StatedSU 4 (3 ^ 1) K) →*
      MulAut (StatedProj (StatedSU 4 (3 ^ 1) K))).range := by
  obtain ⟨A, hA⟩ := hα
  have h4 := isCU_pow h hA 4
  have hmem : A ^ 4 ∈ unitarySU 3 1 K 4 := by
    rw [mem_unitarySU_iff h]
    refine ⟨?_, (mem_uMat h).1 (pow_mem hA.1 4)⟩
    rw [Units.val_pow_eq_pow_val, Matrix.det_pow]
    exact det_pow_four_eq_one h hA.1
  exact ⟨_, (h4.eq_conj h hmem).symm⟩

include h in
theorem pow_eight_mem_range_conj_U (α : MulAut (StatedProj (StatedSU 4 (3 ^ 1) K))) :
    α ^ 8 ∈ (MulAut.conj : StatedProj (StatedSU 4 (3 ^ 1) K) →*
      MulAut (StatedProj (StatedSU 4 (3 ^ 1) K))).range := by
  have hsq : α ^ 2 ∈ InnU 3 1 K h := by
    by_cases hα : α ∈ InnU 3 1 K h
    · exact pow_mem hα 2
    · rw [pow_two]
      exact mul_mem_InnU h hα hα
  rw [show (8 : ℕ) = 2 * 4 from rfl, pow_mul]
  exact pow_four_mem_range_conj_of_mem_InnU h hsq

end Unitary

section Abstract

theorem pow_mem_range_conj_of_mulEquiv {P P' : Type*} [Group P] [Group P'] (e : P ≃* P') (n : ℕ)
    (h : ∀ β : MulAut P', β ^ n ∈ (MulAut.conj : P' →* MulAut P').range) (α : MulAut P) :
    α ^ n ∈ (MulAut.conj : P →* MulAut P).range := by
  obtain ⟨y, hy⟩ := h (MulAut.congr e α)
  refine ⟨e.symm y, ?_⟩
  have h1 : MulAut.congr e (MulAut.conj (e.symm y)) = MulAut.conj y := by
    ext x
    simp [MulAut.congr_apply]
  apply (MulAut.congr e).injective
  rw [h1, hy, map_pow]

theorem pow_eight_mem_range_conj_of_lieModel {P : Type} [Group P]
    (hP : Blueprint.LieModel P .PSL 4 3 1 ∨ Blueprint.LieModel P .PSU 4 3 1) (α : MulAut P) :
    α ^ 8 ∈ (MulAut.conj : P →* MulAut P).range := by
  rcases hP with hL | hU
  · obtain ⟨F, _, _, hF, ⟨e⟩⟩ := LinearCover.exists_mulEquiv_projectiveSL_of_lieModel hL
    rw [pow_one] at hF
    refine pow_mem_range_conj_of_mulEquiv e 8 (fun β => ?_) α
    rw [show (8 : ℕ) = 4 * 2 from rfl, pow_mul]
    obtain ⟨y, hy⟩ := pow_four_mem_range_conj_L hF β
    rw [← hy, ← map_pow]
    exact ⟨_, rfl⟩
  · obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ :=
      LieType.Steinberg.statedClassicalModel_of_lieModel (by decide) hU
    have h : UnitaryFieldData 3 1 K := ⟨Nat.prime_three, le_rfl, by rw [hK]; norm_num⟩
    exact pow_mem_range_conj_of_mulEquiv e 8 (pow_eight_mem_range_conj_U h) α

theorem eq_one_of_barAut_eq_one {Y : Type*} [Group Y] (hY : Group.IsPerfect Y) {γ : MulAut Y}
    (hγ : GSThmB.Cent516.barAut γ = 1) : γ = 1 := by
  have htop : ⁅(⊤ : Subgroup Y), (⊤ : Subgroup Y)⁆ = (⊤ : Subgroup Y) := by
    rw [← _root_.commutator_def]
    exact hY.commutator_eq_top
  have hfix := GSThmB.Cent516.fix_of_perfect γ ⊤ htop fun y _ => by
    have h1 := congrArg (fun χ : MulAut (Y ⧸ center Y) => χ (QuotientGroup.mk y)) hγ
    simp only [GSThmB.Cent516.barAut_mk, MulAut.one_apply] at h1
    have h2 := QuotientGroup.eq.mp h1
    have h3 := inv_mem h2
    rwa [_root_.mul_inv_rev, inv_inv] at h3
  ext y
  exact hfix y (Subgroup.mem_top y)

theorem pow_eight_mem_range_conj_of_perfect {Y : Type} [Group Y] (hY : Group.IsPerfect Y)
    (hP : Blueprint.LieModel (Y ⧸ center Y) .PSL 4 3 1 ∨
      Blueprint.LieModel (Y ⧸ center Y) .PSU 4 3 1) (α : MulAut Y) :
    α ^ 8 ∈ (MulAut.conj : Y →* MulAut Y).range := by
  obtain ⟨y, hy⟩ := pow_eight_mem_range_conj_of_lieModel hP (GSThmB.Cent516.barAut α)
  obtain ⟨q, rfl⟩ := QuotientGroup.mk_surjective y
  have h1 : GSThmB.Cent516.barAut (α ^ 8 * (MulAut.conj q)⁻¹) = 1 := by
    rw [GSThmB.Cent516.barAut_mul]
    have hpow : GSThmB.Cent516.barAut (α ^ 8) = GSThmB.Cent516.barAut α ^ 8 := by
      induction 8 with
      | zero => rw [pow_zero, pow_zero, GSThmB.Cent516.barAut_one]
      | succ n ih => rw [pow_succ, pow_succ, GSThmB.Cent516.barAut_mul, ih]
    have hinv : GSThmB.Cent516.barAut (MulAut.conj q)⁻¹ =
        (GSThmB.Cent516.barAut (MulAut.conj q))⁻¹ := by
      rw [eq_inv_iff_mul_eq_one, ← GSThmB.Cent516.barAut_mul, inv_mul_cancel,
        GSThmB.Cent516.barAut_one]
    rw [hpow, hinv, ← hy, GSThmB.Cent516.barAut_conj, mul_inv_cancel]
  have h2 := eq_one_of_barAut_eq_one hY h1
  exact ⟨q, (mul_inv_eq_one.mp h2).symm⟩

theorem exists_pow_eight_mem_centralizer {G : Type} [Group G] {Q : Subgroup G}
    (hQ : Group.IsPerfect ↥Q)
    (hP : Blueprint.LieModel (↥Q ⧸ center ↥Q) .PSL 4 3 1 ∨
      Blueprint.LieModel (↥Q ⧸ center ↥Q) .PSU 4 3 1)
    {g : G} (hg : g ∈ normalizer (Q : Set G)) :
    ∃ q ∈ Q, q⁻¹ * g ^ 8 ∈ centralizer (Q : Set G) := by
  obtain ⟨q, hq⟩ := pow_eight_mem_range_conj_of_perfect hQ hP
    (normalizerConj Q ⟨g, hg⟩)
  refine ⟨(q : G), q.2, mem_centralizer_iff.mpr fun y hy => ?_⟩
  have h1 := congrArg (fun χ : MulAut ↥Q => ((χ ⟨y, hy⟩ : ↥Q) : G)) hq
  simp only [← map_pow, MulAut.conj_apply] at h1
  have h2 : ((normalizerConj Q (⟨g, hg⟩ ^ 8) ⟨y, hy⟩ : ↥Q) : G) = g ^ 8 * y * (g ^ 8)⁻¹ := by
    rw [show (⟨g, hg⟩ : ↥(normalizer (Q : Set G))) ^ 8 = ⟨g ^ 8, pow_mem hg 8⟩ from rfl]
    rfl
  rw [h2] at h1
  push_cast at h1
  set q' : G := (q : G) with hq'
  calc y * (q'⁻¹ * g ^ 8) = q'⁻¹ * (q' * y * q'⁻¹) * g ^ 8 := by group
    _ = q'⁻¹ * (g ^ 8 * y * (g ^ 8)⁻¹) * g ^ 8 := by rw [h1]
    _ = q'⁻¹ * g ^ 8 * y := by group

end Abstract

end CFSG.ComponentClassification.HarrisLit.Q81
