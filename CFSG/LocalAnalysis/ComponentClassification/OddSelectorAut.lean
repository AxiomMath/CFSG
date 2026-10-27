module

public import CFSG.LocalAnalysis.ComponentInitial.SteinbergBUProjectivePlaneLinearField
public import CFSG.LocalAnalysis.ComponentClassification.OddSelectorGraph
public import CFSG.LocalAnalysis.ComponentClassification.OddSelectorSplitFour

public noncomputable section

namespace CFSG.ComponentClassification.OddSelector

open Subgroup Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial LinearFlag
open CFSG.ComponentClassification.UnbalancedCatalog CFSG.ComponentClassification.OutcomeLocal

variable {k : Type} [Field k] {m : ℕ}

theorem conjAut_mem_inner {X : GL (Fin m) k} {c : kˣ} (hX : GeneralLinearGroup.det X = c ^ m) :
    conjAut m k X ∈ OuterAutomorphisms.inner (projectiveSL m k) := by
  have hdet : (((GeneralLinearGroup.scalar (Fin m) c⁻¹ * X : GL (Fin m) k)) :
      Matrix (Fin m) (Fin m) k).det = 1 := by
    have h1 := congrArg (fun v : kˣ => (v : k)) hX
    simp only [Units.val_pow_eq_pow_val, GeneralLinearGroup.val_det_apply] at h1
    rw [Units.val_mul, det_mul, GeneralLinearGroup.coe_scalar, scalar_apply, det_diagonal,
      Finset.prod_const, Finset.card_univ, Fintype.card_fin, h1, Units.val_inv_eq_inv_val,
      inv_pow, inv_mul_cancel₀ (pow_ne_zero _ c.ne_zero)]
  obtain ⟨g, hg⟩ : ∃ g : SpecialLinearGroup (Fin m) k,
      SpecialLinearGroup.toGL g = GeneralLinearGroup.scalar (Fin m) c⁻¹ * X :=
    ⟨⟨_, hdet⟩, Units.ext rfl⟩
  have hA : X = GeneralLinearGroup.scalar (Fin m) c * SpecialLinearGroup.toGL g := by
    rw [hg, map_inv, mul_inv_cancel_left]
  rw [hA, map_mul, conjAut_scalar, one_mul, conjAut_toGL]
  exact ⟨_, rfl⟩

theorem exists_conjAut_of_mem_inner {α : MulAut (projectiveSL m k)}
    (hα : α ∈ OuterAutomorphisms.inner (projectiveSL m k)) :
    ∃ X : SpecialLinearGroup (Fin m) k, α = conjAut m k (SpecialLinearGroup.toGL X) := by
  obtain ⟨x, rfl⟩ := hα
  obtain ⟨X, rfl⟩ := proj_surjective m k x
  exact ⟨X, (conjAut_toGL X).symm⟩

theorem conjAut_mem_inner_iff [Finite k] (hm : 3 ≤ m) (X : GL (Fin m) k) :
    conjAut m k X ∈ OuterAutomorphisms.inner (projectiveSL m k) ↔
      ∃ c : kˣ, GeneralLinearGroup.det X = c ^ m := by
  refine ⟨fun h => ?_, fun ⟨c, hc⟩ => conjAut_mem_inner hc⟩
  obtain ⟨Y, hY⟩ := exists_conjAut_of_mem_inner h
  obtain ⟨c, hc⟩ := (conjAut_eq_conjAut_iff hm _ _).mp hY
  refine ⟨c, ?_⟩
  rw [hc, map_mul, GeneralLinearGroup.det_scalar, Fintype.card_fin]
  have hY1 : GeneralLinearGroup.det (SpecialLinearGroup.toGL Y) = 1 :=
    Units.ext (by rw [GeneralLinearGroup.val_det_apply, SpecialLinearGroup.coe_GL_coe_matrix,
      Y.2, Units.val_one])
  rw [hY1, one_mul]

variable [Finite k]

theorem eq_of_conjAut_eq_normalForm (hm : 3 ≤ m) {X B : GL (Fin m) k} {τ : k ≃+* k} {ε : ℕ}
    (hε : ε ≤ 1) (h : conjAut m k X = conjAut m k B * fieldAut m k τ * dualAut m k ^ ε) :
    τ = 1 ∧ ε = 0 ∧ conjAut m k X = conjAut m k B := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hε with rfl | rfl
  · rw [pow_zero, mul_one] at h
    have h1 : conjAut m k (X⁻¹ * B) * fieldAut m k τ = 1 := by
      rw [map_mul, map_inv, mul_assoc, ← h, inv_mul_cancel]
    obtain ⟨hτ, -⟩ := eq_one_of_conjAut_mul_fieldAut_eq_one hm _ τ h1
    subst hτ
    rw [map_one, mul_one] at h
    exact ⟨rfl, rfl, h⟩
  · exfalso
    rw [pow_one] at h
    apply ProjectivePlane.dualAut_not_mem_semilinearAutGroup (K := k) hm
    have hδ : dualAut m k = (conjAut m k B * fieldAut m k τ)⁻¹ * conjAut m k X := by
      rw [h, inv_mul_cancel_left]
    rw [hδ]
    refine mul_mem (inv_mem (mem_semilinearAutGroup_iff.mpr ⟨B, τ, rfl⟩)) ?_
    exact mem_semilinearAutGroup_iff.mpr ⟨X, 1, by rw [map_one, mul_one]⟩

omit [Finite k] in
theorem fieldAut_conj_conjAut (τ : k ≃+* k) (A : GL (Fin m) k) :
    fieldAut m k τ * conjAut m k A * (fieldAut m k τ)⁻¹ =
      conjAut m k (GeneralLinearGroup.map (τ : k →+* k) A) :=
  (standard_automorphism_transport (n := m) (K := k)).2.2.1 τ A

omit [Finite k] in
theorem dualAut_conj_conjAut (A : GL (Fin m) k) :
    dualAut m k * conjAut m k A * (dualAut m k)⁻¹ =
      conjAut m k (GeneralLinearGroup.inverseTranspose A) := by
  obtain ⟨-, -, -, hdd, hdc, -⟩ := standard_automorphism_transport (n := m) (K := k)
  rw [← hdc A, inv_eq_of_mul_eq_one_right hdd]

omit [Finite k] in
theorem fieldAut_conj_dualAut (τ : k ≃+* k) :
    fieldAut m k τ * dualAut m k * (fieldAut m k τ)⁻¹ = dualAut m k := by
  rw [← dualAut_mul_fieldAut, mul_inv_cancel_right]

omit [Finite k] in
theorem dualAut_inv : (dualAut m k)⁻¹ = dualAut m k :=
  inv_eq_of_mul_eq_one_right (standard_automorphism_transport (n := m) (K := k)).2.2.2.1

omit [Finite k] in
theorem normalForm_conj_conjAut (B U : GL (Fin m) k) (τ : k ≃+* k) :
    (conjAut m k B * fieldAut m k τ) * conjAut m k U * (conjAut m k B * fieldAut m k τ)⁻¹ =
        conjAut m k (B * GeneralLinearGroup.map (τ : k →+* k) U * B⁻¹) ∧
      (conjAut m k B * fieldAut m k τ * dualAut m k) * conjAut m k U *
          (conjAut m k B * fieldAut m k τ * dualAut m k)⁻¹ =
        conjAut m k (B * GeneralLinearGroup.inverseTranspose
          (GeneralLinearGroup.map (τ : k →+* k) U) * B⁻¹) := by
  constructor
  · calc (conjAut m k B * fieldAut m k τ) * conjAut m k U * (conjAut m k B * fieldAut m k τ)⁻¹
        = conjAut m k B * (fieldAut m k τ * conjAut m k U * (fieldAut m k τ)⁻¹) *
            (conjAut m k B)⁻¹ := by group
      _ = _ := by rw [fieldAut_conj_conjAut, ← map_inv, ← map_mul, ← map_mul]
  · calc (conjAut m k B * fieldAut m k τ * dualAut m k) * conjAut m k U *
          (conjAut m k B * fieldAut m k τ * dualAut m k)⁻¹
        = conjAut m k B * (fieldAut m k τ * (dualAut m k * conjAut m k U * (dualAut m k)⁻¹) *
            (fieldAut m k τ)⁻¹) * (conjAut m k B)⁻¹ := by group
      _ = _ := by
          rw [dualAut_conj_conjAut, fieldAut_conj_conjAut,
            GeneralLinearGroup.map_inverseTranspose, ← map_inv, ← map_mul, ← map_mul]

omit [Finite k] in
theorem mem_centralizer_singleton_iff_conj {G : Type*} [Group G] (α β : G) :
    α ∈ centralizer {β} ↔ α * β * α⁻¹ = β := by
  rw [mem_centralizer_singleton_iff, mul_inv_eq_iff_eq_mul]

theorem conjAut_eq_conjAut_iff' (hm : 3 ≤ m) (A U : GL (Fin m) k) :
    conjAut m k A = conjAut m k U ↔ ∃ c : kˣ, A = GeneralLinearGroup.scalar (Fin m) c * U := by
  rw [conjAut_eq_conjAut_iff hm]
  refine exists_congr fun c => ?_
  rw [GeneralLinearGroup.scalar_commute c U]

theorem mem_centralizer_conjAut_iff (hm : 3 ≤ m) (U : GL (Fin m) k)
    (α : MulAut (projectiveSL m k)) :
    α ∈ centralizer {conjAut m k U} ↔ ∃ (B : GL (Fin m) k) (τ : k ≃+* k),
      (α = conjAut m k B * fieldAut m k τ ∧ ∃ c : kˣ,
        B * GeneralLinearGroup.map (τ : k →+* k) U * B⁻¹ =
          GeneralLinearGroup.scalar (Fin m) c * U) ∨
      (α = conjAut m k B * fieldAut m k τ * dualAut m k ∧ ∃ c : kˣ,
        B * GeneralLinearGroup.inverseTranspose (GeneralLinearGroup.map (τ : k →+* k) U) *
          B⁻¹ = GeneralLinearGroup.scalar (Fin m) c * U) := by
  rw [mem_centralizer_singleton_iff_conj]
  constructor
  · intro h
    obtain ⟨-, hform⟩ := automorphism_generation (K := k) hm
    obtain ⟨B, τ, ε, hε, rfl⟩ := hform α
    obtain ⟨h0, h1⟩ := normalForm_conj_conjAut B U τ
    refine ⟨B, τ, ?_⟩
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hε with rfl | rfl
    · rw [pow_zero, mul_one] at h ⊢
      rw [h0] at h
      exact Or.inl ⟨rfl, (conjAut_eq_conjAut_iff' hm _ _).mp h⟩
    · rw [pow_one] at h ⊢
      rw [h1] at h
      exact Or.inr ⟨rfl, (conjAut_eq_conjAut_iff' hm _ _).mp h⟩
  · rintro ⟨B, τ, ⟨rfl, hc⟩ | ⟨rfl, hc⟩⟩
    · rw [(normalForm_conj_conjAut B U τ).1]
      exact (conjAut_eq_conjAut_iff' hm _ _).mpr hc
    · rw [(normalForm_conj_conjAut B U τ).2]
      exact (conjAut_eq_conjAut_iff' hm _ _).mpr hc

omit [Finite k] in
theorem normalForm_conj_conjAut_dualAut (B S : GL (Fin m) k) (τ : k ≃+* k) :
    (conjAut m k B * fieldAut m k τ) * (conjAut m k S * dualAut m k) *
        (conjAut m k B * fieldAut m k τ)⁻¹ =
      conjAut m k (B * GeneralLinearGroup.map (τ : k →+* k) S *
        (GeneralLinearGroup.inverseTranspose B)⁻¹) * dualAut m k ∧
    (conjAut m k B * fieldAut m k τ * dualAut m k) * (conjAut m k S * dualAut m k) *
        (conjAut m k B * fieldAut m k τ * dualAut m k)⁻¹ =
      conjAut m k (B * GeneralLinearGroup.inverseTranspose
        (GeneralLinearGroup.map (τ : k →+* k) S) * (GeneralLinearGroup.inverseTranspose B)⁻¹) *
        dualAut m k := by
  have hdB : dualAut m k * (conjAut m k B)⁻¹ =
      conjAut m k (GeneralLinearGroup.inverseTranspose B)⁻¹ * dualAut m k := by
    have h1 : dualAut m k * (conjAut m k B)⁻¹ =
        (dualAut m k * conjAut m k B⁻¹ * (dualAut m k)⁻¹) * dualAut m k := by
      rw [map_inv]; group
    rw [h1, dualAut_conj_conjAut, map_inv]
  constructor
  · calc (conjAut m k B * fieldAut m k τ) * (conjAut m k S * dualAut m k) *
          (conjAut m k B * fieldAut m k τ)⁻¹
        = conjAut m k B * (fieldAut m k τ * conjAut m k S * (fieldAut m k τ)⁻¹) *
            (fieldAut m k τ * dualAut m k * (fieldAut m k τ)⁻¹) * (conjAut m k B)⁻¹ := by group
      _ = conjAut m k B * conjAut m k (GeneralLinearGroup.map (τ : k →+* k) S) *
            (dualAut m k * (conjAut m k B)⁻¹) := by
          rw [fieldAut_conj_conjAut, fieldAut_conj_dualAut]; group
      _ = _ := by rw [hdB, ← map_mul, ← mul_assoc, ← map_mul]
  · calc (conjAut m k B * fieldAut m k τ * dualAut m k) * (conjAut m k S * dualAut m k) *
          (conjAut m k B * fieldAut m k τ * dualAut m k)⁻¹
        = conjAut m k B * (fieldAut m k τ * (dualAut m k * conjAut m k S * (dualAut m k)⁻¹) *
            (fieldAut m k τ)⁻¹) * (fieldAut m k τ * dualAut m k * (fieldAut m k τ)⁻¹) *
              (conjAut m k B)⁻¹ := by
          group
      _ = conjAut m k B * conjAut m k (GeneralLinearGroup.map (τ : k →+* k)
            (GeneralLinearGroup.inverseTranspose S)) * (dualAut m k * (conjAut m k B)⁻¹) := by
          rw [dualAut_conj_conjAut, fieldAut_conj_conjAut, fieldAut_conj_dualAut]; group
      _ = _ := by
          rw [hdB, GeneralLinearGroup.map_inverseTranspose, ← map_mul, ← mul_assoc, ← map_mul]

theorem conjAut_mul_dualAut_eq_iff (hm : 3 ≤ m) (A S : GL (Fin m) k) :
    conjAut m k A * dualAut m k = conjAut m k S * dualAut m k ↔
      ∃ c : kˣ, A = GeneralLinearGroup.scalar (Fin m) c * S := by
  rw [mul_left_inj]
  exact conjAut_eq_conjAut_iff' hm A S

omit [Finite k] in
theorem graph_condition_iff (B R T : GL (Fin m) k) (c : kˣ) :
    B * T⁻¹ * (GeneralLinearGroup.inverseTranspose B)⁻¹ =
        GeneralLinearGroup.scalar (Fin m) c * R⁻¹ ↔
      (GeneralLinearGroup.inverseTranspose B)⁻¹ * R * B =
        GeneralLinearGroup.scalar (Fin m) c * T := by
  set Bt := (GeneralLinearGroup.inverseTranspose B)⁻¹
  set s := GeneralLinearGroup.scalar (Fin m) c
  have hsc : s ∈ center (GL (Fin m) k) := by
    rw [GeneralLinearGroup.center_eq_range_scalar]
    exact ⟨c, rfl⟩
  have hs : ∀ X : GL (Fin m) k, X * s = s * X := fun X => mem_center_iff.mp hsc X
  have hsi : ∀ X : GL (Fin m) k, X * s⁻¹ = s⁻¹ * X := fun X =>
    mem_center_iff.mp (inv_mem hsc) X
  constructor
  · intro h
    have h2 : T⁻¹ = B⁻¹ * (s * R⁻¹) * Bt⁻¹ := by rw [← h]; group
    have h3 : T = Bt * R * s⁻¹ * B := by
      calc T = (T⁻¹)⁻¹ := (inv_inv T).symm
        _ = Bt * R * s⁻¹ * B := by rw [h2]; group
    rw [h3]
    calc Bt * R * B = s * (s⁻¹ * (Bt * R * B)) := by group
      _ = s * ((Bt * R * B) * s⁻¹) := by rw [hsi]
      _ = s * (Bt * R * s⁻¹ * B) := by rw [mul_assoc (Bt * R) B, hsi B]; group
  · intro h
    have h1 : T = s⁻¹ * (Bt * R * B) := by rw [h, ← mul_assoc, inv_mul_cancel, one_mul]
    rw [h1]
    calc B * (s⁻¹ * (Bt * R * B))⁻¹ * Bt = B * (B⁻¹ * R⁻¹ * Bt⁻¹ * s) * Bt := by group
      _ = R⁻¹ * (Bt⁻¹ * s * Bt) := by group
      _ = R⁻¹ * (Bt⁻¹ * (Bt * s)) := by rw [mul_assoc Bt⁻¹, ← hs Bt]
      _ = R⁻¹ * s := by group
      _ = s * R⁻¹ := hs R⁻¹

omit [Finite k] in
theorem graph_matrix_iff (B R T : GL (Fin m) k) (c : kˣ) :
    (GeneralLinearGroup.inverseTranspose B)⁻¹ * R * B =
        GeneralLinearGroup.scalar (Fin m) c * T ↔
      (B : Matrix (Fin m) (Fin m) k)ᵀ * R * B = (c : k) • (T : Matrix (Fin m) (Fin m) k) := by
  rw [Units.ext_iff]
  simp only [Units.val_mul, coe_inverseTranspose_inv, GeneralLinearGroup.coe_scalar,
    scalar_eq_smul_one, Matrix.smul_mul, Matrix.one_mul]

omit [Finite k] in
theorem inverseTranspose_inv_map_of_symm (R : GL (Fin m) k)
    (hR : (R : Matrix (Fin m) (Fin m) k)ᵀ = R) (τ : k ≃+* k) :
    GeneralLinearGroup.inverseTranspose (GeneralLinearGroup.map (τ : k →+* k) R)⁻¹ =
      GeneralLinearGroup.map (τ : k →+* k) R := by
  apply Units.ext
  rw [GeneralLinearGroup.coe_inverseTranspose, inv_inv]
  change ((R : Matrix (Fin m) (Fin m) k).map τ)ᵀ = (R : Matrix (Fin m) (Fin m) k).map τ
  rw [← transpose_map, hR]

theorem mem_centralizer_conjAut_inv_dualAut_iff (hm : 3 ≤ m) (R : GL (Fin m) k)
    (hR : (R : Matrix (Fin m) (Fin m) k)ᵀ = R) (B : GL (Fin m) k) (τ : k ≃+* k) :
    (conjAut m k B * fieldAut m k τ ∈ centralizer {conjAut m k R⁻¹ * dualAut m k} ↔
      ∃ c : kˣ, (B : Matrix (Fin m) (Fin m) k)ᵀ * R * B = (c : k) •
        ((GeneralLinearGroup.map (τ : k →+* k) R : GL (Fin m) k) :
          Matrix (Fin m) (Fin m) k)) ∧
    (conjAut m k B * fieldAut m k τ * dualAut m k ∈
        centralizer {conjAut m k R⁻¹ * dualAut m k} ↔
      ∃ c : kˣ, (B : Matrix (Fin m) (Fin m) k)ᵀ * R * B = (c : k) •
        (((GeneralLinearGroup.map (τ : k →+* k) R)⁻¹ : GL (Fin m) k) :
          Matrix (Fin m) (Fin m) k)) := by
  obtain ⟨h0, h1⟩ := normalForm_conj_conjAut_dualAut B R⁻¹ τ
  constructor
  · rw [mem_centralizer_singleton_iff_conj, h0, conjAut_mul_dualAut_eq_iff hm]
    refine exists_congr fun c => ?_
    rw [map_inv, graph_condition_iff, graph_matrix_iff]
  · rw [mem_centralizer_singleton_iff_conj, h1, conjAut_mul_dualAut_eq_iff hm]
    refine exists_congr fun c => ?_
    rw [map_inv, inverseTranspose_inv_map_of_symm R hR, ← inv_inv
      (GeneralLinearGroup.map (τ : k →+* k) R), graph_condition_iff, graph_matrix_iff, inv_inv]

theorem centralizer_conjAut_eq (hm : 3 ≤ m) (U : GL (Fin m) k) :
    (centralizer {conjAut m k U} : Set (MulAut (projectiveSL m k))) =
      {β | ∃ (B : GL (Fin m) k) (τ : k ≃+* k) (ε : ℕ), ε ≤ 1 ∧
        (∃ c : kˣ, B * ((GeneralLinearGroup.inverseTranspose : MulAut (GL (Fin m) k)) ^ ε)
            (GeneralLinearGroup.map (τ : k →+* k) U) * B⁻¹ =
          GeneralLinearGroup.scalar (Fin m) c * U) ∧
        β = conjAut m k B * fieldAut m k τ * dualAut m k ^ ε} := by
  ext β
  rw [SetLike.mem_coe, mem_centralizer_conjAut_iff hm, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨B, τ, ⟨rfl, hc⟩ | ⟨rfl, hc⟩⟩
    · exact ⟨B, τ, 0, zero_le_one, by simpa using hc, by rw [pow_zero, mul_one]⟩
    · exact ⟨B, τ, 1, le_rfl, by simpa using hc, by rw [pow_one]⟩
  · rintro ⟨B, τ, ε, hε, hc, rfl⟩
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hε with rfl | rfl
    · exact ⟨B, τ, Or.inl ⟨by rw [pow_zero, mul_one], by simpa using hc⟩⟩
    · exact ⟨B, τ, Or.inr ⟨by rw [pow_one], by simpa using hc⟩⟩

theorem centralizer_conjAut_inv_dualAut_eq (hm : 3 ≤ m) (R : GL (Fin m) k)
    (hR : (R : Matrix (Fin m) (Fin m) k)ᵀ = R) :
    (centralizer {conjAut m k R⁻¹ * dualAut m k} : Set (MulAut (projectiveSL m k))) =
      {β | ∃ (B : GL (Fin m) k) (τ : k ≃+* k) (ε : ℕ), ε ≤ 1 ∧
        ((ε = 0 ∧ ∃ c : kˣ, (B : Matrix (Fin m) (Fin m) k)ᵀ * R * B = (c : k) •
            ((GeneralLinearGroup.map (τ : k →+* k) R : GL (Fin m) k) :
              Matrix (Fin m) (Fin m) k)) ∨
          (ε = 1 ∧ ∃ c : kˣ, (B : Matrix (Fin m) (Fin m) k)ᵀ * R * B = (c : k) •
            (((GeneralLinearGroup.map (τ : k →+* k) R)⁻¹ : GL (Fin m) k) :
              Matrix (Fin m) (Fin m) k))) ∧
        β = conjAut m k B * fieldAut m k τ * dualAut m k ^ ε} := by
  ext β
  rw [SetLike.mem_coe, Set.mem_ofPred_eq]
  constructor
  · intro hβ
    obtain ⟨-, hform⟩ := automorphism_generation (K := k) hm
    obtain ⟨B, τ, ε, hε, rfl⟩ := hform β
    obtain ⟨h0, h1⟩ := mem_centralizer_conjAut_inv_dualAut_iff hm R hR B τ
    refine ⟨B, τ, ε, hε, ?_, rfl⟩
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hε with rfl | rfl
    · rw [pow_zero, mul_one] at hβ
      exact Or.inl ⟨rfl, h0.mp hβ⟩
    · rw [pow_one] at hβ
      exact Or.inr ⟨rfl, h1.mp hβ⟩
  · rintro ⟨B, τ, ε, -, ⟨rfl, hc⟩ | ⟨rfl, hc⟩, rfl⟩
    · rw [pow_zero, mul_one]
      exact (mem_centralizer_conjAut_inv_dualAut_iff hm R hR B τ).1.mpr hc
    · rw [pow_one]
      exact (mem_centralizer_conjAut_inv_dualAut_iff hm R hR B τ).2.mpr hc

end CFSG.ComponentClassification.OddSelector
